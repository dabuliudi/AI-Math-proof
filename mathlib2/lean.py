import hashlib
import os
import re
import shutil
import subprocess
import time
import uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
TACTICS = {'omega': 'omega', 'simp': 'simp',
           'at_zero': 'intro h\n  have h0 := h 0\n  omega'}


def valid_statement(statement):
    # 严格限定一变量自然数算术，拒绝注释、声明、元编程及任意代码注入。
    return bool(re.fullmatch(r'∀ n : Nat, [n0-9+*() =<>≤≥-]{1,200}', statement)) and '\n' not in statement


def accepted(output, name, code):
    if code != 0 or re.search(r'\bsorry\b|sorryAx', output):
        return False, []
    empty = re.search(r"'" + re.escape(name) + r"' does not depend on any axioms", output)
    match = re.search(r"'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", output)
    if empty:
        return True, []
    if not match:
        return False, []
    axioms = [a.strip() for a in match[1].split(',') if a.strip()]
    return set(axioms) <= ALLOWED_AXIOMS, axioms


class LeanWorker:
    def __init__(self, project=None, timeout=30):
        self.project = Path(project or ROOT / 'lean').resolve()
        self.timeout = timeout
        self.lake = os.environ.get('MATHLIB2_LAKE') or shutil.which('lake')

    def check(self, statement, strategy, negate=False, dependency=None):
        start = time.monotonic()
        result = {'accepted': False, 'returncode': None, 'stdout': '', 'stderr': '',
                  'axioms': [], 'reason': '', 'elapsed': 0, 'source': '', 'sha256': '',
                  'toolchain': (self.project / 'lean-toolchain').read_text().strip()}
        if not valid_statement(statement) or strategy not in {*TACTICS, 'reuse'}:
            result['reason'] = '命题或策略超出受限演示语法'
            return result
        name = 'check_' + uuid.uuid4().hex
        prefix = ''
        if strategy == 'reuse':
            if not dependency or not valid_statement(dependency['statement']) or dependency['strategy'] not in TACTICS:
                result['reason'] = '缺少可重新验证的依赖'
                return result
            prefix = f"theorem prior : {dependency['statement']} := by\n  {TACTICS[dependency['strategy']]}\n"
            tactic = 'intro n\n  simp only [prior]'
        else:
            tactic = TACTICS[strategy]
        target = f'¬ ({statement})' if negate else statement
        source = f'import Mathlib.Data.Nat.Init\nimport Lean.Elab.Tactic.Omega\nset_option maxHeartbeats 200000\n{prefix}theorem {name} : {target} := by\n  {tactic}\n#print axioms {name}\n'
        result.update(source=source, sha256=hashlib.sha256(source.encode()).hexdigest(), name=name, target=target)
        manifest = self.project / 'lake-manifest.json'
        if manifest.exists():
            result['manifest_sha256'] = hashlib.sha256(manifest.read_bytes()).hexdigest()
        if not self.lake:
            result['reason'] = 'Lean/Lake 未安装；结果未知'
            return result
        folder = self.project / 'Checks'
        folder.mkdir(exist_ok=True)
        path = folder / (name + '.lean')
        path.write_text(source, encoding='utf-8')
        command = [self.lake, 'env', 'lean', '-M', '1024', str(path)]
        result['command'] = command
        result['artifact'] = str(path)
        try:
            proc = subprocess.Popen(command, cwd=self.project, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    text=True, encoding='utf-8', errors='replace',
                                    start_new_session=os.name != 'nt')
            try:
                stdout, stderr = proc.communicate(timeout=self.timeout)
            except subprocess.TimeoutExpired:
                if os.name == 'nt':
                    subprocess.run(['taskkill', '/PID', str(proc.pid), '/T', '/F'], capture_output=True)
                else:
                    import signal
                    os.killpg(proc.pid, signal.SIGKILL)
                proc.kill()
                stdout, stderr = proc.communicate()
                result.update(stdout=stdout, stderr=stderr)
                raise
            ok, axioms = accepted(stdout + stderr, name, proc.returncode)
            result.update(accepted=ok, returncode=proc.returncode, stdout=stdout,
                          stderr=stderr, axioms=axioms, reason='验证通过' if ok else '编译失败或公理审计不通过')
        except subprocess.TimeoutExpired:
            result['reason'] = '编译超时；结果未知'
        except OSError as exc:
            result['reason'] = str(exc)
        result['elapsed'] = time.monotonic() - start
        return result
