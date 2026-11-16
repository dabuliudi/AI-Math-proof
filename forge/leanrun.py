"""运行 Lean 并取回结构化消息（--json），不靠解析人类可读文本。"""
import json
import os
import shutil
import signal
import subprocess
import time
import uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / 'lean'
DATA = ROOT / 'forge' / 'data'
STAGING = DATA / 'staging'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def find_lake():
    explicit = os.environ.get('MATHLIB2_LAKE')
    if explicit:
        return explicit
    found = shutil.which('lake')
    if found:
        return found
    candidate = Path.home() / '.elan' / 'bin' / ('lake.exe' if os.name == 'nt' else 'lake')
    if candidate.exists():
        return str(candidate)
    raise RuntimeError('未找到 Lake；请安装 elan 或设置 MATHLIB2_LAKE')


def _env():
    env = os.environ.copy()
    env['PATH'] = str(Path(find_lake()).parent) + os.pathsep + env.get('PATH', '')
    return env


class Result:
    """一次 Lean 运行：messages 是 [{severity,line,column,data}]，tagged 是 Forge 命令的输出。"""

    def __init__(self, returncode, messages, raw, elapsed, timed_out, nonce):
        self.returncode = returncode
        self.messages = messages
        self.raw = raw
        self.elapsed = elapsed
        self.timed_out = timed_out
        self.nonce = nonce

    def errors(self):
        return [m for m in self.messages if m['severity'] == 'error']

    def tagged(self, tag):
        """带本次 nonce 的 `TAG {json}` 输出；nonce 不符的一律丢弃（防伪造）。"""
        out = []
        for m in self.messages:
            data = m['data']
            if m['severity'] == 'information' and data.startswith(tag + ' '):
                try:
                    payload = json.loads(data[len(tag) + 1:])
                except ValueError:
                    continue
                if payload.get('nonce') == self.nonce:
                    out.append(payload)
        return out


def run_source(source, timeout=180, nonce=None, keep=False):
    """把 source 写成临时文件，在固定的 Lean 工程环境里编译。"""
    STAGING.mkdir(parents=True, exist_ok=True)
    path = STAGING / f'check_{uuid.uuid4().hex}.lean'
    path.write_text(source, encoding='utf-8')
    command = [find_lake(), 'env', 'lean', '--json', str(path)]
    start = time.perf_counter()
    timed_out = False
    proc = subprocess.Popen(command, cwd=PROJECT, env=_env(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            text=True, encoding='utf-8', errors='replace', start_new_session=os.name != 'nt')
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        if os.name == 'nt':
            subprocess.run(['taskkill', '/PID', str(proc.pid), '/T', '/F'], capture_output=True)
        else:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
        proc.kill()
        stdout, stderr = proc.communicate()
    messages = []
    for line in stdout.splitlines():
        if not line.startswith('{'):
            continue
        try:
            item = json.loads(line)
        except ValueError:
            continue
        pos = item.get('pos') or {}
        messages.append(dict(severity=item.get('severity', ''), line=pos.get('line', 0),
                             column=pos.get('column', 0), data=item.get('data', '')))
    if not keep:
        path.unlink(missing_ok=True)
    return Result(None if timed_out else proc.returncode, messages, stdout + stderr,
                  time.perf_counter() - start, timed_out, nonce)


def replay(timeout=3600):
    """独立内核重放（lean/scripts/ForgeReplay.lean）：只信内核，不信构建产物。约 1–2 分钟，内存峰值约 14 GB。"""
    proc = subprocess.run([find_lake(), 'env', 'lean', '--run', 'scripts/ForgeReplay.lean'], cwd=PROJECT, env=_env(),
                          capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=timeout)
    for line in proc.stdout.splitlines():
        if line.startswith('FORGE_REPLAY '):
            return json.loads(line[len('FORGE_REPLAY '):])
    return dict(ok=False, kernel_error='重放没有给出结果', output_tail=(proc.stdout + proc.stderr)[-1500:])


def _kill_tree(proc):
    if os.name == 'nt':
        subprocess.run(['taskkill', '/PID', str(proc.pid), '/T', '/F'], capture_output=True)
    else:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
    proc.kill()


def lake_build(target='Mathlib2', timeout=1800, on_start=None):
    """在自己的进程组里构建；超时或出错时结束整组（只结束 lake 的话，它起的 lean 会留下来跟下一次构建抢资源）。
    on_start(pid) 在构建开始时被调用，pid 也是进程组号，供调用方记下、在自己被杀后由别人收拾。"""
    proc = subprocess.Popen([find_lake(), 'build', target], cwd=PROJECT, env=_env(), stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, encoding='utf-8', errors='replace',
                            start_new_session=os.name != 'nt')
    try:
        if on_start:
            on_start(proc.pid)
        stdout, stderr = proc.communicate(timeout=timeout)
    except BaseException:
        _kill_tree(proc)
        proc.communicate()
        raise
    return proc.returncode, stdout + stderr
