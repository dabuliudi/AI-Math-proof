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
# agent 的草稿和拆解状态放在仓库外面：agent 在仓库里搜索时不会顺手翻到以前各轮的证明（抄写见 provenance.py）。
# 不能放在 /tmp：拆解要能接着上次的状态跑，重启后还得在。
SCRATCH = Path(os.environ.get('FORGE_SCRATCH') or Path.home() / '.rsi-math' / 'scratch')
# 每次 Lean 检查的临时文件：里面是完整的证明，所以放在仓库外面。检查完就删；进程被杀留下的由 _sweep_checks 清掉。
# 它们不算抄写来源（provenance.py）：文件名里没有轮次，接着跑的组合拆解会把自己上一次的引理当成抄来的。
CHECKS = SCRATCH / 'checks'
CHECK_MAX_AGE = 24 * 3600   # 认不出进程号（Windows、旧文件名）时，超过一天的算遗留；单次检查最长 900 秒
_swept = [0.0]
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


def _alive(pid):
    if os.name == 'nt':   # Windows 上 os.kill 会结束进程，不能拿来探测
        return None
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except OSError:   # 例如没有权限：进程在
        return True
    return True


def _sweep_checks(now=None):
    """删掉进程已经不在的检查临时文件（check_<进程号>_<uuid>.lean）；认不出进程号的按年龄删。每分钟最多一次。"""
    now = time.time() if now is None else now
    if now - _swept[0] < 60:
        return
    _swept[0] = now
    for path in CHECKS.glob('check_*.lean'):
        parts = path.stem.split('_')
        pid = int(parts[1]) if len(parts) == 3 and parts[1].isdigit() else None
        alive = _alive(pid) if pid is not None else None
        try:
            if alive is False or (alive is None and now - path.stat().st_mtime > CHECK_MAX_AGE):
                path.unlink(missing_ok=True)
        except OSError:
            pass


def run_source(source, timeout=180, nonce=None, keep=False):
    """把 source 写成临时文件，在固定的 Lean 工程环境里编译。"""
    CHECKS.mkdir(parents=True, exist_ok=True)
    _sweep_checks()
    path = CHECKS / f'check_{os.getpid()}_{uuid.uuid4().hex}.lean'
    path.write_text(source, encoding='utf-8')
    try:
        return _run_file(path, timeout, nonce)
    finally:
        if not keep:
            path.unlink(missing_ok=True)


def _run_file(path, timeout, nonce):
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
