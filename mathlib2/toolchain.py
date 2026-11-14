"""跨平台定位 Lake：环境变量 > PATH > elan 默认目录 > 仓库内便携版（Windows）。"""
import os
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def find_lake():
    explicit = os.environ.get('MATHLIB2_LAKE')
    if explicit:
        return explicit
    found = shutil.which('lake')
    if found:
        return found
    exe = 'lake.exe' if os.name == 'nt' else 'lake'
    for candidate in (Path.home() / '.elan' / 'bin' / exe,
                      ROOT / '.tools/lean-4.24.0-windows/bin/lake.exe'):
        if candidate.exists():
            return str(candidate)
    return None


def kill_tree(proc):
    """超时后结束编译进程及其子进程。"""
    if os.name == 'nt':
        import subprocess
        subprocess.run(['taskkill', '/PID', str(proc.pid), '/T', '/F'], capture_output=True)
    else:
        import signal
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
    proc.kill()
