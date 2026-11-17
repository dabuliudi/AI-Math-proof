"""抄写检测：评测题解出后，看这份证明是不是从更早的轮次留下的证明里抄来的。

事故（2026-11-17）：agent 在仓库里能读到以前各轮留下的草稿和证明（forge/data/staging），改进循环的几轮里
有 2–5 道题的“解出”和更早的证明重合 30%–70%，例如 erdos 1062 抄了组合拆解 pf-k6-1 的拼装结果。
这样的解出量的是“能不能找到旧答案”，不是 harness 的水平，不能拿来比较配置。

草稿已经移出仓库（leanrun.SCRATCH），但 agent 仍然读得到整个磁盘，所以这里是最后一道关：
把解出的证明逐行和本轮开始之前就存在的所有草稿、拆解状态比，取重合最多的一份。
只比较草稿和拆解状态，不比较 Mathlib2 库本身——引用库里的定理是知识复利，正是想要的。
"""
import json
import subprocess
import threading
from pathlib import Path

from .leanrun import DATA, ROOT, SCRATCH

# 旧位置（移出仓库之前）：里面的文件还在，照样算作可能被抄的来源
LEGACY = (DATA / 'staging' / 'agents', DATA / 'staging' / 'portfolio')
# 旧版本把 Lean 检查的临时文件 check_*.lean（完整的证明）写在 staging 根上，进程被杀时会留下
CHECK_DIRS = (DATA / 'staging',)
# 同一仓库的其他检出（git worktree）在各自的 forge/data/staging 下也有这些旧位置，agent 读得到，所以都要比
STAGING_REL = Path('forge') / 'data' / 'staging'
THRESHOLD = 0.3     # 证明里超过三成的行在某一份旧文件里原样出现，就算抄写
MIN_SHARED = 5      # 至少 5 行相同：很短的证明里一两行定理头相同不算
MIN_LINE = 20       # 短于 20 个字符的行（simp、omega、· 等）到处都有，不参与比较

_cache = {}
_cache_lock = threading.Lock()


def lines(text):
    """参与比较的行：去掉首尾空白、把连续空白压成一个，丢掉注释和太短的行。"""
    out = set()
    for raw in text.splitlines():
        line = ' '.join(raw.split())
        if len(line) >= MIN_LINE and not line.startswith('--'):
            out.add(line)
    return out


def _strings(value):
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for v in value.values():
            yield from _strings(v)
    elif isinstance(value, list):
        for v in value:
            yield from _strings(v)


def _file_lines(path, mtime):
    key = str(path)
    with _cache_lock:
        hit = _cache.get(key)
        if hit and hit[0] == mtime:
            return hit[1]
    try:
        text = path.read_text(encoding='utf-8', errors='replace')
        if path.suffix == '.json':  # 拆解状态：证明以字符串存在 JSON 里
            text = '\n'.join(_strings(json.loads(text)))
    except (OSError, ValueError):
        return set()
    found = lines(text)
    with _cache_lock:
        _cache[key] = (mtime, found)
    return found


def checkouts():
    """这个仓库的所有检出（主检出和各个 worktree）的根目录；git 不可用时只有当前检出。"""
    found = [ROOT]
    try:
        out = subprocess.run(['git', 'worktree', 'list', '--porcelain'], cwd=ROOT, capture_output=True,
                             text=True, encoding='utf-8', errors='replace', timeout=30).stdout
    except (OSError, subprocess.SubprocessError):
        return found
    seen = {ROOT.resolve()}
    for line in out.splitlines():
        path = Path(line[len('worktree '):]) if line.startswith('worktree ') else None
        if path and path.resolve() not in seen:
            seen.add(path.resolve())
            found.append(path)
    return found


def _default_files():
    """不给 roots 时比的文件：SCRATCH 和 LEGACY 整个目录、CHECK_DIRS 里的 check_*.lean，
    以及同一仓库其他检出里对应的旧位置。"""
    dirs, check_dirs = [SCRATCH, *LEGACY], list(CHECK_DIRS)
    for checkout in checkouts()[1:]:
        staging = checkout / STAGING_REL
        dirs += [staging / 'agents', staging / 'portfolio']
        check_dirs.append(staging)
    for d in dirs:
        yield from _walk(d)
    for d in check_dirs:
        if Path(d).is_dir():
            yield from Path(d).glob('check_*.lean')


def _walk(root):
    root = Path(root)
    if root.is_dir():
        yield from root.rglob('*')


def sources(before, roots=None, exclude=()):
    """在 before（时间戳）之前就存在的草稿和拆解状态文件；exclude 里的目录和文件不算。"""
    exclude = [Path(e) for e in exclude]
    files = (p for r in roots for p in _walk(r)) if roots else _default_files()
    for path in files:
        if path.suffix not in ('.lean', '.json') or not path.is_file():
            continue
        if any(path == e or e in path.parents for e in exclude):
            continue
        try:
            mtime = path.stat().st_mtime
        except OSError:
            continue
        if mtime < before:
            yield path, mtime


def check(text, before, roots=None, exclude=()):
    """返回和这份证明重合最多的旧文件：dict(copied, overlap, shared, source)。没有可比的行时 overlap 为 0。
    exclude：不算来源的目录和文件，例如组合拆解接着跑时它自己上一次留下的引理。"""
    mine = lines(text)
    best = dict(copied=False, overlap=0.0, shared=0, source=None)
    if not mine:
        return best
    for path, mtime in sources(before, roots, exclude):
        shared = len(mine & _file_lines(path, mtime))
        if shared > best['shared']:
            best.update(shared=shared, overlap=round(shared / len(mine), 3), source=str(path))
    best['copied'] = best['overlap'] >= THRESHOLD and best['shared'] >= MIN_SHARED
    return best
