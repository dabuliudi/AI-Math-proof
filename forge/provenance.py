"""抄写检测：评测题解出后，看这份证明是不是从更早的轮次留下的证明里抄来的。

事故（2026-11-17）：agent 在仓库里能读到以前各轮留下的草稿和证明（forge/data/staging），改进循环的几轮里
有 2–5 道题的“解出”和更早的证明重合 30%–70%，例如 erdos 1062 抄了组合拆解 pf-k6-1 的拼装结果。
这样的解出量的是“能不能找到旧答案”，不是 harness 的水平，不能拿来比较配置。

草稿已经移出仓库（leanrun.SCRATCH），但 agent 仍然读得到整个磁盘，所以这里是最后一道关：
把解出的证明逐行和本轮开始之前就存在的所有草稿、拆解状态比，取重合最多的一份。
只比较草稿和拆解状态，不比较 Mathlib2 库本身——引用库里的定理是知识复利，正是想要的。
"""
import json
import threading
from pathlib import Path

from .leanrun import DATA, SCRATCH

# 旧位置（移出仓库之前）：里面的文件还在，照样算作可能被抄的来源
LEGACY = (DATA / 'staging' / 'agents', DATA / 'staging' / 'portfolio')
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


def sources(before, roots=None):
    """在 before（时间戳）之前就存在的草稿和拆解状态文件。"""
    for root in roots or (SCRATCH, *LEGACY):
        root = Path(root)
        if not root.is_dir():
            continue
        for path in root.rglob('*'):
            if path.suffix not in ('.lean', '.json') or not path.is_file():
                continue
            try:
                mtime = path.stat().st_mtime
            except OSError:
                continue
            if mtime < before:
                yield path, mtime


def check(text, before, roots=None):
    """返回和这份证明重合最多的旧文件：dict(copied, overlap, shared, source)。没有可比的行时 overlap 为 0。"""
    mine = lines(text)
    best = dict(copied=False, overlap=0.0, shared=0, source=None)
    if not mine:
        return best
    for path, mtime in sources(before, roots):
        shared = len(mine & _file_lines(path, mtime))
        if shared > best['shared']:
            best.update(shared=shared, overlap=round(shared / len(mine), 3), source=str(path))
    best['copied'] = best['overlap'] >= THRESHOLD and best['shared'] >= MIN_SHARED
    return best
