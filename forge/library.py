"""Mathlib2 库与台账：追加式分片 + 构建门禁。库任何时刻都必须能 `lake build` 通过。"""
import contextlib
import fcntl
import json
import re
import time

from .leanrun import DATA, PROJECT, lake_build
from .verify import HEARTBEATS

LEDGER = DATA / 'ledger.jsonl'
LOCK = DATA / 'library.lock'
SHARDS = PROJECT / 'Mathlib2' / 'Shard'
ROOT_FILE = PROJECT / 'Mathlib2.lean'
SHARD_SIZE = 20  # 每次入库要重编当前分片，分片越小入库越快；分片之间线性依赖，后面的可以引用前面的


@contextlib.contextmanager
def locked():
    """入库串行化：多个 agent 并行证明，由这一把锁保证库的追加和构建一次只发生一个。"""
    DATA.mkdir(parents=True, exist_ok=True)
    with open(LOCK, 'w') as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


def entries():
    if not LEDGER.exists():
        return []
    return [json.loads(line) for line in LEDGER.read_text(encoding='utf-8').splitlines() if line.strip()]


def _shard_path(index):
    return SHARDS / f'S{index:04d}.lean'


def _current_shard():
    SHARDS.mkdir(parents=True, exist_ok=True)
    existing = sorted(SHARDS.glob('S*.lean'))
    if not existing:
        return 1, 0
    index = int(existing[-1].stem[1:])
    count = len(re.findall(r'^-- forge:entry ', existing[-1].read_text(encoding='utf-8'), re.M))
    return (index, count) if count < SHARD_SIZE else (index + 1, 0)


def _write_root():
    shards = sorted(p.stem for p in SHARDS.glob('S*.lean'))
    header = ('/-\nMathlib2：机器生成、内核验证的定理库。\n本文件由 forge 维护：每个分片追加后在这里登记。请勿手改。\n-/\n'
              'import Mathlib\n')
    ROOT_FILE.write_text(header + ''.join(f'import Mathlib2.Shard.{s}\n' for s in shards), encoding='utf-8')


def admit(task, body, check, proved_by):
    """把已通过校验的提交追加进库并重建；构建失败则原样回滚。调用方须持有 locked()。"""
    index, count = _current_shard()
    path = _shard_path(index)
    before_shard = path.read_text(encoding='utf-8') if path.exists() else None
    before_root = ROOT_FILE.read_text(encoding='utf-8')
    if before_shard is None:
        previous = f'import Mathlib2.Shard.S{index - 1:04d}\n' if index > 1 else ''
        text = (f'/- Mathlib2 分片 {index}（forge 自动维护，追加式）。 -/\nimport Mathlib\n{previous}'
                f'set_option maxHeartbeats {HEARTBEATS}\nnamespace Mathlib2\n\nend Mathlib2\n')
    else:
        text = before_shard
    doc = (task.get('informal') or '').replace('-/', '- /').strip()
    block = f'-- forge:entry {task["name"]} kind={check["kind"]} origin={task.get("origin", "")}\nsection\n'
    if doc:
        block += f'/- {doc} -/\n'
    block += body.rstrip('\n') + '\nend\n\n'
    marker = 'end Mathlib2\n'
    position = text.rindex(marker)
    path.write_text(text[:position] + block + text[position:], encoding='utf-8')
    _write_root()
    code, output = lake_build('Mathlib2')
    if code != 0 or "declaration uses 'sorry'" in output:
        if before_shard is None:
            path.unlink()
        else:
            path.write_text(before_shard, encoding='utf-8')
        ROOT_FILE.write_text(before_root, encoding='utf-8')
        lake_build('Mathlib2')
        return dict(ok=False, reason='入库构建失败，已回滚', build_tail=output[-1500:])
    entry = dict(name=task['name'] + ('_disproof' if check['kind'] == 'disproved' else ''), task=task['name'],
                 kind=check['kind'], statement=task['statement'], type=check['type'], hash=task.get('hash'),
                 informal=task.get('informal', ''), origin=task.get('origin', ''), source=task.get('source', ''),
                 tier=task.get('tier', 'agent'), proved_by=proved_by, attempts=len(task.get('attempts', [])) + 1,
                 axioms=check['axioms'], library_deps=check['library_deps'], external_deps=check['external_deps'],
                 helpers=check['names'][:-1], shard=path.stem, lines=body.count('\n') + 1,
                 admitted_at=time.strftime('%Y-%m-%dT%H:%M:%S%z'))
    with open(LEDGER, 'a', encoding='utf-8') as handle:
        handle.write(json.dumps(entry, ensure_ascii=False) + '\n')
    return dict(ok=True, entry=entry)


def source(name):
    """库里某条定理（或其辅助引理所属条目）的完整 Lean 源码块，供复用其中的证明步骤。"""
    owner = None
    for entry in entries():
        if name == entry['name'] or name == entry['task'] or name in entry.get('helpers', []):
            owner = entry
            break
    if owner is None:
        return None
    text = (SHARDS / f'{owner["shard"]}.lean').read_text(encoding='utf-8')
    marker = f'-- forge:entry {owner["task"]} '
    start = text.find(marker)
    if start < 0:
        return None
    following = text.find('-- forge:entry ', start + len(marker))
    end = following if following >= 0 else text.rindex('end Mathlib2')
    return dict(entry=owner['name'], shard=owner['shard'], lean=text[start:end].rstrip() + '\n')


HELPERS = DATA / 'helpers.json'


def helper_index():
    """辅助引理索引：名字不带内容（<任务>_aux1），所以按命题内容登记，供检索和查重。"""
    if not HELPERS.exists():
        return {}
    return json.loads(HELPERS.read_text(encoding='utf-8'))


def record_helpers(owner, helper_info):
    index = helper_index()
    for name, info in helper_info.items():
        index[name] = dict(owner=owner, type=info['type'], hash=info['hash'])
    HELPERS.write_text(json.dumps(index, ensure_ascii=False, indent=1), encoding='utf-8')


def same_statement(hashes, exclude=()):
    """库里已有、命题结构哈希相同的声明（条目或辅助引理）。"""
    found = {}
    for name, info in helper_index().items():
        if info['hash'] in hashes and name not in exclude:
            found.setdefault(info['hash'], []).append(name)
    for entry in entries():
        if entry.get('hash') in hashes and entry['name'] not in exclude:
            found.setdefault(entry['hash'], []).append(entry['name'])
    return found
