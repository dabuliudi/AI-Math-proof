"""Mathlib2 库与台账：追加式分片 + 构建门禁。库任何时刻都必须能 `lake build` 通过。"""
import contextlib
import json
import os
import re
import time
import uuid

from .leanrun import DATA, PROJECT, lake_build
from .verify import HEARTBEATS

LEDGER = DATA / 'ledger.jsonl'
LOCK = DATA / 'library.lock'
SHARDS = PROJECT / 'Mathlib2' / 'Shard'
ROOT_FILE = PROJECT / 'Mathlib2.lean'
SHARD_SIZE = 20  # 每次入库要重编当前分片，分片越小入库越快；分片之间线性依赖，后面的可以引用前面的


if os.name == 'nt':
    import msvcrt

    def _lock(handle):
        while True:  # msvcrt 的阻塞锁最多等 10 秒就报错，所以自己循环
            try:
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_LOCK, 1)
                return
            except OSError:
                time.sleep(0.5)

    def _unlock(handle):
        handle.seek(0)
        msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
else:
    import fcntl

    def _lock(handle):
        fcntl.flock(handle, fcntl.LOCK_EX)

    def _unlock(handle):
        fcntl.flock(handle, fcntl.LOCK_UN)


@contextlib.contextmanager
def locked():
    """入库串行化：多个 agent 并行证明，由这一把锁保证库的追加和构建一次只发生一个。macOS/Linux 与 Windows 都可用。"""
    DATA.mkdir(parents=True, exist_ok=True)
    with open(LOCK, 'a+') as handle:
        _lock(handle)
        try:
            yield
        finally:
            _unlock(handle)


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


def _append(task, body, check, snapshots):
    """把一条提交追加到当前分片末尾；首次改动某个分片前记下原文，供回滚。"""
    index, count = _current_shard()
    path = _shard_path(index)
    if path not in snapshots:
        snapshots[path] = path.read_text(encoding='utf-8') if path.exists() else None
    if path.exists():
        text = path.read_text(encoding='utf-8')
    else:
        previous = f'import Mathlib2.Shard.S{index - 1:04d}\n' if index > 1 else ''
        text = (f'/- Mathlib2 分片 {index}（forge 自动维护，追加式）。 -/\nimport Mathlib\n{previous}'
                f'set_option maxHeartbeats {HEARTBEATS}\nnamespace Mathlib2\n\nend Mathlib2\n')
    doc = (task.get('informal') or '').replace('-/', '- /').strip()
    block = f'-- forge:entry {task["name"]} kind={check["kind"]} origin={task.get("origin", "")}\nsection\n'
    if doc:
        block += f'/- {doc} -/\n'
    block += body.rstrip('\n') + '\nend\n\n'
    marker = 'end Mathlib2\n'
    position = text.rindex(marker)
    path.write_text(text[:position] + block + text[position:], encoding='utf-8')
    return path


def _ledger_entry(task, body, check, proved_by, path):
    return dict(name=task['name'] + ('_disproof' if check['kind'] == 'disproved' else ''), task=task['name'],
                kind=check['kind'], statement=task['statement'], type=check['type'], hash=task.get('hash'),
                informal=task.get('informal', ''), origin=task.get('origin', ''), source=task.get('source', ''),
                tier=task.get('tier', 'agent'), proved_by=proved_by, attempts=len(task.get('attempts', [])) + 1,
                axioms=check['axioms'], library_deps=check['library_deps'], external_deps=check['external_deps'],
                helpers=check['names'][:-1], shard=path.stem, lines=body.count('\n') + 1,
                admitted_at=time.strftime('%Y-%m-%dT%H:%M:%S%z'))


def admit_batch(items):
    """把一批已通过校验的提交 [(task, body, check, proved_by)] 一起追加、只构建一次。

    构建失败则整批原样回滚；多于一条时再逐条入库，找出是哪一条有问题，其余照常入库。调用方须持有 locked()。
    """
    snapshots = {}
    before_root = ROOT_FILE.read_text(encoding='utf-8')
    paths = [_append(task, body, check, snapshots) for task, body, check, _ in items]
    _write_root()
    code, output = lake_build('Mathlib2')
    if code == 0 and "declaration uses 'sorry'" not in output:
        results = []
        with open(LEDGER, 'a', encoding='utf-8') as handle:
            for (task, body, check, proved_by), path in zip(items, paths):
                entry = _ledger_entry(task, body, check, proved_by, path)
                handle.write(json.dumps(entry, ensure_ascii=False) + '\n')
                results.append(dict(ok=True, entry=entry, batch=len(items)))
        return results
    for path, text in snapshots.items():
        if text is None:
            path.unlink(missing_ok=True)
        else:
            path.write_text(text, encoding='utf-8')
    ROOT_FILE.write_text(before_root, encoding='utf-8')
    lake_build('Mathlib2')
    if len(items) == 1:
        return [dict(ok=False, reason='入库构建失败，已回滚', build_tail=output[-1500:])]
    return [admit_batch([item])[0] for item in items]


def admit(task, body, check, proved_by):
    """把一条已通过校验的提交追加进库并重建；构建失败则原样回滚。调用方须持有 locked()。"""
    return admit_batch([(task, body, check, proved_by)])[0]


PENDING = DATA / 'pending'


def commit(task, body, check, proved_by):
    """组提交：先把提交放进待入库区，再抢锁；抢到锁的进程把当时排队的所有提交合并成一次构建。

    并行证明时，一次 `lake build` 的时间（约半分钟到一分钟）原本要乘以提交数，现在由同一时段的提交分摊。
    """
    PENDING.mkdir(parents=True, exist_ok=True)
    ticket = f'{time.time():.6f}-{uuid.uuid4().hex[:8]}'
    staged = PENDING / f'{ticket}.tmp'
    staged.write_text(json.dumps(dict(task=task, body=body, check=check, proved_by=proved_by), ensure_ascii=False),
                      encoding='utf-8')
    staged.rename(PENDING / f'{ticket}.json')  # 原子改名：别的进程不会读到写了一半的提交
    done = PENDING / f'{ticket}.done'
    with locked():
        if not done.exists():
            waiting = sorted(PENDING.glob('*.json'))
            items = [json.loads(p.read_text(encoding='utf-8')) for p in waiting]
            results = admit_batch([(i['task'], i['body'], i['check'], i['proved_by']) for i in items])
            for path, result in zip(waiting, results):
                path.with_suffix('.done').write_text(json.dumps(result, ensure_ascii=False), encoding='utf-8')
                path.unlink()
        result = json.loads(done.read_text(encoding='utf-8'))
        done.unlink()
    return result


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
