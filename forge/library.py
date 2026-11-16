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


_held = __import__('threading').local()


@contextlib.contextmanager
def locked():
    """入库串行化：多个 agent 并行证明，由这一把锁保证库的追加和构建一次只发生一个。macOS/Linux 与 Windows 都可用。

    同一线程里可以嵌套（例如持锁时再调用 consistency()）：文件锁按打开的文件计，同一进程再开一次会等自己，
    以前这样死锁过、把所有入库卡住了六分钟，所以嵌套时直接复用外层的锁。"""
    if getattr(_held, 'depth', 0):
        _held.depth += 1
        try:
            yield
        finally:
            _held.depth -= 1
        return
    DATA.mkdir(parents=True, exist_ok=True)
    with open(LOCK, 'a+') as handle:
        _lock(handle)
        _held.depth = 1
        try:
            yield
        finally:
            _held.depth = 0
            _unlock(handle)


LIBRARY_PATHS = ['forge/data/ledger.jsonl', 'lean/Mathlib2', 'lean/Mathlib2.lean', 'forge/data/tasks', 'forge/data/helpers.json']
# 实验结果可以随快照一起提交，代码不行：代码走 worktree 和 PR。
DATA_DIRS = ('forge/data/', 'lean/Mathlib2/', 'phase2/benchmarks/', 'reports/', 'audits/', 'lean/Research/')


def is_data(path):
    norm = os.path.normpath(path).replace(os.sep, '/')
    return '..' not in norm.split('/') and (norm == 'lean/Mathlib2.lean' or norm.startswith(DATA_DIRS) or norm + '/' in DATA_DIRS)


def _git(*args):
    import subprocess
    from .leanrun import ROOT
    return subprocess.run(['git', *args], cwd=ROOT, capture_output=True, text=True)


def _gh(*args):
    import subprocess
    from .leanrun import ROOT
    return subprocess.run(['gh', *args], cwd=ROOT, capture_output=True, text=True)


def _unpublished_paths():
    """本地 main 相对 origin/main 改过的路径（合并基之后）。git 出错时返回 None。"""
    diff = _git('diff', '--name-only', '-z', 'origin/main...HEAD')
    return None if diff.returncode else [p for p in diff.stdout.split('\0') if p]


def snapshot(message, include=(), publish=True):
    """持锁提交库的快照（台账、分片、任务、辅助引理索引，加上 include 里的实验结果），提交前核对台账与分片一致。

    在主检出的 main 上且 publish 时，把未发布的提交推到数据分支并请求 CI 通过后自动合并：已有打开的数据 PR
    就推到它的分支上，没有才开新 PR。主检出从不直接推 main。在其他分支上（例如升级分支）只在本地提交。"""
    from .leanrun import ROOT
    from .regressions import consistency
    bad = [p for p in include if not is_data(p)]
    if bad:
        return dict(ok=False, reason='--include 只能是数据或实验结果路径', paths=bad, allowed=list(DATA_DIRS))
    paths = [p for p in LIBRARY_PATHS + list(include) if (ROOT / p).exists()]
    on_main = _git('rev-parse', '--abbrev-ref', 'HEAD').stdout.strip() == 'main'
    publish = publish and on_main
    if publish:
        if _git('fetch', '-q', 'origin', 'main').returncode:
            return dict(ok=False, reason='fetch 失败，没有提交')
        changed = _unpublished_paths()
        if changed is None:
            return dict(ok=False, reason='无法比较本地 main 与 origin/main，没有提交')
        code = [p for p in changed if not is_data(p)]
        if code:
            return dict(ok=False, reason='本地 main 上有没走 PR 的代码提交，先把它们移到分支开 PR', paths=code)
    with locked():
        problems = consistency()
        if any(problems.values()):
            return dict(ok=False, reason='台账与分片不一致，没有提交', problems=problems)
        added = _git('add', '-A', '--', *paths)
        if added.returncode:
            return dict(ok=False, reason='git add 失败', error=added.stderr.strip()[-300:])
        committed = _git('diff', '--cached', '--quiet', '--', *paths).returncode != 0
        if committed and _git('commit', '-q', '-m', message, '--', *paths).returncode:
            return dict(ok=False, reason='git commit 失败')
    result = dict(ok=True, committed=committed, commit=_git('rev-parse', '--short', 'HEAD').stdout.strip())
    if not publish:
        return dict(result, published=False, **({} if on_main else dict(reason='不在 main 上，只在本地提交')))
    if _git('rev-list', '--count', 'origin/main..HEAD').stdout.strip() == '0':
        return dict(result, published=False, reason='没有未发布的提交')
    listed = _gh('pr', 'list', '--state', 'open', '--base', 'main', '--limit', '100', '--json', 'headRefName,url')
    if listed.returncode:
        return dict(result, ok=False, published=False, reason='查询打开的 PR 失败', error=listed.stderr.strip()[-300:])
    open_data = [pr for pr in json.loads(listed.stdout or '[]') if pr['headRefName'].startswith('data/')]
    branch = open_data[0]['headRefName'] if open_data else 'data/' + time.strftime('%Y%m%d-%H%M%S-') + uuid.uuid4().hex[:6]
    pushed = _git('push', '-q', 'origin', f'HEAD:refs/heads/{branch}')
    if pushed.returncode:
        return dict(result, ok=False, published=False, branch=branch, reason='推送数据分支失败', error=pushed.stderr.strip()[-500:])
    if open_data:
        return dict(result, published=True, pr=open_data[0]['url'], updated_existing_pr=True)
    body = '由 `forge snapshot` 生成的库与实验数据快照（风险级别：低）。CI 核对台账与分片、重建并审计全库，通过后自动合并。'
    pr = _gh('pr', 'create', '--base', 'main', '--head', branch, '--title', f'data: {message}', '--body', body)
    if pr.returncode:
        return dict(result, ok=False, published=False, branch=branch, reason='开 PR 失败', error=pr.stderr.strip()[-500:])
    url = pr.stdout.strip().splitlines()[-1]
    auto = _gh('pr', 'merge', url, '--auto', '--merge')
    result.update(published=True, pr=url, auto_merge=auto.returncode == 0)
    if auto.returncode:
        result['auto_merge_error'] = auto.stderr.strip()[-300:]
    return result


def sync():
    """主检出拿到 main 上新合并的代码和数据，不碰未提交的数据。

    本地 main 上的数据提交只要内容已经在 origin/main 里（不论用 merge、squash 还是 rebase 合并的），就直接对齐到
    origin/main（git reset --keep：有未提交改动的文件若要被改写就中止）。内容还没进去就等数据 PR 合并。"""
    if _git('rev-parse', '--abbrev-ref', 'HEAD').stdout.strip() != 'main':
        return dict(ok=False, reason='只在主检出的 main 上同步')
    with locked():
        fetched = _git('fetch', '-q', 'origin', 'main')
        if fetched.returncode:
            return dict(ok=False, reason='fetch 失败', error=fetched.stderr.strip()[-300:])
        changed = _unpublished_paths()
        if changed is None:
            return dict(ok=False, reason='无法比较本地 main 与 origin/main')
        if changed and _git('diff', '--quiet', 'HEAD', 'origin/main', '--', *changed).returncode:
            pending = _git('diff', '--name-only', 'HEAD', 'origin/main', '--', *changed).stdout.split()
            return dict(ok=False, reason='本地 main 上的数据提交还没进 origin/main，等数据 PR 合并后再同步', paths=pending[:20])
        moved = _git('reset', '-q', '--keep', 'origin/main')
        if moved.returncode:
            return dict(ok=False, reason='对齐 origin/main 失败（有未提交改动的文件会被改写）', error=moved.stderr.strip()[-500:])
    return dict(ok=True, head=_git('rev-parse', '--short', 'HEAD').stdout.strip())


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
