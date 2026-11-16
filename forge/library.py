"""Mathlib2 库与台账：追加式分片 + 构建门禁。库任何时刻都必须能 `lake build` 通过。"""
import contextlib
import hashlib
import json
import os
import re
import signal
import subprocess
import time
import uuid
from pathlib import Path

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


def _git(*args, index=None):
    import subprocess
    from .leanrun import ROOT
    env = dict(os.environ, GIT_INDEX_FILE=str(index)) if index else None
    return subprocess.run(['git', *args], cwd=ROOT, capture_output=True, text=True, env=env)


def _blob(rev, path):
    found = _git('rev-parse', '-q', '--verify', f'{rev}:{path}')
    return found.stdout.strip() if found.returncode == 0 else None


def _publish_commit(message):
    """在 origin/main 上做一个提交，内容是 origin/main 加上本地 main 里还没进去的数据改动。

    不直接推本地 main 的历史：数据 PR 若被 squash 或 rebase 合并，旧提交还留在本地历史里，再推就会和 main 冲突。
    返回 (提交, 路径, 冲突路径)；没有要发布的改动时提交为 None。"""
    import tempfile
    base = _git('merge-base', 'origin/main', 'HEAD').stdout.strip()
    local = [p for p in _git('diff', '--name-only', '-z', base, 'HEAD').stdout.split('\0') if p]
    todo = [p for p in local if _blob('HEAD', p) != _blob('origin/main', p)]
    if not todo:
        return None, [], []
    ours = _git('rev-list', f'{base}..HEAD').stdout.split()
    conflicts = [p for p in todo if _blob('origin/main', p) != _blob(base, p)
                 and _blob('origin/main', p) not in {_blob(c, p) for c in ours}]
    if conflicts:
        return None, todo, conflicts
    with tempfile.TemporaryDirectory() as tmp:
        index = Path(tmp) / 'index'
        _git('read-tree', 'origin/main', index=index)
        for path in todo:
            blob = _blob('HEAD', path)
            if blob:
                mode = _git('ls-tree', 'HEAD', '--', path).stdout.split()[0]
                _git('update-index', '--add', '--cacheinfo', f'{mode},{blob},{path}', index=index)
            else:
                _git('update-index', '--force-remove', '--', path, index=index)
        tree = _git('write-tree', index=index).stdout.strip()
    commit = _git('commit-tree', tree, '-p', 'origin/main', '-m', message).stdout.strip()
    return commit or None, todo, []


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

    在主检出的 main 上且 publish 时，把还没进 origin/main 的数据改动做成 origin/main 上的一个提交，推到数据分支，
    请求 CI 通过后自动 squash 合并：已有打开的数据 PR 就更新它的分支，没有才开新 PR。主检出从不直接推 main。在其他分支上（例如升级分支）只在本地提交。"""
    from .leanrun import ROOT
    from .regressions import consistency
    bad = [p for p in include if not is_data(p)]
    if bad:
        return dict(ok=False, reason='--include 只能是数据或实验结果路径', paths=bad, allowed=list(DATA_DIRS))
    paths = [p for p in LIBRARY_PATHS + list(include) if (ROOT / p).exists() or _git('ls-files', '--', p).stdout]
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
        staged = [p for p in _git('diff', '--cached', '--name-only', '-z', '--', *paths).stdout.split('\0') if p]
        if staged:
            made = _git('commit', '-q', '-m', message, '--', *staged)
            if made.returncode:
                return dict(ok=False, reason='git commit 失败', error=made.stderr.strip()[-300:])
        committed = bool(staged)
    result = dict(ok=True, committed=committed, commit=_git('rev-parse', '--short', 'HEAD').stdout.strip())
    if not publish:
        return dict(result, published=False, **({} if on_main else dict(reason='不在 main 上，只在本地提交')))
    commit, todo, conflicts = _publish_commit(message)
    if conflicts:
        return dict(result, ok=False, published=False, reason='这些数据在 origin/main 上也被别处改过，先手动合并', paths=conflicts)
    if not commit:
        return dict(result, published=False, reason='没有未发布的数据改动')
    listed = _gh('pr', 'list', '--state', 'open', '--base', 'main', '--limit', '100', '--json', 'headRefName,url')
    if listed.returncode:
        return dict(result, ok=False, published=False, reason='查询打开的 PR 失败', error=listed.stderr.strip()[-300:])
    open_data = [pr for pr in json.loads(listed.stdout or '[]') if pr['headRefName'].startswith('data/')]
    branch = open_data[0]['headRefName'] if open_data else 'data/' + time.strftime('%Y%m%d-%H%M%S-') + uuid.uuid4().hex[:6]
    pushed = _git('push', '-q', '--force', 'origin', f'{commit}:refs/heads/{branch}')  # 数据分支每次从 origin/main 重建
    if pushed.returncode:
        return dict(result, ok=False, published=False, branch=branch, reason='推送数据分支失败', error=pushed.stderr.strip()[-500:])
    if open_data:
        return dict(result, published=True, pr=open_data[0]['url'], updated_existing_pr=True)
    body = '由 `forge snapshot` 生成的库与实验数据快照（风险级别：低）。CI 核对台账与分片、重建并审计全库，通过后自动合并。'
    pr = _gh('pr', 'create', '--base', 'main', '--head', branch, '--title', f'data: {message}', '--body', body)
    if pr.returncode:
        return dict(result, ok=False, published=False, branch=branch, reason='开 PR 失败', error=pr.stderr.strip()[-500:])
    url = pr.stdout.strip().splitlines()[-1]
    auto = _gh('pr', 'merge', url, '--auto', '--squash')
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
            pending = [p for p in _git('diff', '--name-only', '-z', 'HEAD', 'origin/main', '--', *changed).stdout.split('\0') if p]
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


def _append(task, body, check, journal):
    """把一条提交追加到当前分片末尾；首次改动某个分片前把原文记进回滚日志并落盘。"""
    index, count = _current_shard()
    path = _shard_path(index)
    if str(path) not in journal['shards']:
        journal['shards'][str(path)] = path.read_text(encoding='utf-8') if path.exists() else None
        _save_journal(journal)
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


JOURNAL = DATA / 'admit-journal.json'
MARKER = 'end Mathlib2\n'


def _write_durable(path, text):
    temporary = path.with_name(f'{path.name}.{os.getpid()}.tmp')
    with open(temporary, 'w', encoding='utf-8') as handle:
        handle.write(text)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def _save_journal(journal):
    _write_durable(JOURNAL, json.dumps(journal, ensure_ascii=False))


def _ledger_bytes():
    return LEDGER.read_bytes() if LEDGER.exists() else b''


def _entry_names(text):
    return re.findall(r'^-- forge:entry (\S+) ', text, re.M)


def _journal_matches(journal):
    """日志只在库没被别人改过时可信：台账前缀和记下的一样、其后只有这一批的条目，
    每个分片只是在原文的 end Mathlib2 前插进了这一批的条目。"""
    names = set(journal['names'])
    ledger = _ledger_bytes()
    size = journal['ledger_size']
    if len(ledger) < size or hashlib.sha256(ledger[:size]).hexdigest() != journal['ledger_digest']:
        return False
    for line in ledger[size:].decode('utf-8', errors='replace').split('\n')[:-1]:
        try:
            if json.loads(line)['task'] not in names:
                return False
        except (ValueError, KeyError, TypeError):
            return False
    for path, original in journal['shards'].items():
        path = Path(path)
        if not path.exists():
            if original is not None:
                return False
            continue
        current = path.read_text(encoding='utf-8')
        head, tail = ('', '') if original is None else (original[:original.rindex(MARKER)], original[original.rindex(MARKER):])
        if not (current.startswith(head) and current.endswith(tail) and len(current) >= len(head) + len(tail)):
            return False
        if not set(_entry_names(current[len(head):len(current) - len(tail)])) <= names:
            return False
    return True


def _library_consistent():
    """台账与分片一一对应、分片里没有重复条目。"""
    in_shards = []
    for path in sorted(SHARDS.glob('S*.lean')):
        in_shards += _entry_names(path.read_text(encoding='utf-8'))
    return len(in_shards) == len(set(in_shards)) and set(in_shards) == {e['task'] for e in entries()}


def _restore(journal):
    """把分片、根文件和台账恢复到入库前的样子，再删掉回滚日志。"""
    for path, text in journal['shards'].items():
        if text is None:
            Path(path).unlink(missing_ok=True)
        else:
            Path(path).write_text(text, encoding='utf-8')
    ROOT_FILE.write_text(journal['root'], encoding='utf-8')
    if LEDGER.exists():
        with open(LEDGER, 'r+b') as handle:
            handle.truncate(journal['ledger_size'])
    JOURNAL.unlink(missing_ok=True)


def _finish_tickets(tickets, results):
    for path, result in zip(tickets, results):
        if path.exists():
            _write_durable(path.with_suffix('.done'), json.dumps(result, ensure_ascii=False))
            path.unlink()


def _kill_build(pgid):
    """结束上一个入库进程留下的构建（它被杀掉时 lake 和 lean 不会跟着退出）。只结束确实是 lake/lean 的进程组。"""
    if not pgid or os.name == 'nt':
        return
    listing = subprocess.run(['ps', '-A', '-o', 'pgid=,comm='], capture_output=True, text=True).stdout
    commands = [line.split(None, 1)[1] for line in listing.splitlines()
                if len(line.split(None, 1)) == 2 and line.split(None, 1)[0] == str(pgid)]
    if any(Path(c.strip()).name in ('lake', 'lean') for c in commands):
        try:
            os.killpg(pgid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass


def recover():
    """上一次入库做到一半被杀掉（进程被结束、构建超时）时，持锁后先收拾：
    已写完台账的（日志标了 committed）把待入库票据补写完；没写完的把分片和台账恢复原样。
    日志读不出来或与当前库对不上（之后有别人改过库）就不按它恢复，挪到一边；此时库本身一致才继续，否则报错停下等人处理。

    （事故：提交进程在构建中途被结束，没有回滚，待入库的提交又被后来的进程重放了两次，
    同一批 4 条定理在分片里出现了三份、都没进台账，库从此建不过。）调用方须持有 locked()。"""
    if not JOURNAL.exists():
        return False
    try:
        journal = json.loads(JOURNAL.read_text(encoding='utf-8'))
        journal['names'], journal['root'], journal['ledger_size'], journal['ledger_digest'], journal['shards']
    except (ValueError, KeyError, TypeError):
        journal = None
    if journal is not None and 'committed' in journal:
        _finish_tickets([Path(t) for t in journal['tickets']], journal['committed'])
        JOURNAL.unlink(missing_ok=True)
        return True
    if journal is not None:
        _kill_build(journal.get('build'))
        if _journal_matches(journal):
            _restore(journal)
            return True
    os.replace(JOURNAL, JOURNAL.with_name(f'admit-journal.rejected-{time.strftime("%Y%m%d-%H%M%S")}.json'))
    if not _library_consistent():
        raise RuntimeError(f'入库回滚日志不可信（已挪到 {JOURNAL.parent} 下的 admit-journal.rejected-*），'
                           '而台账与分片不一致：需要人工修复后再入库')
    return True


def admit_batch(items, tickets=None):
    """把一批已通过校验的提交 [(task, body, check, proved_by)] 一起追加、只构建一次。

    构建失败或出错（例如构建超时）则整批原样回滚；多于一条时再逐条入库，找出是哪一条有问题，其余照常入库。调用方须持有 locked()。
    tickets 是与 items 对应的待入库票据：结果写进票据的 .done，与台账在同一个回滚日志里完成，进程中途死掉也不会重放已入库的票据。
    改动前先把原文写进回滚日志：进程中途死掉，下一个持锁入库的进程会先恢复。
    """
    tickets = list(tickets) if tickets is not None else [None] * len(items)
    recover()
    ledger = _ledger_bytes()
    journal = dict(names=[task['name'] for task, _, _, _ in items], root=ROOT_FILE.read_text(encoding='utf-8'),
                   ledger_size=len(ledger),
                   ledger_digest=hashlib.sha256(ledger).hexdigest(), shards={}, build=None)
    _save_journal(journal)

    def started(pid):
        journal['build'] = pid
        _save_journal(journal)

    results, restored = None, False
    try:
        paths = [_append(task, body, check, journal) for task, body, check, _ in items]
        _write_root()
        code, output = lake_build('Mathlib2', on_start=started)
        if code == 0 and "declaration uses 'sorry'" not in output:
            results = [dict(ok=True, entry=_ledger_entry(task, body, check, proved_by, path), batch=len(items))
                       for (task, body, check, proved_by), path in zip(items, paths)]
            with open(LEDGER, 'a', encoding='utf-8') as handle:
                handle.write(''.join(json.dumps(r['entry'], ensure_ascii=False) + '\n' for r in results))
                handle.flush()
                os.fsync(handle.fileno())
            # 从这里起这一批算入库了：日志改成 committed，之后死掉由下一个进程把票据补写完，而不是回滚
            journal.update(committed=[r for r, t in zip(results, tickets) if t is not None],
                           tickets=[str(t) for t in tickets if t is not None])
            _save_journal(journal)
        else:
            failure = dict(ok=False, reason='入库构建失败，已回滚', build_tail=output[-1500:])
    except Exception as exc:
        if 'committed' in journal:
            raise
        _restore(journal)
        results, restored = None, True
        failure = dict(ok=False, reason=f'入库时出错（{type(exc).__name__}: {str(exc)[:300]}），已回滚')
    except BaseException:
        if 'committed' not in journal:
            _restore(journal)
        raise
    if results is not None:
        _finish_tickets([Path(t) for t in journal['tickets']], journal['committed'])
        JOURNAL.unlink()
        return results
    if not restored:  # 构建失败：恢复后重建一次，让 .olean 回到库的当前状态
        _restore(journal)
        lake_build('Mathlib2')
    if len(items) == 1:
        if tickets[0] is not None:
            _finish_tickets(tickets, [failure])
        return [failure]
    return [admit_batch([item], [ticket])[0] for item, ticket in zip(items, tickets)]


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
        recover()
        if not done.exists():
            waiting = sorted(PENDING.glob('*.json'))
            items = [json.loads(p.read_text(encoding='utf-8')) for p in waiting]
            admit_batch([(i['task'], i['body'], i['check'], i['proved_by']) for i in items], tickets=waiting)
        result = json.loads(done.read_text(encoding='utf-8'))
        done.unlink()
        stale = time.time() - 86400  # 提交者已经死掉、没人来取的结果
        for path in PENDING.glob('*.done'):
            if path.stat().st_mtime < stale:
                path.unlink(missing_ok=True)
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
