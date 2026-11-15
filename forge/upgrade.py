"""升级 Mathlib 版本后修复 Mathlib2：按分片顺序编译，编不过的分片交给 agent 只改证明，调度器核对陈述没被改动。

分片之间是线性依赖（后面的分片 import 前面的），所以只能一个一个修。对每个编不过的分片：
1. 把 Lean 报错交给 agent（默认 Codex），只许改证明（声明里 `:=` 之后的部分），不许改任何声明的陈述、名字、条目标记；
2. 调度器自己再编译一次，并逐条比对修复前后每个声明的陈述文本，必须完全一致；
3. 不通过就恢复原文件重试，最多 attempts 次；仍不行就停下，报告卡在哪个分片。
修完以后应再跑一次 `forge audit --replay`，用内核把整个库重新检查一遍。
"""
import json
import re
import time

from .leanrun import DATA, PROJECT, ROOT, lake_build
from .scheduler import FORGE, Scheduler

SHARDS = PROJECT / 'Mathlib2' / 'Shard'
LOG = DATA / 'runs'

REPAIR_PROMPT = '''You are repairing a Lean 4 library after a Mathlib upgrade (Mathlib v4.24 -> {target}). Working directory: {root}.
The file {path} no longer compiles. Your job is to make it compile again by changing PROOFS ONLY.

Rules (checked automatically afterwards; any violation is rejected and reverted):
- Do not change any declaration's statement: the text from `theorem`/`lemma`/`def` up to its `:=` must stay exactly the same,
  and every declaration name must stay. Do not add or remove declarations. Do not touch `-- forge:entry` lines.
- No sorry, admit, axiom, native_decide, set_option or new imports.
- Typical causes: renamed or removed Mathlib lemmas (find the new name with `{forge} lookup "<name fragments>"` or
  `grep -rn "<name>" lean/.lake/packages/mathlib/Mathlib`), changed simp sets, changed tactic behaviour.
Check your work with: cd lean && lake build Mathlib2.Shard.{shard}
Current errors (first {shown} of {count}):
{errors}

You have about {minutes} minutes. Edit only {path}. End with one line: RESULT: fixed | stuck.
'''

# 经过审核的陈述迁移：只收 Mathlib 官方弃用说明给出的等价替换，每条注明出处。
# 修复分片前先对陈述做这些替换；核对“陈述不变”时以替换后的文本为准；修完后台账与任务里的陈述同步替换。
MIGRATIONS = [
    (re.compile(r'\[CancelCommMonoidWithZero (\w+)\]'), r'[CommMonoidWithZero \1] [IsCancelMulZero \1]',
     'Mathlib 2026-01-11 弃用 CancelCommMonoidWithZero：“Use `[CommMonoidWithZero M₀] [IsCancelMulZero M₀]`.”'),
]


def migrate(text):
    """对文本做全部陈述迁移，返回 (新文本, 用到的迁移说明列表)。"""
    used = []
    for pattern, replacement, why in MIGRATIONS:
        text, count = pattern.subn(replacement, text)
        if count:
            used.append(why)
    return text, used


DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev)\s+(\S+)', re.M)


def signatures(text):
    """文件里每个声明的 (名字, 陈述文本)：从声明关键字到第一个顶层 `:=`，空白归一化。"""
    out = {}
    for match in DECL.finditer(text):
        start = match.start()
        depth, i = 0, match.end()
        while i < len(text) - 1:
            ch = text[i]
            if ch in '([{⟨':
                depth += 1
            elif ch in ')]}⟩':
                depth -= 1
            elif text.startswith(':=', i) and depth == 0:
                break
            i += 1
        out[match.group(2)] = ' '.join(text[start:i].split())
    return out


def entry_markers(text):
    return re.findall(r'^-- forge:entry .*$', text, re.M)


FORBIDDEN = re.compile(r'\b(sorry|admit|axiom|native_decide)\b|^\s*set_option\b|^import\b', re.M)


def _errors(output, shard):
    lines = [l for l in output.splitlines() if l.startswith(f'error: Mathlib2/Shard/{shard}.lean')]
    blocks, current = [], None
    for line in output.splitlines():
        if line.startswith('error: '):
            current = [line]
            blocks.append(current)
        elif current is not None and line.startswith(' '):
            current.append(line)
        else:
            current = None
    mine = ['\n'.join(b)[:900] for b in blocks if b[0].startswith(f'error: Mathlib2/Shard/{shard}.lean')]
    return mine or lines


def check_repair(before, after):
    """修复是否合规：声明集合与陈述逐字不变、条目标记不变、没有新增的禁用写法。返回问题列表。"""
    problems = []
    old, new = signatures(before), signatures(after)
    if set(old) != set(new):
        problems.append(f'声明集合变了：多了 {sorted(set(new) - set(old))}，少了 {sorted(set(old) - set(new))}')
    for name in set(old) & set(new):
        if old[name] != new[name]:
            problems.append(f'`{name}` 的陈述被改动')
    if entry_markers(before) != entry_markers(after):
        problems.append('条目标记被改动')
    added = len(FORBIDDEN.findall(after)) - len(FORBIDDEN.findall(before))
    if added > 0:
        problems.append('新增了 sorry/axiom/native_decide/set_option/import 之类的写法')
    return problems


def repair(run, target, attempts=3, minutes=25, start=None, effort='xhigh'):
    """按顺序修复全部分片。返回每个分片的结果；遇到修不好的分片就停下。"""
    agent = Scheduler(run, workers=1, max_tasks=10 ** 6, budget_minutes=10 ** 5, task_minutes=minutes, effort=effort)
    (agent.scratch / 'repair').mkdir(parents=True, exist_ok=True)
    LOG.mkdir(parents=True, exist_ok=True)
    log = LOG / f'{run}.jsonl'
    results = []
    shards = sorted(p.stem for p in SHARDS.glob('S*.lean'))
    if start:
        shards = [s for s in shards if s >= start]
    for shard in shards:
        path = SHARDS / f'{shard}.lean'
        code, output = lake_build(f'Mathlib2.Shard.{shard}')
        if code == 0 and "declaration uses 'sorry'" not in output:
            results.append(dict(shard=shard, status='ok'))
            continue
        original, migrations = migrate(path.read_text(encoding='utf-8'))
        if migrations:  # 先做经过审核的陈述迁移，再判断还需不需要 agent 修
            path.write_text(original, encoding='utf-8')
            code, output = lake_build(f'Mathlib2.Shard.{shard}')
            with open(log, 'a', encoding='utf-8') as handle:
                handle.write(json.dumps(dict(shard=shard, migrated=migrations, built=code == 0,
                                             at=time.strftime('%Y-%m-%dT%H:%M:%S%z')), ensure_ascii=False) + '\n')
            if code == 0 and "declaration uses 'sorry'" not in output:
                results.append(dict(shard=shard, status='migrated', migrations=migrations))
                continue
        fixed = False
        best_text, best_errors = original, len(_errors(output, shard))
        for attempt in range(1, attempts + 1):
            errors = _errors(output, shard)
            prompt = REPAIR_PROMPT.format(target=target, root=ROOT, path=path.relative_to(ROOT), forge=FORGE, shard=shard,
                                          shown=min(len(errors), 12), count=len(errors), errors='\n\n'.join(errors[:12]),
                                          minutes=minutes)
            began = time.time()
            for retry in range(4):
                exit_code, message, tokens, slow = agent._invoke(prompt, 'repair')
                if exit_code == 0 or slow or path.read_text(encoding='utf-8') != original:
                    break
                # agent 自身出错（退出码非 0、没动文件）：不算一次修复尝试，等一会儿、确认 agent 能正常回应后再试
                with open(log, 'a', encoding='utf-8') as handle:
                    handle.write(json.dumps(dict(shard=shard, attempt=attempt, agent_error=exit_code, retry=retry,
                                                 raw=agent.last_raw.get('repair', '')[-1500:],
                                                 at=time.strftime('%Y-%m-%dT%H:%M:%S%z')), ensure_ascii=False) + '\n')
                time.sleep(60 * (retry + 1))
                agent._probe()
            after = path.read_text(encoding='utf-8')
            problems = check_repair(original, after)
            code, output = lake_build(f'Mathlib2.Shard.{shard}')
            built = code == 0 and "declaration uses 'sorry'" not in output
            row = dict(shard=shard, attempt=attempt, built=built, problems=problems, seconds=round(time.time() - began),
                       tokens=tokens, exit=exit_code, errors_before=len(errors), message=message[-300:],
                       raw=agent.last_raw.get('repair', '')[-1500:] if exit_code != 0 else '',
                       at=time.strftime('%Y-%m-%dT%H:%M:%S%z'))
            with open(log, 'a', encoding='utf-8') as handle:
                handle.write(json.dumps(row, ensure_ascii=False) + '\n')
            if built and not problems:
                fixed = True
                results.append(dict(shard=shard, status='repaired', attempts=attempt))
                break
            if problems:  # 违规的修改一律撤销，退回到目前最好的合规版本
                path.write_text(best_text, encoding='utf-8')
                code, output = lake_build(f'Mathlib2.Shard.{shard}')
            else:
                remaining = len(_errors(output, shard))
                if remaining < best_errors:  # 合规但还没修完：报错更少就当作新的起点，下次接着修
                    best_text, best_errors = after, remaining
        if not fixed:
            # 修不完时保留报错最少的合规版本（而不是退回原样），已经修好的部分不丢；下次从这里接着修
            path.write_text(best_text, encoding='utf-8')
            results.append(dict(shard=shard, status='stuck', remaining_errors=best_errors))
            break
    return results


def migrate_records(data=DATA):
    """把陈述迁移同步到台账、任务文件和辅助引理索引里记录的陈述文本，保证之后的审计与库内实际陈述一致。"""
    changed = []
    files = [data / 'ledger.jsonl', data / 'helpers.json'] + sorted((data / 'tasks').glob('*/*.json'))
    for path in files:
        if not path.exists():
            continue
        text = path.read_text(encoding='utf-8')
        new, used = migrate(text)
        if used:
            path.write_text(new, encoding='utf-8')
            changed.append(str(path.relative_to(data)))
    return changed


# ---------------------------------------------------------------------------
# 并行修复：先打桩让所有分片都能编译，再让多个 agent 同时修不同的分片。
#
# 分片是线性依赖的，前一个编不过，后一个连检查都没法做，所以逐片修只能串行。打桩把编不过的证明临时换成
# `sorry`（陈述不动），下游分片就能编译了；这时每个分片可以用 `lake env lean <文件>` 单独检查
# （不写编译产物，多个检查同时跑互不干扰），于是可以并行修。最后核对：陈述不变、一个 sorry 都不剩。
# ---------------------------------------------------------------------------
from concurrent.futures import ThreadPoolExecutor
from .leanrun import run_source  # noqa: F401  (保留给以后按文件检查的扩展)
import subprocess

BOUNDARY = re.compile(r'^(?:-- forge:entry |end\s*$|(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                      r'(?:theorem|lemma|def|abbrev)\s)', re.M)


def _error_lines(output, shard):
    return sorted({int(m.group(1)) for m in re.finditer(rf'^error: Mathlib2/Shard/{shard}\.lean:(\d+):', output, re.M)})


def stub_declarations(text, error_lines):
    """把包含报错行的声明的证明换成 `sorry`；报错落在陈述里（`:=` 之前）的不动。返回 (新文本, 打了桩的声明名)。"""
    offsets = [0]
    for line in text.split('\n'):
        offsets.append(offsets[-1] + len(line) + 1)
    decls = []
    for match in DECL.finditer(text):
        nxt = BOUNDARY.search(text, match.end())
        end = nxt.start() if nxt else len(text)
        depth, i = 0, match.end()
        while i < end - 1:
            ch = text[i]
            if ch in '([{⟨':
                depth += 1
            elif ch in ')]}⟩':
                depth -= 1
            elif text.startswith(':=', i) and depth == 0:
                break
            i += 1
        decls.append((match.group(2), match.start(), i, end))
    targets = {}
    for line in error_lines:
        pos = offsets[min(line - 1, len(offsets) - 1)]
        for name, start, assign, end in decls:
            if start <= pos < end and pos >= assign:   # 报错在证明部分
                targets[name] = (assign, end)
    out, stubbed = text, []
    for name, (assign, end) in sorted(targets.items(), key=lambda kv: -kv[1][0]):  # 从后往前替换，前面的位置不变
        out = out[:assign] + ':= by\n  sorry\n\n' + out[end:]
        stubbed.append(name)
    return out, sorted(stubbed)


def _check_file(path):
    """单独检查一个分片文件（依赖已编译好的上游分片），不写编译产物。返回 (错误列表, 是否还有 sorry)。"""
    from .leanrun import _env, find_lake
    proc = subprocess.run([find_lake(), 'env', 'lean', str(path.relative_to(PROJECT))], cwd=PROJECT, env=_env(),
                          capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=1800)
    out = proc.stdout + proc.stderr
    shard = path.stem
    errors = [b for b in _errors(out.replace(f'{path.relative_to(PROJECT)}', f'Mathlib2/Shard/{shard}.lean'), shard)]
    errors = errors or [l for l in out.splitlines() if ': error' in l or l.startswith('error')]
    return errors, "declaration uses 'sorry'" in out


def stub_pass(start=None):
    """按顺序打桩，直到所有分片都能编译。返回 {分片: (原始文本, 打了桩的声明)}；陈述本身编不过时报告 blocked。"""
    stubs, blocked = {}, []
    for shard in sorted(p.stem for p in SHARDS.glob('S*.lean')):
        if start and shard < start:
            continue
        path = SHARDS / f'{shard}.lean'
        original, _ = migrate(path.read_text(encoding='utf-8'))
        path.write_text(original, encoding='utf-8')
        code, output = lake_build(f'Mathlib2.Shard.{shard}')
        names = []
        for _ in range(6):  # 打桩后可能暴露出新的报错，最多几轮
            if code == 0:
                break
            new, stubbed = stub_declarations(path.read_text(encoding='utf-8'), _error_lines(output, shard))
            if not stubbed:
                break
            names += stubbed
            path.write_text(new, encoding='utf-8')
            code, output = lake_build(f'Mathlib2.Shard.{shard}')
        if code != 0:
            path.write_text(original, encoding='utf-8')
            blocked.append(dict(shard=shard, errors=_errors(output, shard)[:5]))
            break
        if names:
            stubs[shard] = (original, sorted(set(names)))
    return stubs, blocked


PARALLEL_PROMPT = '''You are repairing a Lean 4 library after a Mathlib upgrade (Mathlib v4.24 -> {target}). Working directory: {root}.
In {path}, the proofs of these declarations no longer compiled and were temporarily replaced by `sorry`:
{names}
The original (old-Mathlib) file is saved at {original} for reference: reuse its proof ideas, adapting renamed lemmas,
changed simp sets and changed tactic behaviour.

Your job: replace every one of those `sorry`s with a proof that compiles. Rules (checked automatically; violations are reverted):
- Edit only {path}. Do not change any declaration's statement (text up to its `:=`), names, or `-- forge:entry` lines.
- No sorry, admit, axiom, native_decide, set_option or new imports may remain.
- Find renamed lemmas with `{forge} lookup "<name fragments>"` or `grep -rn "<name>" lean/.lake/packages/mathlib/Mathlib`.
Check the file on its own with: cd lean && lake env lean {relpath}
(it must print no errors and no "declaration uses 'sorry'" warning). Do NOT run `lake build`.
You have about {minutes} minutes. End with one line: RESULT: fixed | stuck.
'''


def parallel_repair(run, target, workers=4, attempts=3, minutes=25, start=None, effort='xhigh'):
    """打桩 → 并行修 → 验收。返回各分片结果；最后按顺序完整编译一次。"""
    LOG.mkdir(parents=True, exist_ok=True)
    log = LOG / f'{run}.jsonl'
    stubs, blocked = stub_pass(start)

    def note(row):
        row['at'] = time.strftime('%Y-%m-%dT%H:%M:%S%z')
        with open(log, 'a', encoding='utf-8') as handle:
            handle.write(json.dumps(row, ensure_ascii=False) + '\n')

    note(dict(phase='stub', stubbed={s: names for s, (_, names) in stubs.items()}, blocked=blocked))
    if blocked:
        return dict(blocked=blocked, results=[])
    saved = Scheduler(run, workers=1).scratch / 'originals'
    saved.mkdir(parents=True, exist_ok=True)

    def fix(shard):
        original, names = stubs[shard]
        path = SHARDS / f'{shard}.lean'
        (saved / f'{shard}.lean').write_text(original, encoding='utf-8')
        agent = Scheduler(f'{run}-{shard}', workers=1, max_tasks=10 ** 6, budget_minutes=10 ** 5, task_minutes=minutes, effort=effort)
        for attempt in range(1, attempts + 1):
            began = time.time()
            prompt = PARALLEL_PROMPT.format(target=target, root=ROOT, path=path.relative_to(ROOT), names='\n'.join(f'- {n}' for n in names),
                                            original=saved / f'{shard}.lean', forge=FORGE, relpath=path.relative_to(PROJECT),
                                            minutes=minutes)
            before = path.read_text(encoding='utf-8')
            code, message, tokens, slow = agent._invoke(prompt, 'repair')
            after = path.read_text(encoding='utf-8')
            problems = check_repair(original, after)
            errors, has_sorry = _check_file(path)
            ok = not problems and not errors and not has_sorry
            note(dict(phase='parallel', shard=shard, attempt=attempt, ok=ok, problems=problems, errors=len(errors),
                      sorry=has_sorry, exit=code, tokens=tokens, seconds=round(time.time() - began),
                      raw=agent.last_raw.get('repair', '')[-800:] if code != 0 else ''))
            if ok:
                return dict(shard=shard, status='repaired', attempts=attempt)
            if problems:
                path.write_text(before, encoding='utf-8')
            if code != 0 and after == before:   # agent 自身出错（多半是网络）：等一会儿再试，不算一次尝试
                time.sleep(90)
                agent._probe()
        return dict(shard=shard, status='stuck')

    with ThreadPoolExecutor(max_workers=workers) as pool:
        results = list(pool.map(fix, sorted(stubs)))
    code, output = lake_build('Mathlib2')   # 验收：按顺序完整编译，确认整个库没有 sorry
    final = dict(built=code == 0, sorry="declaration uses 'sorry'" in output)
    note(dict(phase='final', **final))
    return dict(results=results, final=final)


def rehash(data=DATA):
    """升级后重算所有结构哈希。Mathlib 内部定义的写法一变，同一条命题的哈希就会变；不重算的话，
    评测题保护（reserved）和查重（duplicate）会悄悄失效。重算：评测集、台账、任务文件；辅助引理索引另由 `forge reindex` 重建。"""
    from . import bench
    from .verify import statement_hashes
    report = {}
    for path in sorted(bench.BENCH.glob('*.jsonl')):
        items = bench.load(path.stem)
        hashes = statement_hashes([i['statement'] for i in items], opens=[i.get('opens', '') for i in items],
                                  preambles=[i.get('preamble', '') for i in items], timeout=2400)
        lost = [i['name'] for i, h in zip(items, hashes) if h is None]
        for item, digest in zip(items, hashes):
            if digest:
                item['hash'] = digest
        path.write_text(''.join(json.dumps(i, ensure_ascii=False) + '\n' for i in items), encoding='utf-8')
        report[f'bench/{path.stem}'] = dict(items=len(items), unhashable=lost)
    ledger = data / 'ledger.jsonl'
    entries = [json.loads(line) for line in ledger.read_text(encoding='utf-8').splitlines() if line.strip()]
    targets = [e for e in entries if e.get('kind') != 'definition' and e.get('statement')]
    hashes = statement_hashes([e['statement'] for e in targets], timeout=2400)
    for entry, digest in zip(targets, hashes):
        if digest:
            entry['hash'] = digest
    ledger.write_text(''.join(json.dumps(e, ensure_ascii=False) + '\n' for e in entries), encoding='utf-8')
    report['ledger'] = dict(entries=len(targets), unhashable=[e['name'] for e, h in zip(targets, hashes) if h is None])
    task_files = sorted((data / 'tasks').glob('*/*.json'))
    loaded = [(p, json.loads(p.read_text(encoding='utf-8'))) for p in task_files]
    from .statement import StatementError, split_signature

    def well_formed(statement):
        try:
            split_signature(statement)
            return True
        except StatementError:
            return False
    malformed = [t['name'] for p, t in loaded if t.get('statement') and not well_formed(t['statement'])]
    loaded = [(p, t) for p, t in loaded if t.get('statement') and well_formed(t['statement'])]
    hashes = statement_hashes([t['statement'] for _, t in loaded], timeout=2400)
    from . import tasks as task_store
    for (path, task), digest in zip(loaded, hashes):
        if digest and task.get('hash') != digest:
            task['hash'] = digest
            task_store.save(path.parent.name, task)   # 用项目自己的保存格式，避免无意义的格式改动
    report['tasks'] = dict(files=len(loaded), malformed_skipped=malformed, unhashable=[t['name'] for (_, t), h in zip(loaded, hashes) if h is None][:20])
    return report
