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
        original = path.read_text(encoding='utf-8')
        fixed = False
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
            if problems:  # 违规的修改一律撤销，从原文件重来
                path.write_text(original, encoding='utf-8')
                code, output = lake_build(f'Mathlib2.Shard.{shard}')
        if not fixed:
            path.write_text(original, encoding='utf-8')
            results.append(dict(shard=shard, status='stuck'))
            break
    return results
