"""改进循环：自动提出 harness 改动，在固定评测上和当前最好的配置比，变好才采纳。

一轮：
1. 提出一个候选：要么换一个配置（推理强度、提示词版本），要么让 agent 读上一轮的成绩与失败原因，
   改写评测提示词（存成 forge/data/improve/prompts/<名字>.txt，占位符缺失或不认识就丢弃）。
2. 用候选在开发集上跑一轮评测（调度器 + 内核校验，成绩不采信 agent 自述）。
3. 和当前最好的配置比：解出更多，或者解出一样多而 token 少 10% 以上，才算更好。
4. 更好的候选再到保留集上跑一次，解出数不比当前最好的少，才正式采纳（防止只是碰巧适合开发集那几道题）。
5. 每一轮记一行到 forge/data/improve/history.jsonl；token 总预算花完就停。

做法来自 Anthropic 的评测与 harness 设计文章：固定评测、开发集与保留集分开、只采纳在评测上确有改进的改动，
以及“harness 里每个组件都是对模型能力的假设，要定期用评测重新检验”。
"""
import json
import random
import time

from . import bench
from .leanrun import DATA, ROOT
from .scheduler import PROMPT_DIR, Scheduler, bench_prompt, check_prompt

STATE = DATA / 'improve' / 'state.json'
HISTORY = DATA / 'improve' / 'history.jsonl'
EFFORTS = ('low', 'medium', 'high', 'xhigh')

PROPOSE_PROMPT = '''You are improving the prompt that a proving agent receives for each Lean 4 benchmark problem in the
project at {root}. The current prompt template is saved at {current}. It is a Python format string: keep every
placeholder it uses ({fields}) and do not add new ones.

Results of the current prompt on the development set (problem, solved?, tokens, seconds, checker's reason):
{results}

Write an improved prompt template to {target}. Aim for: more problems solved first, then fewer tokens and less time.
Ideas worth trying: tell the agent how to check cheaply before writing a long proof, how to look up lemma names,
what to do when stuck, and to keep its own context short. Keep every rule about what is not allowed (sorry, axiom,
native_decide, editing files outside the scratch directory). Do not tell the agent anything about specific benchmark
problems or their solutions. Keep the template under 3000 characters.
Do not edit any other file. End with one line: RESULT: written.
'''


def _state_path(set_name):
    # 每个评测集各有一份状态：换评测集时从头测基线，不会拿别的评测集的“当前最好”来比
    return STATE if set_name is None else STATE.with_name(f'state-{set_name}.json')


def _load_state(set_name=None):
    path = _state_path(set_name)
    if path.exists():
        return json.loads(path.read_text(encoding='utf-8'))
    return dict(best=None, iteration=0, tokens_spent=0)


def _save_state(state):
    path = _state_path(state.get('set'))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding='utf-8')


def from_run(run, problems):
    """用一轮已经跑完的评测当基线（同一配置不必重跑）：只取这组题的记录。"""
    from .scheduler import RUNS
    per = {}
    for line in (RUNS / f'{run}.jsonl').read_text(encoding='utf-8').splitlines():
        row = json.loads(line)
        if row['task'] not in problems:
            continue
        item = per.setdefault(row['task'], dict(solved=False, tokens=0, seconds=0, reason=''))
        item['solved'] = item['solved'] or row['outcome'] == 'solved'
        item['tokens'] += row.get('tokens') or 0
        item['seconds'] += row['seconds']
        item['reason'] = row.get('reason', '')
    missing = set(problems) - set(per)
    if missing:
        raise ValueError(f'轮次 {run} 里没有这些题，不能当基线：{sorted(missing)}')
    return dict(run=run, solved=sum(i['solved'] for i in per.values()), problems=len(problems),
                tokens=sum(i['tokens'] for i in per.values()), per=per)


def _note(row):
    HISTORY.parent.mkdir(parents=True, exist_ok=True)
    row['at'] = time.strftime('%Y-%m-%dT%H:%M:%S%z')
    with open(HISTORY, 'a', encoding='utf-8') as handle:
        handle.write(json.dumps(row, ensure_ascii=False) + '\n')


def split(set_name, dev_size, holdout_size, seed):
    """把评测集按固定种子分成开发集和保留集，两者不重叠。"""
    names = sorted(i['name'] for i in bench.load(set_name))
    random.Random(seed).shuffle(names)
    return sorted(names[:dev_size]), sorted(names[dev_size:dev_size + holdout_size])


def evaluate(run, set_name, problems, config, workers, minutes, dry_run=False):
    """用一个配置跑一组题，返回成绩：解出数、token、每题明细。"""
    runner = Scheduler(run, workers=workers, max_tasks=len(problems), budget_minutes=24 * 60, task_minutes=minutes,
                       max_failures=max(6, len(problems)), effort=config['effort'], prompt=config['prompt'], dry_run=dry_run)
    runner.run_bench(set_name, only_unsolved=False, problems=problems)
    per = {}
    for row in runner.records:
        item = per.setdefault(row['task'], dict(solved=False, tokens=0, seconds=0, reason=''))
        item['solved'] = item['solved'] or row['outcome'] == 'solved'
        item['tokens'] += row.get('tokens') or 0
        item['seconds'] += row['seconds']
        item['reason'] = row.get('reason', '')
    # 每道题都认真做过（agent 正常退出或交了证明）才算完整；agent 不可用、服务中断时成绩不能拿来比较
    attempted = {r['task'] for r in runner.records if r['exit'] == 0 or r['outcome'] == 'solved' or r['timed_out']}
    return dict(run=run, solved=sum(i['solved'] for i in per.values()), problems=len(problems),
                tokens=sum(i['tokens'] for i in per.values()), per=per,
                complete=set(problems) <= attempted, stop_reason=runner.stop_reason)


def better(candidate, best, token_margin=0.9):
    """解出更多，或者解出一样多而 token 少 10% 以上。"""
    if candidate['solved'] != best['solved']:
        return candidate['solved'] > best['solved']
    return candidate['tokens'] < token_margin * best['tokens']


def propose_prompt(base_prompt, base_score, iteration, run, set_name=''):
    """让 agent 读当前提示词和开发集成绩，写一版新提示词；不合格就返回 None。"""
    import string
    name = f'{set_name}-auto{iteration:03d}' if set_name else f'auto{iteration:03d}'
    PROMPT_DIR.mkdir(parents=True, exist_ok=True)
    current = PROMPT_DIR / f'_current_{name}.txt'
    current.write_text(bench_prompt(base_prompt), encoding='utf-8')
    target = PROMPT_DIR / f'{name}.txt'
    fields = sorted({f for _, f, _, _ in string.Formatter().parse(current.read_text(encoding='utf-8')) if f})
    lines = [f'- {p}: {"solved" if r["solved"] else "UNSOLVED"}, {r["tokens"]} tokens, {r["seconds"]} s, {r["reason"][:80]}'
             for p, r in sorted(base_score['per'].items())]
    prompt = PROPOSE_PROMPT.format(root=ROOT, current=current, fields=', '.join('{' + f + '}' for f in fields),
                                   results='\n'.join(lines), target=target)
    writer = Scheduler(f'{run}-writer', workers=1, task_minutes=15, effort='high')
    writer._invoke(prompt, 'writer')
    current.unlink(missing_ok=True)
    if not target.exists():
        return None, ['agent 没有写出提示词文件']
    problems = check_prompt(target.read_text(encoding='utf-8'))
    if problems:
        target.rename(target.with_suffix('.rejected.txt'))
        return None, problems
    return name, []


def run_loop(set_name, iterations=4, dev_size=16, holdout_size=16, seed=2026, workers=6, minutes=20,
             token_budget=6_000_000, start=None, dry_run=False, baseline_run=None):
    """跑若干轮改进。第一次运行先用 start（默认 v2 + xhigh）测出基线；给了 baseline_run 就直接用那一轮的记录。"""
    state = _load_state(set_name)
    dev, holdout = split(set_name, dev_size, holdout_size, seed)
    if state['best'] is None:
        config = start or dict(prompt='v2', effort='xhigh')
        if baseline_run:
            score, hold = from_run(baseline_run, dev), from_run(baseline_run, holdout)
        else:
            score = evaluate(f'improve-{set_name}-base-dev', set_name, dev, config, workers, minutes, dry_run)
            hold = evaluate(f'improve-{set_name}-base-holdout', set_name, holdout, config, workers, minutes, dry_run)
        state.update(best=dict(config=config, dev=score, holdout=hold), set=set_name, dev=dev, holdout=holdout, baseline_run=baseline_run,
                     tokens_spent=state['tokens_spent'] + score['tokens'] + hold['tokens'])
        _note(dict(event='baseline', set=set_name, from_run=baseline_run, config=config, dev_solved=score['solved'], dev_tokens=score['tokens'],
                   holdout_solved=hold['solved'], holdout_tokens=hold['tokens']))
        _save_state(state)
    for _ in range(iterations):
        if state['tokens_spent'] >= token_budget:
            _note(dict(event='stop', reason=f'token 预算用完（{state["tokens_spent"]}）'))
            break
        state['iteration'] += 1
        n = state['iteration']
        best = state['best']
        if n % 2 == 1 and not dry_run:   # 奇数轮：让 agent 改写提示词
            name, problems = propose_prompt(best['config']['prompt'], best['dev'], n, f'improve-{set_name}-{n:03d}', set_name)
            if not name:
                _note(dict(event='candidate_rejected', set=set_name, iteration=n, kind='prompt', problems=problems))
                _save_state(state)
                continue
            config = dict(best['config'], prompt=name)
        else:            # 偶数轮：换一个推理强度
            others = [e for e in EFFORTS if e != best['config']['effort']]
            config = dict(best["config"], effort=others[(n // 2 - 1) % len(others)])  # 从最便宜的档位试起
        score = evaluate(f'improve-{set_name}-{n:03d}-dev', set_name, state['dev'], config, workers, minutes, dry_run)
        state['tokens_spent'] += score['tokens']
        if not score.get('complete', True):
            # 不完整的成绩（服务中断、额度用完）不能当作“候选更差”；停下，下次从这一轮重来
            state['iteration'] -= 1
            _note(dict(event='aborted', set=set_name, iteration=n, config=config, reason=score.get('stop_reason') or '有题没有做完'))
            _save_state(state)
            break
        row = dict(event='candidate', set=set_name, iteration=n, config=config, dev_solved=score['solved'], dev_tokens=score['tokens'],
                   best_dev_solved=best['dev']['solved'], best_dev_tokens=best['dev']['tokens'])
        if better(score, best['dev']):
            hold = evaluate(f'improve-{set_name}-{n:03d}-holdout', set_name, state['holdout'], config, workers, minutes, dry_run)
            state['tokens_spent'] += hold['tokens']
            if not hold.get('complete', True):
                state['iteration'] -= 1
                _note(dict(event='aborted', set=set_name, iteration=n, config=config, reason=hold.get('stop_reason') or '保留集有题没有做完'))
                _save_state(state)
                break
            row.update(holdout_solved=hold['solved'], holdout_tokens=hold['tokens'],
                       best_holdout_solved=best['holdout']['solved'])
            if hold['solved'] >= best['holdout']['solved']:
                state['best'] = dict(config=config, dev=score, holdout=hold)
                row['decision'] = 'adopted'
            else:
                row['decision'] = 'rejected_on_holdout'
        else:
            row['decision'] = 'rejected_on_dev'
        _note(row)
        _save_state(state)
    return dict(best=state['best']['config'], best_dev=dict(solved=state['best']['dev']['solved'], tokens=state['best']['dev']['tokens']),
                iterations=state['iteration'], tokens_spent=state['tokens_spent'])
