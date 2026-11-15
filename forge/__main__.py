"""forge 命令行：给人和 agent 用的同一套入口，输出都是 JSON。

  python -m forge propose --name N --statement "(a b : ℕ) (h : a ∣ b) : ..." [--informal ...]
  python -m forge propose --file conjectures.jsonl
  python -m forge next --agent A            领取一个任务
  python -m forge check NAME proof.lean     只校验，不入库
  python -m forge submit NAME proof.lean --agent A [--disproof]
  python -m forge sketch NAME skeleton.lean  带 sorry 的骨架 → 空洞成为子任务
  python -m forge assemble NAME             子任务证完后拼回父命题
  python -m forge release NAME --agent A --note "试过什么、卡在哪"
  python -m forge search "dvd le"           检索 Mathlib2
  python -m forge lookup "succ mul choose"  按名称片段查 Mathlib/Mathlib2 的定理
  python -m forge find "自然语言或命题"      按内容检索（Mathlib2 本地 + LeanSearch）
  python -m forge pattern "_ ∣ _ ^ 2"       按类型模式检索（Loogle）
  python -m forge paper paper.pdf           提取论文里的命题清单
  python -m forge review NAME --agent A --verdict faithful|unfaithful|unsure --note …
  python -m forge status | dag [NAME] | report
"""
import argparse
import json
import sys
from pathlib import Path

from . import insight, library, tasks
from .statement import StatementError
from .verify import check_submission

GUIDE = ('提交文件只写 `open` 行和 `theorem`/`lemma` 声明（已在 `namespace Mathlib2` 内，Mathlib 和 Mathlib2 全部可用）。'
         '证明：最后一个声明是 `theorem {name} {statement} := …`。'
         '证伪：最后一个声明是 `theorem {name}_disproof : ¬ ({closed}) := …`，提交时加 --disproof。'
         '辅助引理命名为 `{name}_aux…`。先用 check 校验，通过后再 submit；做不出来就 release 并写明试过什么。')


def emit(value):
    print(json.dumps(value, ensure_ascii=False, indent=2))


def main(argv=None):
    parser = argparse.ArgumentParser(prog='forge', description='定理铸造厂：Lean 内核把关的任务队列与 Mathlib2 库')
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('propose', help='提出命题（猜想、论文命题或人提的问题）')
    p.add_argument('--name'); p.add_argument('--statement'); p.add_argument('--informal', default='')
    p.add_argument('--origin', default='conjecture', choices=['conjecture', 'paper', 'human', 'decomposition'])
    p.add_argument('--source', default=''); p.add_argument('--agent', default='')
    p.add_argument('--file', type=Path, help='JSONL，每行 {name, statement, informal?, origin?, source?}')
    p = sub.add_parser('define', help='引入一条新定义（只允许一条 def）')
    p.add_argument('name'); p.add_argument('file', type=Path); p.add_argument('--agent', default='anonymous')
    p.add_argument('--informal', default=''); p.add_argument('--source', default=''); p.add_argument('--original', default='')
    p = sub.add_parser('next', help='领取一个待证任务')
    p.add_argument('--agent', required=True); p.add_argument('--name'); p.add_argument('--prefix', help='只领名称以此开头的任务')
    p = sub.add_parser('queue', help='列出未完成的任务'); p.add_argument('--brief', action='store_true', help='每个任务一行：状态 名称 领取者')
    p = sub.add_parser('show', help='查看任务'); p.add_argument('name')
    p = sub.add_parser('source', help='打印库里某条定理的完整 Lean 证明'); p.add_argument('name')
    for command in ('check', 'submit'):
        p = sub.add_parser(command, help='校验提交' if command == 'check' else '提交并入库')
        p.add_argument('name'); p.add_argument('file', type=Path); p.add_argument('--disproof', action='store_true')
        p.add_argument('--agent', default='anonymous')
    p = sub.add_parser('sketch', help='登记带 sorry 空洞的证明骨架，空洞自动成为子任务')
    p.add_argument('name'); p.add_argument('file', type=Path); p.add_argument('--agent', default='anonymous')
    p = sub.add_parser('assemble', help='子任务证完后拼回父命题'); p.add_argument('name'); p.add_argument('--agent', default='anonymous')
    p = sub.add_parser('release', help='归还任务并记录失败思路')
    p.add_argument('name'); p.add_argument('--agent', required=True); p.add_argument('--note', required=True)
    p = sub.add_parser('retire', help='把命题有误或已被取代的任务移出队列')
    p.add_argument('name'); p.add_argument('--agent', required=True); p.add_argument('--note', required=True)
    p = sub.add_parser('search', help='检索 Mathlib2'); p.add_argument('query'); p.add_argument('--limit', type=int, default=10)
    p = sub.add_parser('paper', help='从论文提取待形式化的命题清单'); p.add_argument('file', type=Path)
    p = sub.add_parser('review', help='独立复核：Lean 命题与原文是否一致')
    p.add_argument('name'); p.add_argument('--agent', required=True)
    p.add_argument('--verdict', required=True, choices=['faithful', 'unfaithful', 'unsure']); p.add_argument('--note', required=True)
    p = sub.add_parser('lookup', help='按名称片段查 Mathlib/Mathlib2 里的定理名和类型'); p.add_argument('query')
    p = sub.add_parser('find', help='按内容检索：Mathlib2（本地）+ Mathlib（LeanSearch 语义检索）'); p.add_argument('query')
    p = sub.add_parser('pattern', help='按类型模式检索 Mathlib（Loogle），例如 "_ ∣ _ ^ 2 + _ ^ 2"'); p.add_argument('pattern')
    p = sub.add_parser('site', help='生成给数学家用的挑选页面（单文件 HTML）'); p.add_argument('--out', type=Path, default=Path('forge/data/picker.html'))
    sub.add_parser('reindex', help='重建辅助引理索引（按命题内容），供检索与查重')
    p = sub.add_parser('bench-import', help='导入固定评测集（JSONL，每行 {name, statement}）；评测题从此不能进库')
    p.add_argument('set'); p.add_argument('file', type=Path)
    p.add_argument('--opens', default='', help='题目依赖的记号设置，例如 "BigOperators Real Nat Topology Rat"')
    p = sub.add_parser('bench-check', help='对一道评测题校验证明：只判对错，不入库，记入某个轮次')
    p.add_argument('set'); p.add_argument('problem'); p.add_argument('file', type=Path)
    p.add_argument('--run', required=True, help='轮次名，例如 2026-11-16-a'); p.add_argument('--agent', default='anonymous')
    p = sub.add_parser('bench-score', help='评测集各轮次的成绩'); p.add_argument('set')
    p = sub.add_parser('run', help='调度外部 agent（默认本机 Codex）无人值守地清队列或跑评测')
    p.add_argument('--run', required=True, help='轮次名，日志写到 forge/data/runs/<轮次>.jsonl')
    p.add_argument('--prefix', help='队列模式：只领名称以此开头的任务')
    p.add_argument('--bench', help='评测模式：评测集名称'); p.add_argument('--limit', type=int, help='评测模式：最多做几题')
    p.add_argument('--resume', action='store_true', help='评测模式：在同一轮次里接着跑，已认真做过的题跳过，agent 出错作废的重跑')
    p.add_argument('--all', action='store_true', help='评测模式：所有题都重做（默认跳过以前已解出的），用于在同一设置下测基线')
    p.add_argument('--workers', type=int, default=2); p.add_argument('--max-tasks', type=int, default=10)
    p.add_argument('--budget-minutes', type=int, default=60); p.add_argument('--task-minutes', type=int, default=20)
    p.add_argument('--max-failures', type=int, default=4, help='连续这么多次没有进展就整体停下')
    p.add_argument('--agent-cmd', help='自定义 agent 命令（提示词从 stdin 传入）；默认 codex exec')
    p.add_argument('--model', default='gpt-6.1-sol', help='Codex 模型，默认 gpt-6.1-sol')
    p.add_argument('--effort', default='xhigh', help='Codex 推理强度：low/medium/high/xhigh，默认 xhigh')
    p.add_argument('--dry-run', action='store_true', help='不真的调用 agent，只走一遍流程')
    p = sub.add_parser('run-report', help='读回某一轮调度的记账'); p.add_argument('run')
    p = sub.add_parser('audit', help='独立审计：对着已编译的库重新核对每条定理的公理与命题')
    p.add_argument('--replay', action='store_true', help='另外把整个库放进只含 Mathlib 的环境让内核重放一遍（约 14 GB 内存）')
    sub.add_parser('status', help='队列与库的概况')
    p = sub.add_parser('dag', help='内核依赖图'); p.add_argument('name', nargs='?')
    p = sub.add_parser('report', help='供数学家挑选的排序清单'); p.add_argument('--limit', type=int, default=30)
    p = sub.add_parser('catalog', help='生成给人读的库目录 Markdown'); p.add_argument('--out', type=Path, default=Path('forge/data/CATALOG.md'))
    args = parser.parse_args(argv)
    if getattr(args, 'file', None) and not args.file.is_file():
        emit(dict(ok=False, reason=f'找不到文件：{args.file}')); return 1

    if args.command == 'propose':
        if args.file:
            rows = [json.loads(line) for line in args.file.read_text(encoding='utf-8').splitlines() if line.strip()]
        elif args.name and args.statement:
            rows = [dict(name=args.name, statement=args.statement, informal=args.informal, origin=args.origin, source=args.source)]
        else:
            parser.error('propose 需要 --file，或同时给 --name 和 --statement')
        results = []
        for index, r in enumerate(rows, 1):
            results.append(tasks.propose(r['name'], r['statement'], r.get('informal', ''), r.get('origin', args.origin),
                                         r.get('source', args.source), args.agent, r.get('original', '')))
            if args.file:  # 批量时逐条报进度（stderr），最终 JSON 仍在 stdout
                print(f'[{index}/{len(rows)}] {r["name"]}: {results[-1]["status"]}', file=sys.stderr, flush=True)
        emit(results if args.file else results[0])
    elif args.command == 'define':
        result = tasks.define(args.name, args.file.read_text(encoding='utf-8'), args.agent, args.informal, args.source, args.original)
        emit(result); return 0 if result.get('ok') else 1
    elif args.command == 'next':
        task = tasks.claim(args.agent, args.name, args.prefix)
        if not task:
            state, existing = tasks.load(args.name) if args.name else (None, None)
            if state == 'claimed':
                reason = f'任务正由 {existing.get("claimed_by")} 领取'
            elif state == 'done':
                reason = f'任务已结束（{existing.get("status")}）'
            elif args.name and not state:
                reason = '没有这个任务'
            else:
                reason = '队列里没有符合条件的待领取任务'
            emit(dict(task=None, reason=reason)); return 2 if args.name else 0  # 指名领取失败算失败，别让脚本以为领到了
        emit(dict(task=task, how_to=GUIDE.format(name=task['name'], statement=task['statement'], closed=task['closed'])))
    elif args.command == 'queue':
        rows = tasks.queue()
        if args.brief:
            for row in rows:
                waiting = f' 等待子任务×{len(row["waiting_on"])}' if row['waiting_on'] else ''
                print(f'{row["state"]:7} {row["name"]} {row["claimed_by"]}{waiting}'.rstrip())
        else:
            emit(rows)
    elif args.command == 'source':
        found = library.source(args.name)
        if not found:
            emit(dict(ok=False, reason='库里没有这条定理')); return 1
        print(f'-- {found["entry"]}（{found["shard"]}）')
        print(found['lean'])
    elif args.command == 'show':
        state, task = tasks.load(args.name)
        emit(dict(state=state, task=task))
    elif args.command in ('check', 'submit'):
        body = args.file.read_text(encoding='utf-8')
        if args.command == 'submit':
            result = tasks.submit(args.name, body, args.agent, args.disproof)
        else:
            state, task = tasks.load(args.name)
            if not task:
                emit(dict(ok=False, reason='没有这个任务')); return 1
            try:
                result = check_submission(task, body, args.disproof)
            except StatementError as exc:
                result = dict(ok=False, reason=str(exc))
        emit(result)
        return 0 if result.get('ok') else 1
    elif args.command == 'sketch':
        result = tasks.sketch(args.name, args.file.read_text(encoding='utf-8'), args.agent)
        emit(result); return 0 if result.get('ok') else 1
    elif args.command == 'assemble':
        result = tasks.assemble(args.name, args.agent)
        emit(result); return 0 if result.get('ok') else 1
    elif args.command == 'release':
        emit(tasks.release(args.name, args.agent, args.note))
    elif args.command == 'paper':
        from . import paper
        emit(paper.extract(args.file))
    elif args.command == 'review':
        from . import paper
        if not tasks.load(args.name)[1]:
            emit(dict(ok=False, reason='没有这个任务')); return 1
        emit(paper.review(args.name, args.agent, args.verdict, args.note))
    elif args.command == 'lookup':
        from .verify import lookup
        emit(lookup(args.query))
    elif args.command == 'retire':
        emit(tasks.retire(args.name, args.agent, args.note))
    elif args.command == 'find':
        from . import remote
        local = [f'{r["name"]} : {r["type"]}' for r in insight.search(args.query, 4)]
        emit(dict(mathlib=remote.leansearch(args.query), mathlib2=local))  # Mathlib 的语义结果放前面，本地结果只给紧凑的几条
    elif args.command == 'pattern':
        from . import remote
        emit(remote.loogle(args.pattern))
    elif args.command == 'site':
        from . import site
        args.out.write_text(site.build(), encoding='utf-8')
        emit(dict(ok=True, file=str(args.out)))
    elif args.command == 'reindex':
        from .verify import describe
        wanted = {h: e['name'] for e in library.entries() for h in e.get('helpers', [])}
        infos = describe(sorted(wanted))
        with library.locked():
            for owner in sorted(set(wanted.values())):
                library.record_helpers(owner, {h: infos[h] for h, o in wanted.items() if o == owner and h in infos})
        emit(dict(ok=True, helpers=len(wanted), indexed=len(infos)))
    elif args.command == 'bench-import':
        from . import bench
        emit(bench.import_set(args.set, args.file, args.opens))
    elif args.command == 'bench-check':
        from . import bench
        result = bench.check(args.set, args.problem, args.file.read_text(encoding='utf-8'), args.run, args.agent)
        emit(result); return 0 if result.get('solved') else 1
    elif args.command == 'bench-score':
        from . import bench
        emit(bench.score(args.set))
    elif args.command == 'run':
        from .scheduler import Scheduler
        runner = Scheduler(args.run, workers=args.workers, max_tasks=args.max_tasks, budget_minutes=args.budget_minutes,
                           task_minutes=args.task_minutes, max_failures=args.max_failures, agent_cmd=args.agent_cmd,
                           model=args.model, effort=args.effort, dry_run=args.dry_run)
        emit(runner.run_bench(args.bench, args.limit, only_unsolved=not args.all, resume=args.resume) if args.bench else runner.run_queue(args.prefix))
    elif args.command == 'run-report':
        from .scheduler import report
        emit(report(args.run))
    elif args.command == 'audit':
        from .leanrun import lake_build
        from .verify import audit
        code, output = lake_build('Mathlib2')
        if code != 0 or "declaration uses 'sorry'" in output:
            emit(dict(ok=False, reason='库构建失败或含 sorry', build_tail=output[-1500:])); return 1
        result = audit(library.entries())
        if args.replay:
            from .leanrun import replay
            result['replay'] = replay()
            result['ok'] = result['ok'] and result['replay']['ok']
        emit(result); return 0 if result['ok'] else 1
    elif args.command == 'search':
        emit(insight.search(args.query, args.limit))
    elif args.command == 'status':
        entries = library.entries()
        done = tasks.all_tasks('done')
        emit(dict(library=dict(theorems=sum(e['kind'] != 'definition' for e in entries), definitions=sum(e['kind'] == 'definition' for e in entries), proved=sum(e['kind'] == 'proved' for e in entries),
                               disproved=sum(e['kind'] == 'disproved' for e in entries),
                               tier_agent=sum(e['tier'] == 'agent' for e in entries),
                               tier_auto=sum(e['tier'] == 'auto' for e in entries),
                               max_dag_depth=insight.dag()['max_depth']),
                  queue=dict(open=len(tasks.all_tasks('open')), claimed=len(tasks.all_tasks('claimed')),
                             known_in_mathlib=sum(t['status'] == 'known' for t in done))))
    elif args.command == 'dag':
        emit(insight.dag(args.name))
    elif args.command == 'report':
        emit(insight.report(args.limit))
    elif args.command == 'catalog':
        args.out.write_text(insight.catalog(), encoding='utf-8')
        emit(dict(ok=True, file=str(args.out), theorems=len(library.entries())))
    return 0


if __name__ == '__main__':
    sys.exit(main())
