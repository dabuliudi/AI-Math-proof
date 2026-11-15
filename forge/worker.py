"""自主 worker：不依赖 Claude Code，直接用 Anthropic SDK 的 tool runner 驱动同一套 forge 操作。

  python -m forge.worker prove --agent w1 --tasks 5
  python -m forge.worker conjecture --agent c1 --area "初等数论" --count 10

凭据按 SDK 的默认顺序解析（ANTHROPIC_API_KEY，或 `ant auth login` 的配置）。
并行就是多开几个进程：任务领取是原子的，入库有锁。
"""
import argparse
import json

import anthropic
from anthropic import beta_tool

from . import insight, tasks
from .statement import StatementError
from .verify import check_submission

MODEL = 'claude-opus-5-5'
AGENT = 'worker'

SYSTEM = """你是定理铸造厂里的一个 agent。Lean 内核是唯一裁判：只有 submit 返回 ok 才算证完。

提交的 Lean 文本已处在 `namespace Mathlib2` 内，Mathlib 和 Mathlib2 全部可用。只能写顶格的 `open` 行和
顶格的 `theorem`/`lemma` 声明（证明内容缩进）。主定理必须是最后一个声明，名称就是任务名；辅助引理命名为
`<任务名>_aux…`。证伪时证明 `theorem <任务名>_disproof : ¬ (<闭形式>)` 并把 disproof 设为 true。
不允许 sorry（骨架除外）、axiom、def、instance、notation、macro、set_option、native_decide、run_tac。

工作方式：
- 先判断命题真假。任务带 counterexample 时直接做证伪。
- 写证明 → check → 读错误 → 改。错误信息是给你迭代用的。
- 一个任务校验约 8 次仍不通：看得出结构就把卡住的步骤留成 sorry 用 sketch 提交（空洞会成为独立子任务）；
  没有思路就 release，写清楚试过的路线和卡点。
- 任务里的 attempts 是前人的失败记录，先读。
- 不要为了通过而改命题。"""


def _dump(value):
    return json.dumps(value, ensure_ascii=False)


@beta_tool
def next_task() -> str:
    """领取一个待证任务。返回任务的名称、命题签名、闭形式、反例提示和前人的失败记录；队列为空时 task 为 null。"""
    return _dump(dict(task=tasks.claim(AGENT)))


@beta_tool
def check(task_name: str, lean_source: str, disproof: bool = False) -> str:
    """只校验一份证明或证伪，不入库。失败时返回前几条 Lean 错误（行号相对于 lean_source）。

    Args:
        task_name: 任务名。
        lean_source: 提交的 Lean 文本（open 行与 theorem/lemma 声明）。
        disproof: 证伪时为 true，此时主定理须为 `<任务名>_disproof : ¬ (闭形式)`。
    """
    _, task = tasks.load(task_name)
    if not task:
        return _dump(dict(ok=False, reason='没有这个任务'))
    try:
        return _dump(check_submission(task, lean_source, disproof))
    except StatementError as exc:
        return _dump(dict(ok=False, reason=str(exc)))


@beta_tool
def submit(task_name: str, lean_source: str, disproof: bool = False) -> str:
    """校验并入库。只有返回 ok 为 true 才算完成任务。

    Args:
        task_name: 任务名。
        lean_source: 提交的 Lean 文本。
        disproof: 证伪时为 true。
    """
    return _dump(tasks.submit(task_name, lean_source, AGENT, disproof))


@beta_tool
def sketch(task_name: str, lean_source: str) -> str:
    """提交带 sorry 空洞的证明骨架。骨架须能编译且命题匹配；每个空洞处的目标会成为独立子任务。

    Args:
        task_name: 任务名。
        lean_source: 带若干 `sorry` 的主定理证明骨架。
    """
    return _dump(tasks.sketch(task_name, lean_source, AGENT))


@beta_tool
def assemble(task_name: str) -> str:
    """父任务的子任务都证完后，把骨架里的空洞换成对子定理的引用并入库。

    Args:
        task_name: 父任务名。
    """
    return _dump(tasks.assemble(task_name, AGENT))


@beta_tool
def release(task_name: str, note: str) -> str:
    """做不出来时归还任务。

    Args:
        task_name: 任务名。
        note: 试过哪些路线、具体卡在哪一步，供下一个 agent 参考。
    """
    return _dump(tasks.release(task_name, AGENT, note))


@beta_tool
def search(query: str) -> str:
    """检索 Mathlib2 里已有的定理（可在证明中以 `Mathlib2.<名字>` 引用）。

    Args:
        query: 关键词或符号，例如 "dvd le pos" 或 "∑ range ^ 2"。
    """
    return _dump(insight.search(query))


@beta_tool
def propose(name: str, statement: str, informal: str = '') -> str:
    """提出一个新命题。结果为 known / duplicate / invalid / auto_proved / open，其中 open 才是好猜想。

    Args:
        name: 小写下划线的全局唯一名称。
        statement: Lean 签名 `<binders> : <conclusion>`，binder 写全，不带 `:=`。
        informal: 一句话的非形式化描述。
    """
    return _dump(tasks.propose(name, statement, informal, 'conjecture', '', AGENT))


def run(prompt, tools, max_iterations):
    client = anthropic.Anthropic()
    runner = client.beta.messages.tool_runner(
        model=MODEL, max_tokens=32000, system=SYSTEM, tools=tools, max_iterations=max_iterations,
        output_config={'effort': 'high'}, cache_control={'type': 'ephemeral'},
        betas=['server-side-fallback-2026-07-01'], fallbacks='default',
        messages=[{'role': 'user', 'content': prompt}])
    final = None
    for message in runner:
        final = message
        for block in message.content:
            if block.type == 'text' and block.text.strip():
                print(block.text.strip(), flush=True)
    if final is not None and final.stop_reason == 'refusal':
        print('模型拒绝了本次请求：', final.stop_details, flush=True)
    return final


def main():
    global AGENT
    parser = argparse.ArgumentParser(description='forge 自主 worker（Anthropic SDK）')
    sub = parser.add_subparsers(dest='mode', required=True)
    p = sub.add_parser('prove')
    p.add_argument('--agent', default='worker'); p.add_argument('--tasks', type=int, default=3)
    p = sub.add_parser('conjecture')
    p.add_argument('--agent', default='conjecturer'); p.add_argument('--area', required=True)
    p.add_argument('--count', type=int, default=10)
    args = parser.parse_args()
    AGENT = args.agent
    if args.mode == 'prove':
        run(f'依次处理至多 {args.tasks} 个任务：next_task 领取，证明或证伪，submit；做不出来就 sketch 或 release。'
            '队列空了就停。最后用几句话总结每个任务的结果。',
            [next_task, check, submit, sketch, assemble, release, search], max_iterations=40 * args.tasks)
    else:
        run(f'在「{args.area}」方向提出约 {args.count} 个新命题，目标是 propose 返回 open：命题为真、自然、'
            'Mathlib 里没有现成的、常用自动化一步关不掉。根据每次返回的状态调整难度，invalid 时按 Lean 错误修正后换名重提。'
            '不要尝试证明。最后列出每个命题的最终状态。',
            [propose, search], max_iterations=6 * args.count)


if __name__ == '__main__':
    main()
