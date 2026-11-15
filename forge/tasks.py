"""任务队列：一个任务一个 JSON 文件，状态就是它所在的目录。

领取用原子的 rename 实现，多个 agent 并行时同一任务只会被一个领到；
放弃时把失败思路写回任务，下一个 agent 能看到，不重复踩坑。
"""
import json
import os
import time

from . import bench, library
from .leanrun import DATA
from .statement import StatementError, check_name, check_statement_text, closed_form
from .verify import HOLE, check_definition, check_sketch, check_submission, triage, validate_statements

TASKS = DATA / 'tasks'
STATES = ('open', 'claimed', 'done')
STALE_SECONDS = 3600


def _dir(state):
    path = TASKS / state
    path.mkdir(parents=True, exist_ok=True)
    return path


def _now():
    return time.strftime('%Y-%m-%dT%H:%M:%S%z')


def load(name):
    for state in STATES:
        path = _dir(state) / f'{name}.json'
        if path.exists():
            return state, json.loads(path.read_text(encoding='utf-8'))
    return None, None


def save(state, task):
    path = _dir(state) / f'{task["name"]}.json'
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(task, ensure_ascii=False, indent=2), encoding='utf-8')
    os.replace(temporary, path)


def all_tasks(state):
    out = []
    for path in sorted(_dir(state).glob('*.json')):
        try:
            out.append(json.loads(path.read_text(encoding='utf-8')))
        except FileNotFoundError:
            continue  # 列目录之后被别的 agent 领走或归还了
    return out


def _known_hashes():
    seen = {}
    for entry in library.entries():
        if entry.get('hash'):
            seen[entry['hash']] = entry['task']
    for state in STATES:
        for task in all_tasks(state):
            if task.get('hash'):
                seen.setdefault(task['hash'], task['name'])
    return seen


def prepare(name, statement):
    """提交的第一步：格式检查与分诊。只读、不改任何状态，所以批量提交时可以多条并行。
    返回 (提前结束时的结果, 分诊报告)；前者为 None 表示可以进入第二步 settle。"""
    try:
        check_name(name)
        check_statement_text(statement)
    except StatementError as exc:
        return dict(name=name, status='invalid', reason=str(exc)), None
    if load(name)[0]:
        return dict(name=name, status='invalid', reason='名称已被占用，换一个'), None
    return None, triage(name, statement)


def propose(name, statement, informal='', origin='conjecture', source='', proposed_by='', original='', prepared=None):
    """提出一个命题：分诊后要么判为已知/重复/无效，要么被自动化直接证掉入库，要么进入队列等 agent。

    prepared：批量提交时由 prepare() 并行算好的结果；这里（登记、查重、入库）必须逐条执行。"""
    early, report = prepared if prepared is not None else prepare(name, statement)
    if early:
        return early
    if load(name)[0]:  # 并行分诊期间名称可能已被同一批里的别的条目占用
        return dict(name=name, status='invalid', reason='名称已被占用，换一个')
    if report.get('timed_out'):
        # 机器忙时类型检查可能超时；这不说明命题有问题，名称也不占用，稍后原样重提即可。
        return dict(name=name, status='busy', reason='类型检查超时（机器繁忙），请稍后用同一名称重新提交')
    if not report['valid']:
        return dict(name=name, status='invalid', reason='命题无法通过 Lean 的类型检查', errors=report.get('errors', []))
    held_out = bench.reserved().get(report['hash'])
    if held_out:
        return dict(name=name, status='reserved', of=held_out, reason='与评测集里的题目命题相同；评测题不能进库，否则成绩失真')
    duplicate = _known_hashes().get(report['hash'])
    if duplicate:
        return dict(name=name, status='duplicate', of=duplicate, reason='与已有任务或库中定理的命题结构相同')
    if report.get('vacuous'):
        # 假设互相矛盾时命题空真成立，证出来也毫无数学内容；不占名称，改好假设后可原名重提。
        return dict(name=name, status='vacuous', tactic=report['vacuous'],
                    reason=f'签名里的假设互相矛盾（`{report["vacuous"]}` 能从假设推出 False），命题是空真的，不入库')
    task = dict(name=name, statement=statement, closed=closed_form(statement), informal=informal, origin=origin,
                source=source, original=original[:6000], proposed_by=proposed_by, hash=report['hash'], type=report['type'], attempts=[],
                created_at=_now())
    if report.get('known'):
        task.update(status='known', known_as=report.get('known_as', ''))
        save('done', task)
        return dict(name=name, status='known', known_as=task['known_as'],
                    reason='Mathlib 或 Mathlib2 里已有，`exact?` 一步即得，不入库')
    if report.get('follows_from'):
        found = report['follows_from']
        task.update(status='known', known_as=f'{found["lemma"]}（{found["tactic"]}）')
        save('done', task)
        return dict(name=name, status='known', known_as=task['known_as'],
                    reason=f'可由库里已有的 `{found["lemma"]}` 一步推出（`{found["tactic"]}`），是换了写法的已有结论，不入库')
    if report.get('counterexample'):
        task['counterexample'] = report['counterexample']
    for tactic in report.get('auto', []):
        body = f'theorem {name} {statement} := by\n  {tactic}\n'
        with library.locked():
            check = check_submission(task, body)
            if check['ok']:
                task['tier'] = 'auto'
                result = library.admit(task, body, check, proved_by='auto:' + tactic)
                if result['ok']:
                    task.update(status='proved', closed_by='auto:' + tactic, finished_at=_now())
                    save('done', task)
                    return dict(name=name, status='auto_proved', tactic=tactic,
                                reason='被自动化直接证出，已入库（tier=auto，价值较低）')
        break
    task['status'] = 'open'
    save('open', task)
    out = dict(name=name, status='open', reason='已进入队列，等待证明或证伪')
    if task.get('counterexample'):
        out.update(refutable=True, counterexample=task['counterexample'], reason='随机测试找到反例，已进入队列，等待形式化证伪')
    return out


def waiting_on(task):
    """父任务最新骨架里还没有结论的子任务。"""
    if not task.get('sketches'):
        return []
    pending = []
    for child in task['sketches'][-1]['children']:
        _, child_task = load(child['task'])
        if not child_task or child_task['status'] in ('open', 'claimed'):
            pending.append(child['task'])
    return pending


def claim(agent, name=None, prefix=None, parity=None):
    """领取一个任务（原子操作）。优先尝试次数少的；超时未归还的领取会被回收。"""
    now = time.time()
    for path in _dir('claimed').glob('*.json'):
        try:
            stale = now - path.stat().st_mtime > STALE_SECONDS
            task = json.loads(path.read_text(encoding='utf-8')) if stale else None
        except FileNotFoundError:
            continue
        if stale:
            task['attempts'].append(dict(agent=task.get('claimed_by', ''), note='领取超时，自动回收', at=_now()))
            task['status'] = 'open'
            save('open', task)
            path.unlink(missing_ok=True)
    candidates = sorted(all_tasks('open'), key=lambda t: (len(t['attempts']), t['created_at'], t['name']))
    if name:
        candidates = [t for t in candidates if t['name'] == name]
    else:
        candidates = [t for t in candidates if not waiting_on(t)]  # 等子任务的父任务先不发出去
    if prefix:
        candidates = [t for t in candidates if t['name'].startswith(prefix)]
    if parity is not None:  # A/B 对比：按名称的 crc32 奇偶把任务确定地分成两组
        import zlib
        candidates = [t for t in candidates if zlib.crc32(t['name'].encode()) % 2 == parity]
    for task in candidates:
        source = _dir('open') / f'{task["name"]}.json'
        target = _dir('claimed') / f'{task["name"]}.json'
        try:
            os.rename(source, target)
        except (FileNotFoundError, PermissionError):
            continue  # 被别的 agent 抢先领走（Windows 上文件被占用时是 PermissionError）
        task.update(status='claimed', claimed_by=agent, claimed_at=_now())
        save('claimed', task)
        return task
    return None


def _held_by_other(state, task, agent):
    """别的 agent 正领着的任务不能被抢交、抢拆；未领取的任务谁都可以直接提交。"""
    if state == 'claimed' and task.get('claimed_by') != agent:
        return dict(ok=False, reason=f'任务正由 {task.get("claimed_by")} 领取；换一个任务，或等它归还')
    return None


def retire(name, agent, note):
    """把无法完成的任务移出队列（命题有误、被更好的表述取代等），保留记录。"""
    state, task = load(name)
    if state not in ('open', 'claimed'):
        return dict(ok=False, reason=f'任务不在队列中（当前：{state}）')
    blocked = _held_by_other(state, task, agent)
    if blocked:
        return blocked
    task.update(status='retired', retired_by=agent, retired_note=note[:2000], finished_at=_now())
    save('done', task)
    (_dir(state) / f'{name}.json').unlink(missing_ok=True)
    return dict(ok=True, reason='已移出队列')


def release(name, agent, note):
    state, task = load(name)
    if state != 'claimed':
        return dict(ok=False, reason=f'任务不在已领取状态（当前：{state}）')
    if task.get('claimed_by') != agent:
        return dict(ok=False, reason=f'任务由 {task.get("claimed_by")} 领取，只有领取者能归还')
    task['attempts'].append(dict(agent=agent, note=note[:2000], at=_now()))
    task['status'] = 'open'
    save('open', task)
    (_dir('claimed') / f'{name}.json').unlink(missing_ok=True)
    return dict(ok=True, reason='已归还队列，失败记录已保存')


def submit(name, body, agent, disproof=False):
    """提交证明或证伪：持锁校验（对着库的最新状态）→ 入库 → 重建。"""
    state, task = load(name)
    if state not in ('claimed', 'open'):
        return dict(ok=False, reason=f'任务不可提交（当前：{state}）')
    blocked = _held_by_other(state, task, agent)
    if blocked:
        return blocked
    try:
        # 校验不持锁、可以并行；入库由组提交合并构建。锁外校验失败时在锁内再校验一次，
        # 排除恰好撞上别的进程正在重建库（读到半新的 .olean）造成的误报。
        check = check_submission(task, body, disproof)
        if not check['ok']:
            with library.locked():
                check = check_submission(task, body, disproof)
            if not check['ok']:
                return check
        held = bench.reserved()
        leaked = [held[h] for h in [check['hash']] + [i['hash'] for i in check.get('helper_info', {}).values()] if h in held]
        if leaked:
            return dict(ok=False, reason=f'提交里有与评测题相同的命题（{", ".join(leaked)}），评测题不能进库')
        result = library.commit(task, body, check, proved_by=agent)
    except StatementError as exc:
        return dict(ok=False, reason=str(exc))
    if not result['ok']:
        return result
    task.update(status=check['kind'], closed_by=agent, finished_at=_now())
    save('done', task)
    (_dir(state) / f'{name}.json').unlink(missing_ok=True)
    out = dict(ok=True, kind=check['kind'], reason='已入库', entry=result['entry']['name'],
               library_deps=check['library_deps'])
    helpers = check.get('helper_info', {})
    if helpers:
        # 辅助引理若与库里已有的声明命题相同，提醒一下：下次直接引用已有的，不必重证。
        repeated = library.same_statement({info['hash'] for info in helpers.values()}, exclude=set(helpers))
        if repeated:
            out['duplicate_helpers'] = [dict(yours=n, existing=['Mathlib2.' + e for e in repeated[info['hash']]])
                                        for n, info in helpers.items() if info['hash'] in repeated]
            out['reason'] += '。注意：有辅助引理与库里已有的声明命题相同，以后可直接引用已有的'
        with library.locked():
            library.record_helpers(result['entry']['name'], helpers)
    return out


def sketch(name, body, agent):
    """登记证明骨架：每个空洞成为一个子任务（origin=decomposition），父任务挂起等待。"""
    state, task = load(name)
    if state not in ('claimed', 'open'):
        return dict(ok=False, reason=f'任务不可拆解（当前：{state}）')
    blocked = _held_by_other(state, task, agent)
    if blocked:
        return blocked
    if task.get('sketches') and task['sketches'][-1]['agent'] != agent and waiting_on(task):
        return dict(ok=False, reason=f'{task["sketches"][-1]["agent"]} 已经拆解了这个任务，子任务还在进行；'
                                     '去证那些子任务（./forge.sh queue 可见），不要另起一份骨架')
    try:
        check = check_sketch(task, body)
    except StatementError as exc:
        return dict(ok=False, reason=str(exc))
    if not check['ok']:
        return check
    # 先整体检查每个空洞的目标都能作为独立命题重新解析，全部通过才登记任何子任务：
    # 否则前几个子任务已入队、后一个失败，会留下孤儿并堵死重试。
    problems = validate_statements([hole['statement'] for hole in check['holes']])
    for index, (hole, problem) in enumerate(zip(check['holes'], problems), 1):
        if problem:
            return dict(ok=False, reason=f'第 {index} 个空洞的目标无法作为独立命题重新解析，本次没有登记任何子任务',
                        hole=hole['statement'], error=problem,
                        hint='把这一步写得更显式（给绑定变量写上类型、避免依赖隐式宇宙或匿名假设）后重试')
    by_hash = _known_hashes()
    round_number = len(task.get('sketches', [])) + 1
    children = []
    for index, hole in enumerate(check['holes'], 1):
        existing = by_hash.get(hole['hash'])
        if existing:  # 同一命题已经是任务或库中定理（例如上一份骨架留下的），直接复用
            child, result = existing, dict(status='duplicate')
            _, existing_task = load(existing)
            result.update(known_as=(existing_task or {}).get('known_as', ''))
        else:
            child = f'{name}_s{round_number}h{index}'
            suffix = 0
            while load(child)[0] or any(e['name'] == child for e in library.entries()):
                suffix += 1
                child = f'{name}_s{round_number}h{index}v{suffix}'
            result = propose(child, ': ' + hole['statement'], informal=f'{name} 的证明骨架中第 {index} 个空洞',
                             origin='decomposition', source=name, proposed_by=agent)
            if result['status'] == 'duplicate':
                child = result['of']
            elif result['status'] in ('invalid', 'busy'):
                return dict(ok=False, reason=f'第 {index} 个空洞登记失败（{result["status"]}）', detail=result,
                            note='此前的空洞已登记为子任务；修正后重新 sketch 时，相同的命题会被自动复用')
        children.append(dict(hole=index, task=child, status=result['status'], statement=hole['statement'],
                             args=hole.get('args', []), known_as=result.get('known_as', ''),
                             counterexample=result.get('counterexample', '')))
    # 新骨架取代旧骨架：旧骨架里没被复用、也还没人领的子任务不再需要，自动撤掉，免得别人白做。
    kept = {child['task'] for child in children}
    superseded = []
    for previous in task.get('sketches', []):
        for old in previous['children']:
            old_state, old_task = load(old['task'])
            if old['task'] not in kept and old_state == 'open' and old_task.get('origin') == 'decomposition':
                old_task.update(status='retired', retired_by=agent, finished_at=_now(),
                                retired_note=f'{name} 重新拆解，这个子任务属于被取代的旧骨架')
                save('done', old_task)
                (_dir('open') / f'{old["task"]}.json').unlink(missing_ok=True)
                superseded.append(old['task'])
    task.setdefault('sketches', []).append(dict(agent=agent, body=body, children=children, at=_now()))
    task['status'] = 'open'
    save('open', task)
    if state == 'claimed':
        (_dir('claimed') / f'{name}.json').unlink(missing_ok=True)
    refuted = [c for c in children if c['counterexample']]
    return dict(ok=True, children=children, superseded=superseded,
                reason='骨架已登记，子任务已入队；全部证出后运行 assemble 拼回父命题' +
                       ('。注意：有空洞被随机测试找到反例，这个拆法多半不成立' if refuted else ''))


def assemble(name, agent):
    """子任务都有结论后，把骨架里的空洞换成对子定理的引用，校验并入库。"""
    state, task = load(name)
    if state not in ('claimed', 'open') or not task.get('sketches'):
        return dict(ok=False, reason='任务没有可拼装的骨架')
    last = task['sketches'][-1]
    fills = []
    pending = []
    for child in last['children']:
        child_state, child_task = load(child['task'])
        status = child_task['status'] if child_task else 'missing'
        if status == 'proved':
            # 子定理是“对骨架里当时的全部局部变量全称量化”的闭命题：按拆解时记下的顺序把它们喂回去。
            applied = f'exact @Mathlib2.{child["task"]} {" ".join(child["args"])} | ' if child.get('args') else ''
            fills.append(f'(first | {applied}exact Mathlib2.{child["task"]} | apply Mathlib2.{child["task"]} <;> assumption | '
                         f'simpa using Mathlib2.{child["task"]})')
        elif status == 'known' and child_task.get('known_as'):
            known = child_task['known_as']
            fills.append(f'(first | exact ({known}) | apply ({known}) <;> assumption | exact?)')
        else:
            pending.append(dict(task=child['task'], status=status))
    dead = [p for p in pending if p['status'] in ('disproved', 'retired', 'missing')]
    if dead:
        return dict(ok=False, dead=dead,
                    reason='这份骨架作废了：有子引理被证伪或撤销，说明拆法本身不成立。修正对应步骤后重新 sketch；'
                           '新骨架里可以直接引用已证出的子定理（Mathlib2.<名字>），只把需要改的步骤留成 sorry')
    if pending:
        return dict(ok=False, reason='还有子任务没有证出', pending=pending)
    # 每个 sorry 处都把全部子定理挨个试一遍：这样 sorry 与目标不必一一对应（`<;> sorry` 一个 sorry 管多个目标也能拼）。
    options = ' | '.join(fill[len('(first | '):-1] for fill in fills)
    combined = f'(first | {options})'
    body = HOLE.sub(lambda _: combined, last['body'])
    result = submit(name, body, agent)
    if not result.get('ok'):
        result['hint'] = '自动拼装失败：请手写最终证明，直接引用各子定理（Mathlib2.<子任务名>）后 submit'
        result['children'] = [c['task'] for c in last['children']]
    return result


def define(name, body, agent, informal='', source='', original=''):
    """引入一条新定义。定义不是被“证明”的，内核只保证它良构；它是否忠实于原文要靠 review。"""
    try:
        check_name(name)
    except StatementError as exc:
        return dict(ok=False, reason=str(exc))
    if load(name)[0] or any(e['name'] == name for e in library.entries()):
        return dict(ok=False, reason='名称已被占用')
    try:
        with library.locked():
            check = check_definition(name, body)
            if not check['ok']:
                return check
            task = dict(name=name, statement=body.strip(), informal=informal, origin='definition', source=source,
                        original=original[:6000], hash=None, tier='definition', attempts=[], created_at=_now())
            result = library.admit(task, body, check, proved_by=agent)
    except StatementError as exc:
        return dict(ok=False, reason=str(exc))
    if not result['ok']:
        return result
    task.update(status='defined', closed_by=agent, finished_at=_now(), type=check['type'])
    save('done', task)
    return dict(ok=True, kind='definition', entry=name, type=check['type'],
                reason=f'已入库，可在命题和证明里写作 `{name}`（全名 Mathlib2.{name}）。请安排独立 review 核对它是否忠实于原文。')


def queue():
    """队列一览：每个未完成任务的状态、谁在做、尝试过几次、在等哪些子任务。"""
    rows = []
    for state in ('open', 'claimed'):
        for task in all_tasks(state):
            rows.append(dict(name=task['name'], state=state, origin=task.get('origin', ''),
                             claimed_by=task.get('claimed_by', '') if state == 'claimed' else '',
                             attempts=len(task['attempts']), refutable=bool(task.get('counterexample')),
                             waiting_on=waiting_on(task), statement=task['statement'][:160]))
    return rows
