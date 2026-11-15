"""准入校验与分诊：都只相信内核侧命令的带 nonce 输出。"""
import re
import uuid

from .leanrun import ALLOWED_AXIOMS, run_source
from .statement import analyse_definition, analyse_submission, closed_form, is_disproof, split_signature

HEADER = 'import Mathlib\nimport Mathlib2\nimport Forge\n'
HEARTBEATS = 400000

# 分诊阶梯：先问库里是否已有（exact?），再试一遍常用自动化。能被自动化关掉的命题不值得花 agent 的预算。
LADDER = ['exact?', 'rfl', 'decide', 'simp', 'norm_num', 'omega', 'linarith', 'nlinarith', 'positivity', 'ring',
          'tauto', 'aesop', 'grind', 'simp_all', 'intros; omega', 'intros; linarith', 'intros; simp_all',
          'intros; aesop']


def _brief(messages, offset, limit=3, width=1200):
    """给 agent 看的错误：最多几条、带相对行号、截断，避免把整屏输出塞进上下文。"""
    out = []
    for m in messages[:limit]:
        text = m['data'].strip()
        if len(text) > width:
            text = text[:width] + f'\n…（截断，原文 {len(m["data"])} 字符）'
        out.append(dict(line=max(m['line'] - offset, 0), column=m['column'], message=text))
    return out


def check_submission(task, body, disproof=False, timeout=300):
    """校验一份提交。返回 dict(ok, reason, errors, infos...)；不修改任何状态。"""
    name = task['name']
    disproof = disproof or is_disproof(body, name)
    names = analyse_submission(body, name, disproof)
    nonce = uuid.uuid4().hex
    # 评测集的题目可能依赖记号设置（例如 miniF2F 的 `open Real Nat …`）；只影响解析，不影响内核里的命题。
    opens = task.get('opens', '')
    prefix = HEADER + f'set_option maxHeartbeats {HEARTBEATS}\nnamespace Mathlib2\nsection\n' + (f'open {opens}\n' if opens else '')
    offset = prefix.count('\n')
    main = names[-1]
    tail = '\nend\nend Mathlib2\n' + ''.join(f'#forge_info "{nonce}" Mathlib2.{n}\n' for n in names)
    tail += f'open Mathlib2 {opens} in\n#forge_match "{nonce}" Mathlib2.{main} "{"disproved" if disproof else "proved"}" ({closed_form(task["statement"])})\n'
    result = run_source(prefix + body.rstrip('\n') + tail, timeout=timeout, nonce=nonce)
    out = dict(ok=False, kind='disproved' if disproof else 'proved', names=names, elapsed=round(result.elapsed, 1))
    if result.timed_out:
        return dict(out, reason=f'编译超时（{timeout} 秒）。把证明拆成更小的辅助引理，或换更直接的策略。')
    errors = result.errors()
    if errors:
        return dict(out, reason='Lean 报错', errors=_brief(errors, offset), error_count=len(errors))
    infos = {i['name']: i for i in result.tagged('FORGE_INFO')}
    for n in names:
        info = infos.get('Mathlib2.' + n)
        if not info:
            return dict(out, reason=f'没有拿到 `{n}` 的内核信息')
        if info['kind'] != 'theorem':
            return dict(out, reason=f'`{n}` 不是定理')
        bad = sorted(set(info['axioms']) - ALLOWED_AXIOMS)
        if bad:
            return dict(out, reason=f'`{n}` 依赖了不允许的公理：{", ".join(bad)}（出现 sorryAx 说明证明没写完）')
    match = [m for m in result.tagged('FORGE_MATCH') if m['name'] == 'Mathlib2.' + main]
    if not match or not match[0]['ok']:
        want = f'¬ ({closed_form(task["statement"])})' if disproof else task['statement']
        return dict(out, reason=f'主定理 `{main}` 的命题与任务要求不一致。要求：{want}')
    info = infos['Mathlib2.' + main]
    deps = set()
    for n in names:
        deps.update(infos['Mathlib2.' + n]['deps'])
    local = {'Mathlib2.' + n for n in names}
    return dict(out, ok=True, reason='通过：命题匹配，公理合规', type=info['type'], hash=info['hash'],
                helper_info={n: dict(type=infos['Mathlib2.' + n]['type'], hash=infos['Mathlib2.' + n]['hash']) for n in names[:-1]},
                axioms=sorted({a for n in names for a in infos['Mathlib2.' + n]['axioms']}),
                library_deps=sorted(d[len('Mathlib2.'):] for d in deps if d.startswith('Mathlib2.') and d not in local),
                external_deps=len([d for d in deps if not d.startswith('Mathlib2.')]))


EVALUATING = {'decide', 'rfl', 'plausible', 'plausible_rat'}  # 会真的去算值，遇到天文数字可能跑不完


def _ladder_run(decl, labelled, timeout):
    """跑一组互相独立的 `example … := by tactic`，返回 (哪些没报错, 各块消息, 是否超时)。"""
    lines = HEADER.rstrip('\n').split('\n') + ['namespace ForgeTriage', 'open Mathlib2', 'set_option maxHeartbeats 100000',
                                                 'set_option pp.deepTerms true', 'set_option pp.maxSteps 100000']
    blocks = []
    for label, text, tactic in labelled:
        start = len(lines) + 1
        lines.extend(f'example {text} := by\n  {tactic}'.split('\n'))
        blocks.append((label, start, len(lines)))
    lines.append('end ForgeTriage')
    result = run_source('\n'.join(lines) + '\n', timeout=timeout)
    per_block = {label: [m for m in result.messages if start <= m['line'] <= end] for label, start, end in blocks}
    if result.timed_out:
        return set(), per_block, True
    passed = {label for label, messages in per_block.items() if not any(m['severity'] == 'error' for m in messages)}
    return passed, per_block, False


# 空真检查：只看签名里的假设（冒号前的绑定）。结论里的蕴含不拆，以免把 `¬P`、`∀ x < n, …` 这类正常结论误判为空真。
VACUITY = ['simp_all', 'omega', 'linarith', 'nlinarith', 'tauto', 'contradiction', 'aesop']
# “一步推论”检查：拿词法检索最相近的几条库内定理，看能否只用一条就直接推出新命题。
RELATED = 5


# 同一个量的常见不同写法（子类型的 card、Finset.filter 的 card、Set.toFinset、Nat.card），先统一再套用。
NORMALIZE = 'Fintype.card_subtype, Fintype.card_coe, Finset.card_univ, Set.toFinset_card, Nat.card_eq_fintype_card'


def _corollary_tactics(lemma):
    normalized = f'have h := @{lemma}; (try simp only [{NORMALIZE}] at h ⊢); '
    return [f'simp_all [{lemma}]', normalized + 'first | exact h | apply h <;> assumption', normalized + 'simp_all',
            f'solve_by_elim [{lemma}]', f'grind [{lemma}]']


def _relations(binders, decl, statement):
    """空真与一步推论的探针块：(标签, 声明, 策略)。标签前缀 vac: / lib:<序号>:。"""
    from .insight import search  # 延迟导入：insight → library → verify 会成环
    blocks = [(f'vac:{t}', f'{binders} : False', t) for t in VACUITY] if binders.strip() else []
    related = [hit['name'] for hit in search(statement, limit=RELATED)]
    for i, lemma in enumerate(related):
        blocks += [(f'lib:{i}:{t}', decl, t) for t in _corollary_tactics(lemma)]
    return blocks, related


def triage(name, statement, timeout=240):
    """分诊：命题是否合法、结构哈希、库里是否已有、能否被自动化关掉、随机测试有没有反例，
    假设是否自相矛盾（空真），以及能否由库里某一条定理一步推出（换了写法的重复）。

    四次独立的 Lean 运行并行进行：命题本身（决定是否合法）、符号类自动化、会实际求值的检查、空真与一步推论探针。
    后三者超时只意味着“没得到结论”，不会把一个合法命题误判成无效。
    """
    from concurrent.futures import ThreadPoolExecutor
    binders, conclusion = split_signature(statement)
    decl = f'{binders} : {conclusion}'
    nonce = uuid.uuid4().hex
    core = HEADER + f'namespace ForgeTriage\nopen Mathlib2\ntheorem {name} {decl} := by\n  sorry\nend ForgeTriage\n#forge_info "{nonce}" ForgeTriage.{name}\n'
    symbolic = [(t, decl, t) for t in LADDER if t not in EVALUATING]
    evaluating = [(t, decl, t) for t in LADDER if t in EVALUATING] + [('plausible', decl, 'plausible')]
    if 'ℝ' in decl:
        # plausible 不会对实数取样；把 ℝ 换成 ℚ 再测一次，只作为“可能为假”的提示，不算证伪。
        evaluating.append(('plausible_rat', decl.replace('ℝ', 'ℚ'), 'plausible'))
    relations, related = _relations(binders, decl, statement)
    with ThreadPoolExecutor(max_workers=4) as pool:
        core_future = pool.submit(run_source, core, 120, nonce)
        symbolic_future = pool.submit(_ladder_run, decl, symbolic, timeout)
        evaluating_future = pool.submit(_ladder_run, decl, evaluating, 60)
        relations_future = pool.submit(_ladder_run, decl, relations, 120) if relations else None
        result = core_future.result()
        passed_symbolic, messages_symbolic, slow_symbolic = symbolic_future.result()
        passed_evaluating, messages_evaluating, slow_evaluating = evaluating_future.result()
        passed_relations, _, slow_relations = relations_future.result() if relations_future else (set(), {}, False)
    info = result.tagged('FORGE_INFO')
    # 命题一旦报错，Lean 仍会留下一个类型里带 sorry 的常量，这样的“命题”谁也证不了，必须在这里拦住。
    out = dict(valid=bool(info) and not result.errors(), elapsed=round(result.elapsed, 1), timed_out=result.timed_out)
    if not out['valid']:
        out['errors'] = _brief(result.errors(), HEADER.count('\n') + 1)
        if result.timed_out:
            out['errors'] = [dict(line=0, column=0, message='命题本身的类型检查超时（120 秒）')]
        return out
    out.update(type=info[0]['type'], hash=info[0]['hash'], inconclusive=[
        label for label, slow in (('symbolic', slow_symbolic), ('evaluating', slow_evaluating),
                                  ('relations', slow_relations)) if slow])
    vacuous = [label[4:] for label, _, _ in relations if label.startswith('vac:') and label in passed_relations]
    if vacuous:
        out['vacuous'] = vacuous[0]
    for label, _, tactic in relations:
        if label.startswith('lib:') and label in passed_relations:
            out['follows_from'] = dict(lemma=related[int(label.split(':')[1])], tactic=tactic)
            break
    for label in ('plausible', 'plausible_rat'):
        for m in messages_evaluating.get(label, []):
            if m['severity'] == 'error' and 'Found a counter-example' in m['data'] and 'counterexample' not in out:
                prefix = '（把 ℝ 换成 ℚ 后的随机测试，仅供参考）\n' if label == 'plausible_rat' else ''
                out['counterexample'] = prefix + m['data'].strip()[:1500]
    passed = passed_symbolic | (passed_evaluating - {'plausible', 'plausible_rat'})
    closers = [t for t in LADDER if t in passed]
    if 'exact?' in closers:
        for m in messages_symbolic.get('exact?', []):
            found = re.search(r'Try this:\s*(?:\[apply\]\s*)?exact\s+(.+)', m['data'], re.S)
            if found:
                out['known_as'] = ' '.join(found.group(1).split())[:500]
                break
        out['known'] = True
        closers.remove('exact?')
    out['auto'] = closers
    return out


HOLE = re.compile(r"(?<![\w.'])sorry(?![\w'])")


def check_sketch(task, body, timeout=300):
    """校验证明骨架：把每个 `sorry` 换成 `forge_hole`，由内核给出各空洞处的闭命题。

    骨架本身必须能编译、命题必须匹配——也就是说，只要这些空洞都成立，父命题就成立。
    """
    from .statement import strip_comments
    names = analyse_submission(body, task['name'], allow_holes=True)
    holes = len(HOLE.findall(strip_comments(body)))
    if not holes:
        return dict(ok=False, reason='骨架里没有 `sorry` 空洞；完整证明请直接 submit')
    nonce = uuid.uuid4().hex
    marked = HOLE.sub(f'forge_hole "{nonce}"', body)
    prefix = HEADER + f'set_option maxHeartbeats {HEARTBEATS}\nnamespace Mathlib2\nsection\n'
    offset = prefix.count('\n')
    tail = f'\nend\nend Mathlib2\nopen Mathlib2 in\n#forge_match "{nonce}" Mathlib2.{names[-1]} "proved" ({closed_form(task["statement"])})\n'
    result = run_source(prefix + marked.rstrip('\n') + tail, timeout=timeout, nonce=nonce)
    if result.timed_out:
        return dict(ok=False, reason=f'骨架编译超时（{timeout} 秒）')
    errors = result.errors()
    if errors:
        return dict(ok=False, reason='骨架除空洞外还有 Lean 错误', errors=_brief(errors, offset), error_count=len(errors))
    match = result.tagged('FORGE_MATCH')
    if not match or not match[0]['ok']:
        return dict(ok=False, reason='骨架主定理的命题与任务要求不一致')
    found = result.tagged('FORGE_HOLE')
    # 一个 `sorry` 可能对应多个目标（例如 `refine ⟨?_, ?_⟩ <;> sorry`），所以提取到的目标数可以多于 sorry 的个数。
    if len(found) < holes:
        return dict(ok=False, reason=f'只提取到 {len(found)}/{holes} 个空洞的目标（空洞须写在策略块里）')
    for index, hole in enumerate(found, 1):
        if hole.get('roundtrip') is False:
            return dict(ok=False, hole=hole['statement'],
                        reason=f'第 {index} 个空洞的目标打印成文本后再解析，得到的不是原来的命题（类型标注或强制转换丢了），本次没有登记任何子任务',
                        hint='把这一步写得更显式：给字面量绑定一个带类型的变量（∀ f : Polynomial K, f = … → …），'
                             '把“函数的乘积作用于 x”写成逐个应用（τ (ρ x) 而不是 (τ * ρ) x），避免依赖 open 进来的记号')
    # 打印出来的宇宙参数名（Type u_1）在独立命题里没有绑定，换成 Type* / Sort* 才能重新解析。
    def portable(text):
        return re.sub(r'\b(Type|Sort) u_\d+\b', r'\1*', text)
    return dict(ok=True, holes=[dict(statement=portable(h['statement']), hash=h['hash'], args=h.get('args', [])) for h in found])


def lookup(query, timeout=120):
    """按名称片段在 Mathlib + Mathlib2 的全部定理里查找，返回准确名称和类型。"""
    fragments = ' '.join(re.findall(r"[A-Za-z0-9_.'₀-₉]+", query))
    if not fragments:
        return dict(ok=False, reason='给出名称片段，例如 "succ mul choose"')
    nonce = uuid.uuid4().hex
    result = run_source(HEADER + f'#forge_find "{nonce}" "{fragments}"\n', timeout=timeout, nonce=nonce)
    found = result.tagged('FORGE_FIND')
    if not found:
        return dict(ok=False, reason='查找失败', errors=_brief(result.errors(), 0))
    return dict(ok=True, total=found[0]['total'], results=[f'{r["name"]} : {r["type"]}' for r in found[0]['results']],
                note='按名称片段匹配（不分大小写，全部片段都要出现）；结果按名称长度排序，最多 25 条')


def audit(entries, timeout=900):
    """独立审计：不看台账里记的结论，对着已编译的库重新核对每条定理的种类、公理和命题。"""
    nonce = uuid.uuid4().hex
    lines = [HEADER.rstrip('\n'), f'set_option maxHeartbeats {HEARTBEATS}']
    for entry in entries:
        mode = 'disproved' if entry['kind'] == 'disproved' else 'proved'
        lines.append(f'#forge_info "{nonce}" Mathlib2.{entry["name"]}')
        if entry['kind'] != 'definition':
            lines.append(f'open Mathlib2 in\n#forge_match "{nonce}" Mathlib2.{entry["name"]} "{mode}" ({closed_form(entry["statement"])})')
    result = run_source('\n'.join(lines) + '\n', timeout=timeout, nonce=nonce)
    infos = {i['name']: i for i in result.tagged('FORGE_INFO')}
    matches = {m['name']: m for m in result.tagged('FORGE_MATCH')}
    problems = []
    for entry in entries:
        full = 'Mathlib2.' + entry['name']
        info, match = infos.get(full), matches.get(full)
        if not info:
            problems.append(dict(name=entry['name'], problem='库里找不到这个常量'))
        elif info['kind'] != ('def' if entry['kind'] == 'definition' else 'theorem'):
            problems.append(dict(name=entry['name'], problem='常量种类与台账不符'))
        elif set(info['axioms']) - ALLOWED_AXIOMS:
            problems.append(dict(name=entry['name'], problem='依赖不允许的公理', axioms=info['axioms']))
        elif entry['kind'] != 'definition' and (not match or not match['ok']):
            problems.append(dict(name=entry['name'], problem='类型与台账记录的命题不一致'))
    return dict(ok=not problems and not result.timed_out, checked=len(entries), passed=len(entries) - len(problems),
                problems=problems, timed_out=result.timed_out, elapsed=round(result.elapsed, 1),
                axioms_used=sorted({a for i in infos.values() for a in i['axioms']}))


def check_definition(name, body, timeout=120):
    """校验一条新定义：能编译、确实是 def、不引入新公理、短名不遮蔽任何已有的根级概念。"""
    analyse_definition(body, name)
    nonce = uuid.uuid4().hex
    prefix = HEADER + f'set_option maxHeartbeats {HEARTBEATS}\nnamespace Mathlib2\nsection\n'
    source = prefix + body.rstrip('\n') + f'\nend\nend Mathlib2\n#forge_info "{nonce}" Mathlib2.{name}\n'
    result = run_source(source, timeout=timeout, nonce=nonce)
    if result.timed_out:
        return dict(ok=False, reason='编译超时')
    if result.errors():
        return dict(ok=False, reason='Lean 报错', errors=_brief(result.errors(), prefix.count('\n')))
    info = result.tagged('FORGE_INFO')
    if not info or info[0]['kind'] != 'def':
        return dict(ok=False, reason='没有得到一个 def')
    if info[0].get('rootClash'):
        return dict(ok=False, reason=f'`{name}` 与已有的根级名称同名，会造成歧义；换一个带领域前缀的名字')
    bad = sorted(set(info[0]['axioms']) - ALLOWED_AXIOMS)
    if bad:
        return dict(ok=False, reason=f'定义依赖了不允许的公理：{", ".join(bad)}')
    return dict(ok=True, kind='definition', names=[name], type=info[0]['type'], hash=info[0]['hash'],
                axioms=sorted(info[0]['axioms']),
                library_deps=sorted(d[len('Mathlib2.'):] for d in info[0]['deps'] if d.startswith('Mathlib2.')),
                external_deps=len([d for d in info[0]['deps'] if not d.startswith('Mathlib2.')]))


def validate_statements(statements, timeout=180):
    """一次 Lean 运行里检查若干闭命题能否各自作为独立命题通过类型检查。返回与输入等长的错误信息列表（None 表示通过）。"""
    lines = HEADER.rstrip('\n').split('\n') + ['namespace ForgeValidate', 'open Mathlib2']
    spans = []
    for index, statement in enumerate(statements):
        start = len(lines) + 1
        lines.extend(f'theorem v{index} : {statement} := by\n  sorry'.split('\n'))
        spans.append((start, len(lines)))
    lines.append('end ForgeValidate')
    result = run_source('\n'.join(lines) + '\n', timeout=timeout)
    if result.timed_out:
        return ['类型检查超时'] * len(statements)
    out = []
    for start, end in spans:
        errors = [m['data'].strip()[:600] for m in result.errors() if start <= m['line'] <= end]
        out.append(errors[0] if errors else None)
    return out


def statement_hashes(statements, opens='', timeout=900):
    """一次 Lean 运行里求若干命题（`<绑定> : <结论>` 形式）的结构哈希，与分诊用的是同一个哈希。无效的为 None。

    `opens` 只影响记号解析；哈希取自内核里的命题，所以与不带 open 写出的同一命题一致。
    """
    nonce = uuid.uuid4().hex
    lines = HEADER.rstrip('\n').split('\n') + ['namespace ForgeBench', f'open Mathlib2 {opens}'.rstrip()]
    spans = []
    for index, statement in enumerate(statements):
        binders, conclusion = split_signature(statement)
        start = len(lines) + 1
        lines.extend(f'theorem b{index} {binders} : {conclusion} := by\n  sorry'.split('\n'))
        spans.append((start, len(lines)))
    lines.append('end ForgeBench')
    lines += [f'#forge_info "{nonce}" ForgeBench.b{index}' for index in range(len(statements))]
    result = run_source('\n'.join(lines) + '\n', timeout=timeout, nonce=nonce)
    infos = {i['name']: i['hash'] for i in result.tagged('FORGE_INFO')}
    out = []
    for index, (start, end) in enumerate(spans):
        broken = any(start <= m['line'] <= end for m in result.errors())
        out.append(None if broken else infos.get(f'ForgeBench.b{index}'))
    return out


def describe(names, timeout=600):
    """取回库里若干声明的类型与结构哈希（给辅助引理建索引用）。"""
    nonce = uuid.uuid4().hex
    source = HEADER + ''.join(f'#forge_info "{nonce}" Mathlib2.{name}\n' for name in names)
    result = run_source(source, timeout=timeout, nonce=nonce)
    return {i['name'][len('Mathlib2.'):]: dict(type=i['type'], hash=i['hash']) for i in result.tagged('FORGE_INFO')}
