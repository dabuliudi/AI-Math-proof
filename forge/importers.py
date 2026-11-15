"""导入外部 Lean 数据集（miniF2F、Lean Workbook 等）时共用的转换。

外部数据集常用较旧的 Mathlib 写出，最常见的不兼容是大算子写法：旧版 `∑ x in s, f`，新版 `∑ x ∈ s, f`。
新写法的主体优先级更高，`∑ x ∈ s, a + b` 会被读成 `(∑ x ∈ s, a) + b`，所以转换时必须给主体加括号，
否则题意会被悄悄改变（miniF2F 导入时就因此坏了 6 题）。
"""
import re

OPEN, CLOSE = '([{', ')]}'


def convert_big_operators(text):
    """把 `∑ x in s, body` / `∏ x : T in s, body` 改成 `∑ x ∈ s, (body)` / `∏ x ∈ (s : Finset T), (body)`。

    旧写法的主体一直延伸到所在括号层的结尾（或整个字符串结尾），这里按同样的范围加括号。返回 (新文本, 改了几处)。
    """
    out, i, changed = '', 0, 0
    while True:
        found = re.search(r'[∑∏]', text[i:])
        if not found:
            return out + text[i:], changed
        j = i + found.start()
        depth, k = 0, j + 1
        while k < len(text) and not (text[k] == ',' and depth == 0):
            depth += text[k] in OPEN
            depth -= text[k] in CLOSE
            k += 1
        binder = text[j + 1:k]
        match = re.match(r'\s*(\S+?)\s*(?::\s*(.+?))?\s+in\s+(.+)$', binder, re.S)
        if not match or k >= len(text):
            out += text[i:k]
            i = k
            continue
        var, typ, domain = match.group(1), match.group(2), match.group(3).strip()
        new_binder = f' {var} ∈ ({domain} : Finset {typ})' if typ else f' {var} ∈ {domain}'
        depth, end = 0, k + 1
        while end < len(text):
            if text[end] in OPEN:
                depth += 1
            elif text[end] in CLOSE:
                if depth == 0:
                    break
                depth -= 1
            end += 1
        body, inner = convert_big_operators(text[k + 1:end])
        out += text[i:j + 1] + new_binder + ', (' + body.strip() + ')'
        i = end
        changed += 1 + inner


def theorem_signature(source):
    """从 `theorem 名字 <签名> := by sorry` 这样的一条声明里取出 (名字, 签名)。签名形如 `<binders> : <conclusion>`。
    不是这种形状（多条声明、带定义、没有 sorry）的返回 None。"""
    code = re.sub(r'/-.*?-/', '', source, flags=re.S)
    code = re.sub(r'--[^\n]*', '', code).strip()
    match = re.fullmatch(r'(?:theorem|lemma)\s+(\S+)\s*(.*?):=\s*(?:by\s+)?sorry', code, re.S)
    if not match or re.search(r'\b(theorem|lemma|def|abbrev|instance)\b', match.group(2)):
        return None
    return match.group(1), ' '.join(match.group(2).split())


def putnam_problem(source):
    """把一个 PutnamBench 的 Lean 文件转成评测题：{name, statement, opens?, preamble?}；转不了的返回 None。

    答案题的 `abbrev X_solution : T := sorry` 后面紧跟的注释是官方答案；按排行榜“填好答案”（with solution）
    赛道的做法，把官方答案填进去作为前置定义。题目自带的其他辅助定义（def/abbrev）也放进前置定义。
    """
    lines = source.split('\n')
    opens = [line.strip()[5:] for line in lines if line.startswith('open ')]
    if len(opens) > 1:
        return None
    body = '\n'.join(line for line in lines if not line.startswith(('import ', 'open ')))
    body = re.sub(r'/--.*?-/', '', body, flags=re.S)          # 题目的文档注释（自然语言原题）
    at = re.search(r'^theorem\s', body, re.M)
    if not at:
        return None
    head, theorem = body[:at.start()], body[at.start():]

    def fill(match):
        answer = ' '.join(c.strip()[2:].strip() for c in match.group(2).strip().split('\n'))
        return f'{match.group(1)} {answer}\n' if answer else match.group(0)

    head = re.sub(r'^((?:noncomputable\s+)?abbrev\s+\S+_solution\s*:.*?:=)\s*sorry\s*\n((?:\s*--[^\n]*\n)+)',
                  fill, head, flags=re.M | re.S)
    head = re.sub(r'/-.*?-/', '', head, flags=re.S).strip()
    if re.search(r'\bsorry\b', head) or re.search(r'--', head):
        return None                                           # 答案没能填上，或者前置部分有无法处理的注释
    parsed = theorem_signature(theorem)
    if not parsed:
        return None
    name, signature = parsed
    item = dict(name=name, statement=signature)
    if opens:
        item['opens'] = opens[0]
    if head:
        item['preamble'] = head
    return item
