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
