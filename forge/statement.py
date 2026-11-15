"""命题与提交文本的解析和静态检查。

任务的命题写成 Lean 签名：`<binders> : <conclusion>`，例如
`(a b : ℕ) (h : a ∣ b) (hb : 0 < b) : a ≤ b`。
静态检查只是纵深防御；真正的保证来自内核侧的公理与命题匹配检查。
"""
import re

NAME = re.compile(r'[a-z][A-Za-z0-9_]{2,79}')
OPEN = '([{⦃⟨'
CLOSE = ')]}⦄⟩'

# 提交里禁止出现的词：新公理、逃逸到元程序、改变记号或实例含义、改环境选项。
FORBIDDEN = ['axiom', 'sorry', 'admit', 'unsafe', 'partial', 'opaque', 'constant', 'instance', 'def', 'abbrev',
             'structure', 'inductive', 'class', 'macro', 'macro_rules', 'syntax', 'notation', 'infix', 'infixl',
             'infixr', 'prefix', 'postfix', 'elab', 'elab_rules', 'attribute', 'local', 'set_option', 'import',
             'namespace', 'section', 'end', 'universe', 'variable', 'initialize', 'run_cmd', 'run_tac', 'run_elab',
             'run_meta', 'by_elab', 'mutual', 'deriving', 'extern', 'implemented_by', 'native_decide', 'export',
             'include', 'omit', 'private', 'protected', 'noncomputable', 'unseal', 'csimp', 'reduceBool',
             'ofReduceBool', 'trustCompiler', 'IO', 'declare_syntax_cat', 'register_option']


class StatementError(ValueError):
    pass


def strip_comments(text):
    """去掉注释和字符串字面量，保留换行，便于按行定位。"""
    out = []
    i = 0
    depth = 0
    while i < len(text):
        two = text[i:i + 2]
        if depth:
            if two == '/-':
                depth += 1; i += 2
            elif two == '-/':
                depth -= 1; i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif two == '/-':
            depth = 1; i += 2
        elif two == '--':
            while i < len(text) and text[i] != '\n':
                i += 1
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
            out.append('""')
        else:
            out.append(text[i]); i += 1
    return ''.join(out)


def split_signature(signature):
    """按第一个顶层冒号拆成 (binders, conclusion)。"""
    text = signature.strip()
    if ':=' in strip_comments(text):
        raise StatementError('命题里不能带 `:=`；只写签名（binders : conclusion）')
    depth = 0
    for i, ch in enumerate(text):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif ch == ':' and depth == 0:
            binders, conclusion = text[:i].strip(), text[i + 1:].strip()
            if not conclusion:
                break
            return binders, conclusion
    raise StatementError('命题必须是 `<binders> : <conclusion>` 的形式（没有 binder 时写 `: <conclusion>`）')


def closed_form(signature):
    binders, conclusion = split_signature(signature)
    return f'∀ {binders}, {conclusion}' if binders else conclusion


def check_name(name):
    if not NAME.fullmatch(name):
        raise StatementError('名称须为小写字母开头的标识符（字母、数字、下划线，3–80 字符，不带点）')
    return name


def check_statement_text(signature):
    clean = strip_comments(signature)
    for word in FORBIDDEN:
        if re.search(r"(?<![\w.'])" + re.escape(word) + r"(?![\w'])", clean):
            raise StatementError(f'命题里出现了禁止的词：{word}')
    if len(signature) > 4000:
        raise StatementError('命题过长（上限 4000 字符）')
    split_signature(signature)


def analyse_submission(body, task_name, disproof=False, allow_holes=False):
    """静态检查提交文本，返回其中声明的定理名列表（最后一个必须是主定理）。"""
    if len(body) > 200000:
        raise StatementError('提交过长')
    clean = strip_comments(body)
    for word in FORBIDDEN:
        if allow_holes and word == 'sorry':
            continue  # 骨架里的 sorry 是待拆出的空洞
        match = re.search(r"(?<![\w.'])" + re.escape(word) + r"(?![\w'])", clean)
        if match:
            line = clean.count('\n', 0, match.start()) + 1
            raise StatementError(f'第 {line} 行出现了禁止的词 `{word}`。提交只能包含 `open` 行和 `theorem`/`lemma` 声明。')
    names = []
    for number, line in enumerate(clean.splitlines(), 1):
        if not line or line[0].isspace():
            continue
        head = re.match(r'(theorem|lemma)\s+([^\s:({\[⦃]+)', line)
        if head:
            names.append(head.group(2))
        elif not re.match(r'open\s', line):
            raise StatementError(f'第 {number} 行：顶格的行只能以 `theorem`、`lemma` 或 `open` 开头（证明内容请缩进）。')
    main = task_name + ('_disproof' if disproof else '')
    if not names or names[-1] != main:
        raise StatementError(f'最后一个声明必须是主定理 `{main}`')
    for name in names[:-1]:
        if not re.fullmatch(re.escape(task_name) + r'_aux[A-Za-z0-9_]*', name):
            raise StatementError(f'辅助引理 `{name}` 须命名为 `{task_name}_aux…`，以免与库中其他定理重名')
    if len(set(names)) != len(names):
        raise StatementError('声明名称重复')
    return names


def is_disproof(body, task_name):
    """提交里若声明了 `<任务名>_disproof`，就按证伪处理，不要求调用方另外加标志。"""
    return bool(re.search(r'^(?:theorem|lemma)\s+' + re.escape(task_name) + r'_disproof(?![\w\'])', strip_comments(body), re.M))


def analyse_definition(body, name):
    """新定义的静态检查：只允许一条 `def <name> …`（可带 noncomputable）和 `open` 行。"""
    if len(body) > 20000:
        raise StatementError('定义过长')
    clean = strip_comments(body)
    for word in FORBIDDEN:
        if word in ('def', 'noncomputable'):
            continue
        match = re.search(r"(?<![\w.'])" + re.escape(word) + r"(?![\w'])", clean)
        if match:
            raise StatementError(f'定义里出现了禁止的词 `{word}`。只能写一条 `def`，不能带实例、记号、属性或 sorry。')
    heads = []
    for number, line in enumerate(clean.splitlines(), 1):
        if not line or line[0].isspace():
            continue
        head = re.match(r"(?:noncomputable\s+)?def\s+([^\s:({\[⦃]+)", line)
        if head:
            heads.append(head.group(1))
        elif not re.match(r'open\s', line):
            raise StatementError(f'第 {number} 行：顶格的行只能是 `def`（可带 noncomputable）或 `open`。')
    if heads != [name]:
        raise StatementError(f'必须恰好包含一条名为 `{name}` 的 def')
    if len(re.findall(r"(?<![\w.'])def(?![\w'])", clean)) != 1:
        raise StatementError('只能出现一个 def')


# 外部数据集里常见的形式化错误：从文本就能识别，提醒证明者和复核者“这条 Lean 写法可能不是原题的意思”。
LINTS = [
    (re.compile(r'\^\s*\(\s*\d+\s*/\s*\d+\s*\)'),
     '指数写成了 `^ (m / n)`：在 Lean 里 `m / n` 默认按自然数除法计算（例如 1 / 3 = 0），于是 `x ^ (1 / 3)` 就是 `x ^ 0 = 1`，'
     '不是立方根。若原题是分数次幂，应写成 `x ^ ((1 : ℝ) / 3)`。'),
]


def lint_statement(statement):
    """返回命题里疑似形式化错误的提醒（只看文本，不改变任何判断）。"""
    return [message for pattern, message in LINTS if pattern.search(statement)]
