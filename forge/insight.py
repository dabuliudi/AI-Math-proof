"""库的检索、依赖图和供数学家挑选的排序。全部从台账计算，不需要 Lean。"""
import math
import re
from collections import Counter

from . import library


def _tokens(text):
    words = re.findall(r'[A-Za-z][a-z]+|[A-Z]+(?![a-z])|\d+|[^\sA-Za-z0-9_().,:\[\]{}]', text)
    return [w.lower() for w in words]


def search(query, limit=10):
    """BM25 词法检索：名称、命题类型、非形式化描述一起算。符号（∣ ≤ ∀…）也是词。"""
    docs = [d for d in library.entries()]
    # 辅助引理也进检索：它们的名字不带内容，只能靠命题类型和所属条目的描述被找到。
    owners = {d['name']: d for d in docs}
    for helper, info in library.helper_index().items():
        owner = owners.get(info['owner'], {})
        docs.append(dict(name=helper, type=info['type'], tier='helper',
                         informal=f'（{info["owner"]} 的辅助引理）' + owner.get('informal', '')[:120]))
    if not docs:
        return []
    bags = [Counter(_tokens(' '.join([d['name'].replace('_', ' '), d['type'], d['type'], d.get('informal', '')]))) for d in docs]
    average = sum(sum(b.values()) for b in bags) / len(bags)
    frequency = Counter(t for b in bags for t in b)
    scored = []
    for doc, bag in zip(docs, bags):
        length = sum(bag.values())
        score = 0.0
        for term in set(_tokens(query)):
            if term in bag:
                idf = math.log(1 + (len(docs) - frequency[term] + 0.5) / (frequency[term] + 0.5))
                score += idf * bag[term] * 2.2 / (bag[term] + 1.2 * (0.25 + 0.75 * length / average))
        if score > 0:
            scored.append((score, doc))
    scored.sort(key=lambda pair: -pair[0])
    return [dict(name='Mathlib2.' + d['name'], type=d['type'], informal=d.get('informal', ''), tier=d['tier'],
                 score=round(s, 2)) for s, d in scored[:limit]]


def _owners():
    """辅助引理名 -> 它所属的条目名。别的证明引用某条目的辅助引理，也算引用了那个条目。"""
    owners = {}
    for entry in library.entries():
        owners[entry['name']] = entry['name']
        for helper in entry.get('helpers', []):
            owners[helper] = entry['name']
    return owners


def _deps(entry, owners):
    return sorted({owners[d] for d in entry.get('library_deps', []) if d in owners and owners[d] != entry['name']})


def cited_by():
    counts = Counter()
    owners = _owners()
    for entry in library.entries():
        for dep in _deps(entry, owners):
            counts[dep] += 1
    return counts


def dag(name=None):
    """内核给出的引用关系（证明项里实际用到的 Mathlib2 定理），不是从文本猜的。"""
    owners = _owners()
    by_name = {e['name']: dict(e, library_deps=_deps(e, owners)) for e in library.entries()}
    if name is None:
        keep = set(by_name)
    else:
        keep, stack = set(), [name]
        while stack:
            current = stack.pop()
            if current in keep or current not in by_name:
                continue
            keep.add(current)
            stack.extend(by_name[current].get('library_deps', []))
    depth = {}

    def level(node):
        if node not in depth:
            depth[node] = 0
            parents = [d for d in by_name[node].get('library_deps', []) if d in by_name]
            depth[node] = 1 + max((level(p) for p in parents), default=-1)
        return depth[node]

    nodes = [dict(name=n, kind=by_name[n]['kind'], tier=by_name[n]['tier'], depth=level(n)) for n in sorted(keep)]
    edges = [dict(source=d, target=n) for n in sorted(keep) for d in by_name[n].get('library_deps', []) if d in by_name]
    return dict(nodes=nodes, edges=edges, max_depth=max((n['depth'] for n in nodes), default=0))


def report(limit=30):
    """给数学家的挑选清单。分数只是排序启发：需要 agent 才能证出、被后续证明引用、证伪了一个猜想，都加分。"""
    from .paper import reviews
    citations = cited_by()
    checked = reviews()
    rows = []
    for entry in library.entries():
        if entry['kind'] == 'definition':
            continue  # 定义不参与“定理”排序；它的价值体现在被多少定理引用
        score = (3 if entry['tier'] == 'agent' else 0) + 2 * citations[entry['name']] + \
                (1 if entry['kind'] == 'disproved' else 0) + min(entry.get('attempts', 1) - 1, 3)
        rows.append(dict(name=entry['name'], kind=entry['kind'], tier=entry['tier'], score=score,
                         cited_by=citations[entry['name']], origin=entry.get('origin', ''),
                         statement=entry['type'], informal=entry.get('informal', ''), source=entry.get('source', ''),
                         alignment=[r['verdict'] for r in checked.get(entry['task'], [])]))
    rows.sort(key=lambda r: (-r['score'], r['name']))
    return rows[:limit]


def catalog():
    """给人读的库目录（Markdown）：按排序分数列出每条定理的命题、来源、层级、依赖和复核结论。"""
    from .paper import reviews
    entries = {e['name']: e for e in library.entries()}
    definitions = [e for e in library.entries() if e['kind'] == 'definition']
    checked = reviews()
    citations = cited_by()
    rows = report(limit=10 ** 9)
    lines = ['# Mathlib2 目录', '',
             f'共 {len(rows)} 条内核验证的定理：{sum(r["kind"] == "proved" for r in rows)} 条证明，'
             f'{sum(r["kind"] == "disproved" for r in rows)} 条证伪；'
             f'{sum(r["tier"] == "agent" for r in rows)} 条需要 agent 才证出，'
             f'{sum(r["tier"] == "auto" for r in rows)} 条被自动化直接关掉。', '',
             '排序分数只是启发：需要 agent 才能证出、被后续证明引用、证伪了一个猜想、前人失败过，都加分。'
             '“复核”一栏是独立 agent 对“Lean 命题是否忠实于原文”的判断，不是内核保证的内容。', '']
    for row in rows:
        entry = entries[row['name']]
        lines.append(f'## `Mathlib2.{row["name"]}`')
        lines.append('')
        if entry.get('informal'):
            lines.append(entry['informal'])
            lines.append('')
        lines.append('```lean')
        lines.append(entry['type'])
        lines.append('```')
        facts = [f'结论：{"证伪" if entry["kind"] == "disproved" else "证明"}', f'层级：{entry["tier"]}',
                 f'来源：{entry.get("origin", "")}' + (f'（{entry["source"]}）' if entry.get('source') else ''),
                 f'完成者：{entry.get("proved_by", "")}', f'尝试次数：{entry.get("attempts", 1)}',
                 f'被引用：{citations[row["name"]]} 次', f'分数：{row["score"]}']
        if entry.get('library_deps'):
            facts.append('依赖：' + '、'.join(f'`{d}`' for d in entry['library_deps']))
        for record in checked.get(entry['task'], []):
            facts.append(f'复核（{record["agent"]}）：{record["verdict"]} — {record["note"][:300]}')
        lines.extend(f'- {fact}' for fact in facts)
        lines.append('')
    if definitions:
        lines.extend(['# 新引入的定义', '', '定义只由内核保证良构；是否忠实于原文见复核栏。', ''])
        for entry in definitions:
            lines.extend([f'## `Mathlib2.{entry["name"]}`', '', entry.get('informal', ''), '', '```lean', entry['statement'], '```',
                          f'- 来源：{entry.get("source", "")}', f'- 被引用：{citations[entry["name"]]} 次'])
            lines.extend(f'- 复核（{r["agent"]}）：{r["verdict"]} — {r["note"][:300]}' for r in checked.get(entry['task'], []))
            lines.append('')
    return '\n'.join(lines)
