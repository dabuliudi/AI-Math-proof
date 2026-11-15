"""成果展示页：由台账与 forge/data/showcase.json 生成的单文件静态页面（数据内嵌），不依赖服务器。

面向两类读者：不懂数学的人（精选成果的大白话、论文体检的红绿灯、领域分布），
以及数学家（最下面可搜索的全部定理，带 Lean 原文与收藏导出）。大白话说明写在 showcase.json 里，
可以由人或 agent 逐条补充，不需要改这个文件。
"""
import json
import re
import time

from . import insight, library
from .leanrun import DATA, STAGING
from .paper import reviews

SHOWCASE = DATA / 'showcase.json'
DOMAINS = ['数论', '代数', '多项式', '线性代数', '分析', '组合与图论', '几何与拓扑']
_PREFIX = {'poly': '多项式', 'ms': '多项式', 'lin': '线性代数', 'comb': '组合与图论', 'gr': '组合与图论', 'geo': '几何与拓扑',
           'top': '几何与拓扑', 'ana': '分析', 'alg': '代数', 'arith': '数论', 'nt': '数论', 'nt2': '数论', 'ab': '数论',
           'p3': '数论', 'p4': '数论', 'p5': '数论'}


def domain(name, statement):
    """按名称前缀与命题里的关键词粗分领域，只用于展示。"""
    prefix = re.match(r'[a-z]+\d*', name).group(0)
    words = name.lower()
    if prefix in _PREFIX:
        return _PREFIX[prefix]
    if 'Polynomial' in statement:
        return '多项式'
    if any(w in words for w in ('rank', 'matrix', 'nilpotent', 'idempot', 'fitting', 'tripotent', 'involution')) or 'Matrix' in statement:
        return '线性代数'
    if any(w in words for w in ('graph', 'mantel', 'ramsey', 'szekeres', 'card', 'choose', 'perm', 'derange', 'subset', 'hockey')) \
            or 'SimpleGraph' in statement:
        return '组合与图论'
    if any(w in words for w in ('isometry', 'compact', 'metric', 'edelstein')) or 'MetricSpace' in statement:
        return '几何与拓扑'
    if prefix == 'calc' or any(w in words for w in ('sqrt_two_rec', 'hardy', 'carleman', 'integral', 'tsum', 'exp', 'pi_')) \
            or any(s in statement for s in ('∫', 'Real.', 'Tendsto', '∑\'')):
        return '分析'
    if any(w in words for w in ('group', 'sylow', 'order', 'center', 'gaussian', 'zsqrtd', 'minpoly', 'field', 'adjoin')):
        return '代数'
    return '数论'


def _audit():
    path = STAGING / 'audit_last.json'
    try:
        data = json.loads(path.read_text(encoding='utf-8'))
        return dict(checked=data['checked'], passed=data['passed'], replay=bool(data.get('replay', {}).get('ok')))
    except (OSError, ValueError, KeyError):
        return None


def build():
    from . import tasks
    checked = reviews()
    citations = insight.cited_by()
    showcase = json.loads(SHOWCASE.read_text(encoding='utf-8')) if SHOWCASE.exists() else dict(featured=[], papers=[])
    entries = []
    for entry in library.entries():
        if entry['kind'] == 'definition':
            continue
        verdicts = [r['verdict'] for r in checked.get(entry['task'], [])]
        entries.append(dict(n=entry['name'], k=entry['kind'], d=domain(entry['name'], entry['statement']),
                            s=entry['statement'], i=(entry.get('informal') or '')[:400], o=entry.get('origin', ''),
                            c=citations[entry['name']], r=verdicts[-1] if verdicts else ''))
    known = {e['n'] for e in entries}
    featured = [f for f in showcase.get('featured', []) if f['name'] in known]
    summary = dict(theorems=len(entries), proved=sum(e['k'] == 'proved' for e in entries),
                   disproved=sum(e['k'] == 'disproved' for e in entries), built_on=sum(e['c'] > 0 for e in entries),
                   depth=insight.dag()['max_depth'], waiting=len(tasks.all_tasks('open')) + len(tasks.all_tasks('claimed')),
                   audit=_audit(), generated=time.strftime('%Y-%m-%d %H:%M'))
    payload = json.dumps(dict(entries=entries, featured=featured, front=showcase.get('front', 6), papers=showcase.get('papers', []), summary=summary,
                              domains=DOMAINS), ensure_ascii=False).replace('</', '<\\/')
    return TEMPLATE.replace('__DATA__', payload)


TEMPLATE = r'''<title>定理铸造厂</title>
<meta name="claude:viewport-fit-sides" content="cover">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Geist:wght@400;500;600;700&family=Geist+Mono:wght@400;500&display=swap">
<style>
/* 布局：单列阅读流。先给结论（一句话 + 四个数字），再解释“计算机检查”，然后精选成果、论文体检、领域分布，
   最后才是给数学家的全部定理。视觉沿用 shadcn 的中性色、细边框和徽章；唯一的强调色是“已证实”的绿。 */
:root{
  --bg:#fafafa; --card:#ffffff; --fg:#0a0a0b; --muted:#6b6b74; --line:#e5e5e8; --soft:#f3f3f5;
  --primary:#18181b; --primary-fg:#fafafa; --ok:#047857; --ok-soft:#e7f6ef; --warn:#a15c07; --warn-soft:#fdf3e2;
  --bad:#c02626; --bad-soft:#fdecec; --idle:#6b6b74; --idle-soft:#f1f1f3;
  --sans:"Geist","PingFang SC","Hiragino Sans GB","Noto Sans SC","Microsoft YaHei",system-ui,sans-serif;
  --mono:"Geist Mono","SF Mono",Menlo,Consolas,monospace;
  --radius:10px;
}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){
  --bg:#09090b; --card:#111114; --fg:#f4f4f5; --muted:#a1a1aa; --line:#27272a; --soft:#18181b;
  --primary:#f4f4f5; --primary-fg:#18181b; --ok:#34d399; --ok-soft:#0d2a20; --warn:#fbbf24; --warn-soft:#2b2110;
  --bad:#f87171; --bad-soft:#2d1414; --idle:#a1a1aa; --idle-soft:#1c1c20; color-scheme:dark}}
:root[data-theme="dark"]{
  --bg:#09090b; --card:#111114; --fg:#f4f4f5; --muted:#a1a1aa; --line:#27272a; --soft:#18181b;
  --primary:#f4f4f5; --primary-fg:#18181b; --ok:#34d399; --ok-soft:#0d2a20; --warn:#fbbf24; --warn-soft:#2b2110;
  --bad:#f87171; --bad-soft:#2d1414; --idle:#a1a1aa; --idle-soft:#1c1c20; color-scheme:dark}
*{box-sizing:border-box}
body{background:var(--bg);color:var(--fg);font-family:var(--sans);font-size:15px;line-height:1.65;-webkit-font-smoothing:antialiased}
.wrap{max-width:1040px;margin:0 auto;padding-block:28px 72px;padding-left:max(16px,env(safe-area-inset-left,0px));padding-right:max(16px,env(safe-area-inset-right,0px));display:flex;flex-direction:column;gap:56px}
section{display:flex;flex-direction:column;gap:18px}
h1{font-size:clamp(26px,4.2vw,38px);line-height:1.2;font-weight:700;letter-spacing:-.02em;margin:0;text-wrap:balance;max-width:22ch}
h2{font-size:22px;font-weight:600;letter-spacing:-.01em;margin:0;text-wrap:balance}
h3{font-size:16px;font-weight:600;margin:0;line-height:1.45;text-wrap:balance}
p{margin:0}
.lede{color:var(--muted);font-size:17px;max-width:62ch}
.sub{color:var(--muted);max-width:66ch}
.top{display:flex;align-items:center;gap:10px;flex-wrap:wrap;color:var(--muted);font-size:13px}
.brand{font-weight:600;color:var(--fg);font-size:15px}
.badge{display:inline-flex;align-items:center;gap:5px;font-size:12px;font-weight:500;border:1px solid var(--line);border-radius:999px;padding:1px 9px;color:var(--muted);background:var(--card);white-space:nowrap;line-height:1.7}
.badge.ok{color:var(--ok);background:var(--ok-soft);border-color:transparent}
.badge.warn{color:var(--warn);background:var(--warn-soft);border-color:transparent}
.badge.bad{color:var(--bad);background:var(--bad-soft);border-color:transparent}
.badge.idle{color:var(--idle);background:var(--idle-soft);border-color:transparent}
.dot{width:6px;height:6px;border-radius:50%;background:currentColor;display:inline-block}
.hero{display:flex;flex-direction:column;gap:14px}
.stats{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:12px}
.stat{background:var(--card);border:1px solid var(--line);border-radius:var(--radius);padding:16px 18px;display:flex;flex-direction:column;gap:2px;min-width:0}
.stat b{font-size:30px;font-weight:600;letter-spacing:-.02em;font-variant-numeric:tabular-nums;line-height:1.2}
.stat .label{font-weight:500}
.stat .note{color:var(--muted);font-size:13px}
.stat.verified b{color:var(--ok)}
.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:14px}
.card{background:var(--card);border:1px solid var(--line);border-radius:var(--radius);padding:18px 20px;display:flex;flex-direction:column;gap:10px;min-width:0}
.card .row{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.card .plain{font-size:15px}
.card .why{color:var(--muted);font-size:14px}
details{min-width:0}
summary{cursor:pointer;color:var(--muted);font-size:13px;width:fit-content;list-style:none}
summary::-webkit-details-marker{display:none}
summary::before{content:"›";display:inline-block;margin-right:6px;transition:transform .15s}
details[open] summary::before{transform:rotate(90deg)}
summary:hover{color:var(--fg)}
pre{margin:8px 0 0;background:var(--soft);border:1px solid var(--line);border-radius:8px;padding:10px 12px;font-family:var(--mono);font-size:13px;line-height:1.55;overflow-x:auto;white-space:pre-wrap;word-break:break-word}
.lean-name{font-family:var(--mono);font-size:12px;color:var(--muted);word-break:break-all}
.papers{display:flex;flex-direction:column;border:1px solid var(--line);border-radius:var(--radius);background:var(--card);overflow:hidden}
.paper{display:grid;grid-template-columns:200px minmax(0,1fr);gap:6px 20px;padding:16px 20px;border-top:1px solid var(--line)}
.paper:first-child{border-top:0}
.paper .verdict{display:flex;flex-direction:column;gap:6px;align-items:flex-start}
.paper .verdict .count{color:var(--muted);font-size:13px;font-variant-numeric:tabular-nums}
.paper .body{display:flex;flex-direction:column;gap:4px;min-width:0}
.paper a{color:var(--muted);font-family:var(--mono);font-size:12.5px;text-decoration:none;width:fit-content}
.paper a:hover{color:var(--fg);text-decoration:underline}
.tools{display:flex;gap:10px;flex-wrap:wrap;align-items:center}
input[type=search],select{font:inherit;font-size:14px;height:36px;padding:0 12px;border:1px solid var(--line);border-radius:8px;background:var(--card);color:var(--fg)}
input[type=search]{flex:1 1 260px;min-width:0}
button{font:inherit;font-size:14px;height:36px;padding:0 14px;border-radius:8px;border:1px solid var(--line);background:var(--card);color:var(--fg);cursor:pointer}
button.primary{background:var(--primary);color:var(--primary-fg);border-color:var(--primary)}
button:hover{background:var(--soft)} button.primary:hover{opacity:.9;background:var(--primary)}
:focus-visible{outline:2px solid var(--fg);outline-offset:2px}
.count{color:var(--muted);font-size:13px;font-variant-numeric:tabular-nums}
.list{display:flex;flex-direction:column;border:1px solid var(--line);border-radius:var(--radius);background:var(--card);overflow:hidden}
.item{padding:14px 18px;border-top:1px solid var(--line);display:flex;flex-direction:column;gap:6px;min-width:0}
.item:first-child{border-top:0}
.item .row{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.item .lean-name{color:var(--fg);font-size:13px}
.item .informal{color:var(--muted);font-size:14px;max-width:80ch}
.star{height:28px;padding:0 10px;font-size:13px;margin-left:auto}
.item.picked .star{background:var(--ok-soft);color:var(--ok);border-color:transparent}
.more{align-self:center}
#export{width:100%;min-height:96px;font-family:var(--mono);font-size:13px;background:var(--soft);color:var(--fg);border:1px solid var(--line);border-radius:8px;padding:10px}
.experts>summary{font-size:15px;font-weight:500;color:var(--fg);border:1px solid var(--line);border-radius:var(--radius);background:var(--card);padding:12px 16px;width:100%}
.experts-body{margin-top:16px}
footer{color:var(--muted);font-size:13px;display:flex;flex-direction:column;gap:4px}
@media (max-width:820px){.stats{grid-template-columns:1fr}.grid{grid-template-columns:1fr}.paper{grid-template-columns:1fr}}
@media (prefers-reduced-motion:reduce){*{transition:none!important}}
</style>
<div class="wrap">
  <header class="hero">
    <div class="top"><span class="brand">定理铸造厂</span><span class="badge">Mathlib2</span><span id="generated"></span></div>
    <h1 id="headline">AI 写下的数学定理，每一条都经过计算机逐步检查</h1>
    <p class="lede">AI 提出数学命题并写出证明，计算机逐步核对，有一步不严格就不收。这些大多是已知结论，哪些有价值由数学家判断。</p>
    <div class="stats" id="stats"></div>
  </header>

  <section aria-labelledby="featured-title">
    <h2 id="featured-title">精选成果</h2>
    <div class="grid" id="featured"></div>
  </section>

  <section aria-labelledby="papers-title">
    <h2 id="papers-title">论文体检</h2>
    <div class="papers" id="papers"></div>
  </section>

  <details class="experts">
    <summary id="experts-summary">给数学家：查看全部定理</summary>
    <section aria-label="全部定理" class="experts-body">
      <div class="tools">
        <input type="search" id="q" placeholder="搜索名称、命题或描述，例如 Fibonacci、∣、rank" aria-label="搜索定理">
        <select id="dom" aria-label="按领域筛选"></select>
        <select id="kind" aria-label="按结论筛选"><option value="">证明与证伪</option><option value="proved">只看证明</option><option value="disproved">只看证伪</option></select>
        <select id="sort" aria-label="排序"><option value="cited">被引用最多</option><option value="name">按名称</option></select>
        <span class="count" id="count"></span>
      </div>
      <div class="list" id="list"></div>
      <button class="more" id="more">显示更多</button>
      <div class="tools"><strong>我的收藏</strong><span class="count" id="pickcount"></span><button id="copy">复制清单</button><span class="count" id="copied" role="status"></span></div>
      <textarea id="export" readonly aria-label="收藏清单"></textarea>
    </section>
  </details>

  <footer id="footer"></footer>
</div>
<script>
const DATA = __DATA__;
const $ = id => document.getElementById(id);
const esc = s => String(s).replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const S = DATA.summary;
const byName = Object.fromEntries(DATA.entries.map(e => [e.n, e]));

$('generated').textContent = '更新于 ' + S.generated;
$('headline').textContent = `AI 写下的 ${S.theorems} 条数学定理，每一条都经过计算机逐步检查`;
const audit = S.audit;
$('stats').innerHTML = [
  ['verified', S.theorems, '条定理已被证实', `${S.proved} 条证明，${S.disproved} 条找到反例`],
  ['', audit ? `${audit.passed}/${audit.checked}` : '—', '独立复查通过', audit && audit.replay ? '检查程序又从头重放了一遍' : '无一出错'],
  ['', DATA.papers.length, '篇论文做了体检', `发现 ${DATA.papers.filter(p => p.status === 'error').length} 处计算错误`],
].map(([cls, big, label, note]) => `<div class="stat ${cls}"><b>${esc(big)}</b><span class="label">${esc(label)}</span><span class="note">${esc(note)}</span></div>`).join('');

$('featured').innerHTML = DATA.featured.slice(0, DATA.front).map(f => {
  const e = byName[f.name];
  return `<article class="card">
    <div class="row"><span class="badge">${esc(f.domain)}</span>${f.known ? '<span class="badge">已知结论</span>' : '<span class="badge warn">可能是新结论</span>'}</div>
    <h3>${esc(f.title)}</h3>
    <p class="plain">${esc(f.plain)}</p>
    ${f.known ? `<p class="why">${esc(f.known)}</p>` : ''}
    <details><summary>计算机里的写法</summary><pre>${esc(e.s)}</pre><div class="lean-name">Mathlib2.${esc(e.n)}</div></details>
  </article>`;
}).join('');

const STATUS = {error:['bad','发现错误'], imprecise:['warn','有不严谨处'], ok:['ok','全部成立'], pending:['idle','进行中']};
$('papers').innerHTML = DATA.papers.map(p => {
  const [cls, label] = STATUS[p.status] || ['idle', p.status];
  return `<div class="paper">
    <div class="verdict"><span class="badge ${cls}"><span class="dot"></span>${esc(label)}</span></div>
    <div class="body"><h3>${esc(p.topic)}</h3><p class="sub">${esc(p.short || p.finding)}</p>
      <details><summary>详情</summary><p class="sub">${esc(p.finding)}</p><a href="${esc(p.url)}" target="_blank" rel="noopener">${esc(p.id)}</a></details></div>
  </div>`;
}).join('');

$('experts-summary').textContent = `给数学家：查看全部 ${S.theorems} 条定理（可搜索、收藏）`;
$('dom').innerHTML = '<option value="">全部领域</option>' + DATA.domains.map(d => `<option value="${esc(d)}">${esc(d)}</option>`).join('');
let picked = new Set();
try { picked = new Set(JSON.parse(localStorage.getItem('forge-picks') || '[]')); } catch (e) {}
const save = () => { try { localStorage.setItem('forge-picks', JSON.stringify([...picked])); } catch (e) {} };
const ORIGIN = {paper:'来自论文', conjecture:'AI 猜想', decomposition:'拆出的引理', human:'人提的问题'};
const REVIEW = {faithful:['ok','复核：忠实'], unfaithful:['bad','复核：不忠实'], unsure:['warn','复核：存疑']};
let shown = 40;

function filtered() {
  const q = $('q').value.trim().toLowerCase(), d = $('dom').value, k = $('kind').value;
  let rows = DATA.entries.filter(e => (!d || e.d === d) && (!k || e.k === k) &&
    (!q || (e.n + ' ' + e.s + ' ' + e.i).toLowerCase().includes(q)));
  rows.sort($('sort').value === 'name' ? (a, b) => a.n.localeCompare(b.n) : (a, b) => b.c - a.c || a.n.localeCompare(b.n));
  return rows;
}
function render() {
  const rows = filtered();
  $('count').textContent = `共 ${rows.length} 条`;
  $('list').innerHTML = rows.slice(0, shown).map(e => {
    const review = REVIEW[e.r];
    return `<div class="item ${picked.has(e.n) ? 'picked' : ''}">
      <div class="row"><span class="lean-name">${esc(e.n)}</span>
        <span class="badge">${esc(e.d)}</span>
        ${e.k === 'disproved' ? '<span class="badge bad">证伪</span>' : ''}
        ${ORIGIN[e.o] ? `<span class="badge">${ORIGIN[e.o]}</span>` : ''}
        ${review ? `<span class="badge ${review[0]}">${review[1]}</span>` : ''}
        ${e.c ? `<span class="badge">被引用 ${e.c} 次</span>` : ''}
        <button class="star" data-n="${esc(e.n)}" aria-pressed="${picked.has(e.n)}">${picked.has(e.n) ? '已收藏' : '收藏'}</button></div>
      ${e.i ? `<p class="informal">${esc(e.i)}</p>` : ''}
      <details><summary>Lean 原文</summary><pre>${esc(e.s)}</pre></details>
    </div>`;
  }).join('') || '<div class="item"><p class="informal">没有符合条件的定理。换个关键词或清除筛选试试。</p></div>';
  $('more').hidden = rows.length <= shown;
  $('pickcount').textContent = `${picked.size} 条`;
  $('export').value = [...picked].sort().map(n => `Mathlib2.${n}`).join('\n');
}
['q', 'dom', 'kind', 'sort'].forEach(id => $(id).addEventListener('input', () => { shown = 40; render(); }));
$('more').addEventListener('click', () => { shown += 60; render(); });
$('list').addEventListener('click', ev => {
  const b = ev.target.closest('.star'); if (!b) return;
  const n = b.dataset.n; picked.has(n) ? picked.delete(n) : picked.add(n); save(); render();
});
$('copy').addEventListener('click', () => {
  const text = $('export').value;
  if (!text) { $('copied').textContent = '还没有收藏任何定理'; return; }
  const done = () => { $('copied').textContent = '已复制'; };
  navigator.clipboard?.writeText(text).then(done, () => { $('export').select(); $('copied').textContent = '已选中，按复制键即可'; })
    ?? ($('export').select(), $('copied').textContent = '已选中，按复制键即可');
});
$('footer').innerHTML = `<p>库里还有 ${S.waiting} 道题在排队等待证明。所有证明只依赖三条数学界公认的基本公理。</p>
  <p>数据生成于 ${esc(S.generated)}。</p>`;
render();
</script>
'''
