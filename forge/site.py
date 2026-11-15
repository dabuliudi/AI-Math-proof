"""给数学家用的挑选页面：由台账生成的单文件静态页面（数据内嵌），不依赖服务器。"""
import json

from . import insight, library
from .paper import reviews

TEMPLATE = r'''<title>Mathlib2 挑选台</title>
<meta name="claude:viewport-fit-sides" content="cover">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Mono:wght@400;500&family=IBM+Plex+Sans:wght@400;500;600&display=swap">
<style>
/* 布局：顶部概况与筛选条，下面是一列定理卡片；命题用等宽字体，是页面的主角。 */
:root{--bg:#f6f7f4;--panel:#ffffff;--ink:#1c2420;--muted:#5d6b63;--line:#d9ded7;--accent:#1f6f5c;--accent-ink:#ffffff;
 --code:#eef1ec;--good:#1f7a4d;--warn:#9a6a00;--bad:#b0362f;--pick:#c98a00;
 --sans:"IBM Plex Sans",system-ui,-apple-system,"PingFang SC","Microsoft YaHei",sans-serif;
 --mono:"IBM Plex Mono","JuliaMono","DejaVu Sans Mono",Menlo,Consolas,monospace}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){--bg:#141a17;--panel:#1c2420;--ink:#e6ece7;--muted:#9aa8a0;--line:#2f3a34;--accent:#5fc2a6;--accent-ink:#0f1512;--code:#232d28;--good:#6fcf97;--warn:#e0b252;--bad:#ef8a80;--pick:#f0b93a;color-scheme:dark}}
:root[data-theme="dark"]{--bg:#141a17;--panel:#1c2420;--ink:#e6ece7;--muted:#9aa8a0;--line:#2f3a34;--accent:#5fc2a6;--accent-ink:#0f1512;--code:#232d28;--good:#6fcf97;--warn:#e0b252;--bad:#ef8a80;--pick:#f0b93a;color-scheme:dark}
body{background:var(--bg);color:var(--ink);font-family:var(--sans);font-size:15px;line-height:1.55}
.wrap{max-width:980px;margin:0 auto;padding-block:28px 60px;padding-left:max(16px,env(safe-area-inset-left,0px));padding-right:max(16px,env(safe-area-inset-right,0px));display:flex;flex-direction:column;gap:18px}
h1{font-size:26px;font-weight:600;margin:0;text-wrap:balance}
.lede{color:var(--muted);margin:0;max-width:68ch}
.stats{display:flex;flex-wrap:wrap;gap:8px 22px;font-variant-numeric:tabular-nums}
.stats b{font-weight:600;font-size:20px;margin-right:5px}
.stats span{color:var(--muted)}
.bar{display:flex;flex-wrap:wrap;gap:10px;align-items:center;background:var(--panel);border:1px solid var(--line);border-radius:6px;padding:10px 12px}
.bar input[type=search]{flex:1 1 220px;min-width:0;font:inherit;padding:7px 10px;border:1px solid var(--line);border-radius:4px;background:var(--bg);color:var(--ink)}
.bar select,.bar button{font:inherit;padding:7px 10px;border:1px solid var(--line);border-radius:4px;background:var(--bg);color:var(--ink)}
.bar button{cursor:pointer}
.bar button.primary{background:var(--accent);color:var(--accent-ink);border-color:var(--accent)}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
.count{color:var(--muted);font-variant-numeric:tabular-nums}
.list{display:flex;flex-direction:column;gap:12px}
.item{background:var(--panel);border:1px solid var(--line);border-radius:6px;padding:14px 16px;display:flex;flex-direction:column;gap:8px;min-width:0}
.item.picked{border-color:var(--pick);box-shadow:inset 3px 0 0 var(--pick)}
.head{display:flex;gap:10px;align-items:baseline;flex-wrap:wrap}
.name{font-family:var(--mono);font-weight:500;font-size:14px;word-break:break-all}
.tags{display:flex;gap:6px;flex-wrap:wrap;margin-left:auto}
.tag{font-size:12px;border:1px solid var(--line);border-radius:999px;padding:1px 9px;color:var(--muted);white-space:nowrap}
.tag.proved{color:var(--good);border-color:var(--good)}.tag.disproved{color:var(--bad);border-color:var(--bad)}
.tag.faithful{color:var(--good)}.tag.unfaithful{color:var(--bad)}.tag.unsure{color:var(--warn)}
.informal{margin:0;max-width:72ch}
pre{margin:0;background:var(--code);border-radius:4px;padding:10px 12px;font-family:var(--mono);font-size:13.5px;overflow-x:auto;white-space:pre-wrap;word-break:break-word}
.meta{display:flex;flex-wrap:wrap;gap:4px 16px;color:var(--muted);font-size:13px}
.meta code{font-family:var(--mono);font-size:12.5px}
.review{font-size:13px;color:var(--muted);border-left:2px solid var(--line);padding-left:10px;margin:0}
.pickbtn{font:inherit;font-size:13px;border:1px solid var(--line);background:var(--bg);color:var(--ink);border-radius:4px;padding:4px 10px;cursor:pointer;align-self:flex-start}
.item.picked .pickbtn{background:var(--pick);border-color:var(--pick);color:#1c1400}
.note{color:var(--muted);font-size:13px;max-width:72ch}
#export{width:100%;min-height:120px;font-family:var(--mono);font-size:13px;background:var(--code);color:var(--ink);border:1px solid var(--line);border-radius:4px;padding:10px;box-sizing:border-box}
</style>
<div class="wrap">
  <header style="display:flex;flex-direction:column;gap:8px">
    <h1>Mathlib2 挑选台</h1>
    <p class="lede">这里的每一条都已由 Lean 内核验证，只用到三条标准公理。内核保证证明成立；命题是否值得保留、论文命题是否译得忠实，需要你来判断。勾选你认为有价值的条目，底部可以导出清单。</p>
    <div class="stats" id="stats"></div>
  </header>
  <div class="bar">
    <input type="search" id="q" placeholder="搜索名称、命题或描述（支持 ∣ ≤ ∑ 等符号）" aria-label="搜索">
    <select id="kind" aria-label="结论"><option value="">全部结论</option><option value="proved">证明</option><option value="disproved">证伪</option></select>
    <select id="origin" aria-label="来源"><option value="">全部来源</option><option value="paper">论文</option><option value="conjecture">agent 猜想</option><option value="decomposition">拆解出的引理</option></select>
    <select id="sort" aria-label="排序"><option value="score">按分数</option><option value="cited">按被引用次数</option><option value="name">按名称</option></select>
    <label style="display:flex;gap:6px;align-items:center"><input type="checkbox" id="onlypicked"> 只看已选</label>
    <span class="count" id="count"></span>
  </div>
  <div class="list" id="list"></div>
  <section style="display:flex;flex-direction:column;gap:8px">
    <div style="display:flex;gap:10px;align-items:center;flex-wrap:wrap"><strong>已选清单</strong><button class="pickbtn" id="copy">复制</button><span class="count" id="copied"></span></div>
    <textarea id="export" readonly aria-label="已选清单"></textarea>
    <p class="note">选择只保存在你这台设备的浏览器里，不会回传。把清单复制出来发给维护者即可。分数只是排序启发：需要 agent 才能证出、被后续证明引用、证伪了一个猜想，都会加分。</p>
  </section>
</div>
<script>
const DATA = __DATA__;
const $ = id => document.getElementById(id);
let picked = new Set();
try { picked = new Set(JSON.parse(localStorage.getItem('mathlib2-picks') || '[]')); } catch (e) {}
function save() { try { localStorage.setItem('mathlib2-picks', JSON.stringify([...picked])); } catch (e) {} }
function esc(s) { return String(s).replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c])); }
const ORIGIN = {paper:'论文', conjecture:'agent 猜想', decomposition:'拆解引理', human:'人工', definition:'定义'};
const VERDICT = {faithful:'复核：忠实', unfaithful:'复核：不忠实', unsure:'复核：存疑'};
function render() {
  const q = $('q').value.trim().toLowerCase(), kind = $('kind').value, origin = $('origin').value, only = $('onlypicked').checked, sort = $('sort').value;
  let rows = DATA.entries.filter(e => (!kind || e.kind === kind) && (!origin || e.origin === origin) && (!only || picked.has(e.name)) &&
    (!q || (e.name + ' ' + e.type + ' ' + e.informal + ' ' + e.source).toLowerCase().includes(q)));
  rows.sort(sort === 'name' ? (a, b) => a.name.localeCompare(b.name) : sort === 'cited' ? (a, b) => b.cited - a.cited || b.score - a.score : (a, b) => b.score - a.score || a.name.localeCompare(b.name));
  $('count').textContent = rows.length + ' / ' + DATA.entries.length + ' 条';
  $('list').innerHTML = rows.map(e => `<article class="item${picked.has(e.name) ? ' picked' : ''}">
    <div class="head"><span class="name">Mathlib2.${esc(e.name)}</span><div class="tags">
      <span class="tag ${e.kind}">${e.kind === 'disproved' ? '证伪' : '证明'}</span><span class="tag">${ORIGIN[e.origin] || esc(e.origin)}</span>
      ${e.reviews.map(r => `<span class="tag ${r.verdict}">${VERDICT[r.verdict] || esc(r.verdict)}</span>`).join('')}</div></div>
    ${e.informal ? `<p class="informal">${esc(e.informal)}</p>` : ''}
    <pre>${esc(e.type)}</pre>
    <div class="meta"><span>分数 ${e.score}</span><span>被引用 ${e.cited} 次</span><span>证明 ${e.lines} 行</span>${e.source ? `<span>出处：${esc(e.source)}</span>` : ''}
      ${e.deps.length ? `<span>依赖：${e.deps.map(d => `<code>${esc(d)}</code>`).join('、')}</span>` : ''}</div>
    ${e.reviews.map(r => `<p class="review">${esc(r.note)}</p>`).join('')}
    <button class="pickbtn" data-name="${esc(e.name)}">${picked.has(e.name) ? '已选 · 点击取消' : '选入清单'}</button></article>`).join('') ||
    '<p class="note">没有符合条件的条目。</p>';
  $('export').value = DATA.entries.filter(e => picked.has(e.name)).map(e => `Mathlib2.${e.name} : ${e.type}`).join('\n');
}
$('list').addEventListener('click', ev => { const b = ev.target.closest('.pickbtn'); if (!b) return; const n = b.dataset.name; picked.has(n) ? picked.delete(n) : picked.add(n); save(); render(); });
['q', 'kind', 'origin', 'sort', 'onlypicked'].forEach(id => $(id).addEventListener('input', render));
$('copy').addEventListener('click', () => { const t = $('export'); const done = () => { $('copied').textContent = '已复制'; setTimeout(() => $('copied').textContent = '', 1500); };
  navigator.clipboard.writeText(t.value).then(done).catch(() => { t.select(); $('copied').textContent = '已全选，请手动复制'; }); });
const s = DATA.summary;
$('stats').innerHTML = [[s.theorems, '条定理'], [s.proved, '证明'], [s.disproved, '证伪'], [s.papers, '条来自论文'], [s.reviewed, '条经独立复核'], [s.cited, '条被库内引用'], [s.depth, '层依赖']]
  .map(([n, l]) => `<div><b>${n}</b><span>${l}</span></div>`).join('') + `<div><span>生成于 ${esc(s.generated)}</span></div>`;
render();
</script>
'''


def build():
    import time
    checked = reviews()
    citations = insight.cited_by()
    scores = {row['name']: row['score'] for row in insight.report(limit=10 ** 9)}
    entries = []
    for entry in library.entries():
        if entry['kind'] == 'definition':
            continue
        entries.append(dict(name=entry['name'], kind=entry['kind'], origin=entry.get('origin', ''), type=entry['type'],
                            informal=entry.get('informal', ''), source=entry.get('source', ''), lines=entry.get('lines', 0),
                            score=scores.get(entry['name'], 0), cited=citations[entry['name']], deps=entry.get('library_deps', []),
                            reviews=[dict(verdict=r['verdict'], note=r['note'][:600]) for r in checked.get(entry['task'], [])]))
    summary = dict(theorems=len(entries), proved=sum(e['kind'] == 'proved' for e in entries),
                   disproved=sum(e['kind'] == 'disproved' for e in entries), papers=sum(e['origin'] == 'paper' for e in entries),
                   reviewed=sum(bool(e['reviews']) for e in entries), cited=sum(e['cited'] > 0 for e in entries),
                   depth=insight.dag()['max_depth'], generated=time.strftime('%Y-%m-%d %H:%M'))
    payload = json.dumps(dict(entries=entries, summary=summary), ensure_ascii=False).replace('</', '<\\/')
    return TEMPLATE.replace('__DATA__', payload)
