"""保守规则识别；原文切片针对未清洗的逐页文本。"""
import re

VERSION = '0.3.0'
KINDS = 'Definition|Theorem|Lemma|Proposition|Corollary|Proof|Example|Conjecture'


def extract_page(text, page):
    objects = []

    def add(start, end, kind, title, method, confidence, uncertain=False, reason=''):
        while end > start and text[end-1].isspace():
            end -= 1
        if end <= start or any(o['start'] <= start < o['end'] for o in objects):
            return
        raw = text[start:end]
        objects.append(dict(object_type=kind, title=title, body=raw, text=raw, original_text=raw,
            page=page, line=text[:start].count('\n')+1,
            paragraph=len(re.findall(r'\n\s*\n', text[:start]))+1,
            start=start, end=end, context_before=text[max(0,start-240):start],
            context_after=text[end:end+240], extraction_method=method, confidence=confidence,
            recognition_status='uncertain' if uncertain else 'recognized', reason=reason))

    for m in re.finditer(r'(?s)\\begin\{(' + KINDS.lower() + r')\}(?:\[([^\]]*)\])?.*?\\end\{\1\}', text):
        add(m.start(), m.end(), m[1].title(), m[2] or m[1].title(), 'latex_environment', .98)

    # 代码作为原始资料单独识别；不把作者 Lean 代码当作系统新证明。
    for m in re.finditer(r'(?m)^(?:def |theorem |lemma |variable |```lean)[^\n]*', text):
        if not m.group().startswith(('variable ', '```lean')) and not re.match(r"^(?:def|theorem|lemma) [\w.']+\s*(?:[({\[:]|$)",m.group()):
            continue  # 小写 theorem/lemma 出现在叙述中，不是 Lean 声明。
        tail = text[m.end():]
        boundary = re.search(r'(?m)\n(?:\s*\n|```|def |theorem |lemma |variable |The |Using |Now |Our |We |Here |Finally,|[1-9] [A-Z]|(?:'+KINDS+r')\s+\d)', tail)
        end = m.end()+boundary.start() if boundary else min(len(text), m.end()+1000)
        add(m.start(), end, 'Code', m.group().strip(), 'lean_code_fragment', .85,
            reason='论文代码转录；未经执行，不是独立生成的证明')

    headers = []
    for m in re.finditer(r'(?m)^[ \t]*(?P<md>\#{1,6}[ \t]+)?(?P<kind>' + KINDS + r')\b(?P<tail>[^\n]*)', text):
        tail = m['tail'].strip()
        kind = m['kind']
        numbered = bool(re.match(r'\d+(?:\.\d+)*(?:\b|[.:])', tail))
        proof = kind == 'Proof' and (not tail or tail.startswith(('.', ':', '(Proof of ')) or re.match(r'of\s+(?:Theorem|Lemma|Proposition|Corollary)\s+\d', tail))
        certain = bool(m['md']) or numbered or proof
        if certain or not tail or tail.startswith((':', '.')):
            headers.append((m, kind, certain))
    for i, (m, kind, certain) in enumerate(headers):
        end = headers[i+1][0].start() if i+1 < len(headers) else len(text)
        boundary = re.search(r'(?m)^#{1,6}\s+', text[m.end():end])
        if boundary:
            end = m.end()+boundary.start()
        if not m['md']:
            blank = re.search(r'\n\s*\n', text[m.end():end])
            if blank:
                end = m.end()+blank.start()
            discussion = re.search(r'(?m)\n(?:Mason and Stothers|Like the ABC|From|Next,|Since|We |Our |[1-9] [A-Z]|theorem |def |variable )', text[m.end():end])
            if discussion and kind != 'Proof':
                end = m.end()+discussion.start()
        add(m.start(), end, kind, m.group().strip(), 'numbered_heading' if certain else 'ambiguous_heading',
            .9 if certain else .4, not certain, '' if certain else '缺少编号或明确标记；待核查')

    chinese = {'定义':'Definition','定理':'Theorem','引理':'Lemma','命题':'Proposition','推论':'Corollary','证明':'Proof','例':'Example','猜想':'Conjecture'}
    for m in re.finditer(r'(?m)^#{1,6}\s*(定义|定理|引理|命题|推论|证明|例|猜想)[^\n]*', text):
        next_heading = re.search(r'(?m)^#{1,6}\s+', text[m.end():])
        end = m.end()+next_heading.start() if next_heading else len(text)
        add(m.start(), end, chinese[m[1]], m.group(), 'markdown_heading', .9)

    # 叙述型定义必须出现显式定义关系。
    definition = r'(?m)(?:^|(?<=[.!?])\s+)(?:\d+\.\s+)?(?:An?\s+[^.\n]{1,70}?\s+is\s+(?:an?\s+)?(?:integer|number|set|function|group)\b[^.]*\.|[^.\n]{1,100}?\bis\s+(?:called|defined as)\s+[^.]*\.)'
    for m in re.finditer(definition, text):
        if not re.search(r'\b(integer|number|function|set|group|divisor|prime)\b|[∈∀∃]', m.group(), re.I):
            continue
        start = m.start()
        while start < m.end() and text[start].isspace():
            start += 1
        add(start, m.end(), 'Definition', text[start:m.end()].split('\n')[0], 'explicit_definition_sentence', .78)

    for m in re.finditer(r'(?m)^[ \t]*(?:\d+\.\s+(?:Prove that|Show that|If\b|Let\b)|\([a-z]\)\s+)[^\n]*', text):
        if not ('Prove that' in m.group() or 'Show that' in m.group() or 'Tasks:' in text[max(0,m.start()-1800):m.start()]):
            continue
        tail = text[m.start():]
        boundary = re.search(r'(?m)\n(?:\s*\n|\([a-z]\)|\d+\.|Tasks:|Fig(?:ure)?\.?\s*\d|Table\s+\d|Acknowledgements|Funding|Declarations)', tail)
        end = m.start()+boundary.start() if boundary else len(text)
        add(m.start(), end, 'Conjecture', m.group().strip(), 'numbered_task', .82,
            reason='练习题原文；真值及隐含假设未判断')

    for m in re.finditer(r'(?mi)^(?:Fig(?:ure)?\.?|Table)\s*\d+[^\n]*', text):
        if re.match(r'^Fig\.?\s*\d+\.', m.group()):
            continue  # “Fig. 10. The proof ...” 是正文，不是图注
        prose = bool(re.match(r'(?:Fig(?:ure)?\.?|Table)\s*\d+\s+(?:shows?|reports?|illustrates?|presents?|summarizes?)\b',m.group(),re.I))
        add(m.start(), m.end(), 'SourceMaterial', m.group(),
            'prose_reference' if prose else ('table_caption_only' if m.group().lower().startswith('table') else 'figure_caption_only'),
            .3, True, '仅图表标题；图片内容需 OCR 或人工转录，不是完整证明')

    for m in re.finditer(r'[^.!?\n][^.!?]*[.!?](?=\s|$)', text):
        raw = m.group()
        if len(raw) > 1200:
            continue
        if re.search(r'statement is false|prompted to provide a proof', raw, re.I):
            add(m.start(), m.end(), 'Proof', raw.split('\n')[0], 'condition_discussion', .55, True,
                '作者对条件或真假的讨论；不自动修订原始任务')
        elif re.search(r'\b(?:He|She|They) (?:then |continues |starts |moves on |replaces )', raw) and re.search(r'divisor|perfect|abundant|sum|multiply', raw, re.I):
            add(m.start(), m.end(), 'Proof', raw.split('\n')[0], 'narrative_proof_step', .5, True,
                '证明步骤叙述；指代和跨页关联未解析，不自动建立逻辑依赖')
    for obj in objects:
        obj['statement_text'] = obj['text'] if obj['object_type'] not in {'Proof','Code','SourceMaterial'} else ''
        obj['proof_body'] = obj['text'] if obj['object_type']=='Proof' else ''
        obj['code_fragments'] = [obj['text']] if obj['object_type']=='Code' else []
        obj['boundary_status'] = 'page_limited' if obj['end'] == len(text.rstrip()) else 'local_boundary'
        obj['proof_steps'] = []
        if obj['extraction_method'] == 'narrative_proof_step':
            cuts = [0] + [m.start() for m in re.finditer(r'\band (?:then |moves on |therefore |hence )', obj['text'])] + [len(obj['text'])]
            for a,b in zip(cuts,cuts[1:]):
                obj['proof_steps'].append({'text':obj['text'][a:b], 'page':page,
                    'start':obj['start']+a, 'end':obj['start']+b, 'status':'uncertain',
                    'sequence_only':True, 'reason':'原文叙述分句，不等于已证明引理或逻辑依赖'})
    return sorted(objects, key=lambda o: o['start'])


def extract(pages):
    return [obj for page, text in pages for obj in extract_page(text, page)]
