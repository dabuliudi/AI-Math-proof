import hashlib
import logging
from pathlib import Path
from .structures import extract, VERSION


class ParseWarnings(logging.Handler):
    def __init__(self):
        super().__init__(logging.WARNING)
        self.messages = []

    def emit(self, record):
        message = record.getMessage()
        message = '缺少 fontTools，字体编码可能不完整' if 'fontTools' in message else message[:240]
        if message not in self.messages:
            self.messages.append(message)


def ingest(path: str) -> dict:
    p = Path(path)
    raw = p.read_bytes()
    source = {'path': str(p.resolve()), 'filename': p.name, 'sha256': hashlib.sha256(raw).hexdigest(),
              'pages': [], 'objects': [], 'parser_version': VERSION, 'warnings': [],
              'stages': {'file': 'received', 'text': 'pending', 'structure': 'pending', 'candidates': 'pending', 'lean': 'not_run'}}
    try:
        if len(raw) > 10_000_000:
            raise ValueError('文件超过 10 MB 限制')
        if p.suffix.lower() == '.pdf':
            from pypdf import PdfReader
            handler = ParseWarnings()
            logger = logging.getLogger('pypdf')
            logger.addHandler(handler)
            try:
                reader = PdfReader(p)
                pages = [(i+1, page.extract_text() or '') for i, page in enumerate(reader.pages)]
                source['image_pages'] = [i+1 for i, page in enumerate(reader.pages) if '/XObject' in page.get('/Resources', {})]
            finally:
                logger.removeHandler(handler)
            source['warnings'] = handler.messages
        elif p.suffix.lower() in {'.md', '.tex', '.txt'}:
            pages = [(None, raw.decode('utf-8'))]
        else:
            raise ValueError('支持 Markdown、LaTeX、纯文本及文本型 PDF')
    except Exception as exc:
        source['stages'].update(text='failed', structure='not_run', candidates='not_run')
        source['error'] = f'{type(exc).__name__}: {str(exc)[:300]}'
        return source
    source['pages'] = pages
    source['empty_pages'] = [page for page, text in pages if not text.strip()]
    if not any(text.strip() for _, text in pages):
        source['stages'].update(text='needs_ocr', structure='not_run', candidates='not_run')
        source['warnings'].append('没有可提取文字：可能为扫描页或空白页；未执行 OCR')
        return source
    source['objects'] = extract(pages)
    source['stages'].update(text='partial' if source['empty_pages'] else 'parsed', structure='recognized' if source['objects'] else 'no_objects')
    source['method'] = '规则识别；原文切片可追溯不等于数学语义理解；无 OCR'
    return source
