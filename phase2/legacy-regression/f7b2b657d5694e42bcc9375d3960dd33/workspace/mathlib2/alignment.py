"""独立语义核读的版本绑定记录；不是自然语言自动等价判定器。"""
import hashlib
from pathlib import Path
from .formalization import ROOT, templates

def digest(text):
    return hashlib.sha256(text.encode('utf-8')).hexdigest()

def valid_record(record, candidate, state, template_id):
    if not record or record.get('conclusion')!='confirmed' or record.get('template_id')!=template_id:
        return False
    if record.get('revision')!=state['revision']:
        return False
    if record.get('original_sha256')!=digest(candidate.get('original_statement',candidate.get('statement',''))):
        return False
    if record.get('normalized_sha256')!=digest(state['normalized_statement']):
        return False
    if record.get('lean_source_sha256')!=digest(templates()[template_id]['source']):
        return False
    report=ROOT/record.get('report_path','')
    if not report.is_file() or hashlib.sha256(report.read_bytes()).hexdigest()!=record.get('report_sha256'):
        return False
    for item in record.get('files',[]):
        path=ROOT/item['path']
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=item['sha256']:
            return False
    return bool(record.get('files')) and record.get('candidate_id')==candidate.get('candidate_id')
