import copy
import json
import unittest
from pathlib import Path
from mathlib2.alignment import valid_record
from mathlib2.store import Store
from mathlib2.workbench import state


class AlignmentTests(unittest.TestCase):
    def test_current_record_and_stale_bindings(self):
        path=Path('reports/lemma1-alignment-result.json')
        if not path.exists(): self.skipTest('先执行真实独立语义验收')
        audit=json.loads(path.read_text(encoding='utf-8'))['alignment']
        store=Store()
        try:
            cid=audit['candidate_id']
            c=next((r['payload'] for r in store.rows('candidates') if r['id']==cid),None)
            if c is None: self.skipTest('本机数据库没有该候选记录（data/ 不入库）；需原实验数据库')
            c={**c,'candidate_id':cid}; s=state(store,cid)
            self.assertTrue(valid_record(audit,c,s,'mason_lemma1'))
            for key,value in [('revision',999),('report_sha256','wrong'),('lean_source_sha256','wrong'),('candidate_id',-1)]:
                altered={**audit,key:value}
                self.assertFalse(valid_record(altered,c,s,'mason_lemma1'))
            self.assertFalse(valid_record(audit,{**c,'original_statement':'different'},s,'mason_lemma1'))
            self.assertFalse(valid_record(audit,c,{**s,'normalized_statement':'different'},'mason_lemma1'))
            bad=copy.deepcopy(audit); bad['files'][0]['sha256']='wrong'
            self.assertFalse(valid_record(bad,c,s,'mason_lemma1'))
        finally: store.db.close()
