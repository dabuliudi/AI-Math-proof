import os
import tempfile
import unittest
from pathlib import Path
from mathlib2.store import Store
from mathlib2.pipeline import run
from mathlib2.workbench import candidates_for,review,compile_for,approve_verified,state,graph_for


class E2ETests(unittest.TestCase):
    @unittest.skipUnless(os.environ.get('MATHLIB2_INTEGRATION')=='1','需真实 Lean')
    def test_real_paper_to_verified_test_approval(self):
        with tempfile.TemporaryDirectory() as tmp:
            store=Store(str(Path(tmp)/'e2e.sqlite'))
            try:
                r=run(store,'2408.15180v2.pdf')
                c=next(c for c in candidates_for(store,r['source_id']) if c['title'].startswith('Lemma 1.'))
                cid=c['candidate_id']
                with self.assertRaises(ValueError): approve_verified(store,cid,'自动测试角色','未验证不能批准')
                review(store,cid,'approved','自动测试模拟审核人','仅测试审核流程，不是真人审批；核对Field及非零条件')
                result=compile_for(store,cid,'mason_lemma1')
                self.assertTrue(result['candidate_verified'],result)
                self.assertTrue(any(e.get('used_in_lean') for e in graph_for(store,r['source_id'])['edges']))
                review(store,cid,'approved','自动测试角色','变更必须使旧证据失效',normalized='不同的命题')
                with self.assertRaises(ValueError): approve_verified(store,cid,'自动测试角色','拒绝历史证明')
                review(store,cid,'approved','自动测试角色','恢复并重新验证',normalized=c['normalized_statement'])
                self.assertTrue(compile_for(store,cid,'mason_lemma1')['candidate_verified'])
                approve_verified(store,cid,'自动测试模拟审核人','临时数据库中的流程测试，非生产知识批准')
                self.assertEqual(state(store,cid)['approval_status'],'approved')
                with self.assertRaises(ValueError): review(store,cid,'rejected','x','不能覆盖入库版本')
            finally: store.db.close()
