import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from streamlit.testing.v1 import AppTest
from mathlib2.store import Store
from mathlib2.pipeline import run

ROOT=Path(__file__).resolve().parents[1]

class WorkbenchUiTests(unittest.TestCase):
    def test_empty_navigation_and_guidance(self):
        with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ,{'MATHLIB2_DB':str(Path(tmp)/'empty.sqlite')}):
            app=AppTest.from_file(str(ROOT/'app.py')).run(timeout=30)
            self.assertFalse(app.exception)
            self.assertTrue(any('尚未导入论文' in x.value for x in app.info))
            for page in ['文献管理','候选审核','Proof DAG','Mathlib 检索','Lean Lab','知识库','研究首页']:
                app.selectbox(key='research_page').select(page).run(timeout=30)
                self.assertFalse(app.exception,page)

    def test_candidate_review_history_and_pages(self):
        with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ,{'MATHLIB2_DB':str(Path(tmp)/'data.sqlite'),'MATHLIB2_PROVIDER':'mock'}):
            paper=Path(tmp)/'paper.md'
            paper.write_text('## Theorem 1\nFor all n ∈ N, n = n.',encoding='utf-8')
            store=Store(os.environ['MATHLIB2_DB'])
            run(store,str(paper)); store.db.close()
            app=AppTest.from_file(str(ROOT/'app.py')).run(timeout=30)
            self.assertFalse(app.exception)
            for page in ['候选审核','Proof DAG','Mathlib 检索','Lean Lab','知识库','文献管理']:
                app.selectbox(key='research_page').select(page).run(timeout=30)
                self.assertFalse(app.exception,page)
            app.selectbox(key='research_page').select('候选审核').run()
            app.text_input[0].set_value('测试审核人')
            app.text_area[1].set_value('保留原文，仍待数学语义复核')
            app.button[0].click().run()
            self.assertFalse(app.exception)
            store=Store(os.environ['MATHLIB2_DB'])
            self.assertEqual(len(store.rows('workbench_history')),1)
            self.assertEqual(store.rows('candidates')[0]['status'],'unknown')
            store.db.close()
