import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from streamlit.testing.v1 import AppTest
from test_documents import PAPER
from mathlib2.store import Store


class AppTests(unittest.TestCase):
    @unittest.skipUnless(PAPER.exists(), '需实际论文文件')
    def test_upload_source_filter_and_unknown(self):
        with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ, {'MATHLIB2_DB':str(Path(tmp)/'app.sqlite'), 'MATHLIB2_PROVIDER':'mock'}):
            store = Store(os.environ['MATHLIB2_DB'])
            sid = store.add('sources',{'path':str(Path('samples/nat.md').resolve()),'sha256':'legacy','objects':[]})
            store.add('candidates',{'label':'旧教学候选','statement':'∀ n : Nat, n = n','depends_on':[]},sid)
            store.db.close()
            app = AppTest.from_file(str(Path(__file__).resolve().parents[1]/'app.py')).run(timeout=30)
            self.assertFalse(app.exception)
            app.selectbox(key='research_page').select('文献管理').run()
            app.file_uploader(key='document_upload').upload('s40753-021-00140-1.pdf',PAPER.read_bytes()).run()
            app.button(key='run_document').click().run(timeout=30)
            self.assertFalse(app.exception)
            self.assertFalse(app.error)
            self.assertTrue(app.session_state['last_result']['results'])
            self.assertEqual(len(app.session_state['last_result']['results']),4)
            self.assertTrue(any('保留的原始资料' in e.label for e in app.expander))
            self.assertEqual(app.session_state['last_result']['stages']['lean'],'not_run')
            self.assertTrue(all(x['status']=='unknown' for x in app.session_state['last_result']['results']))
            current = app.session_state['last_result']['source_id']
            self.assertNotEqual(current,sid)
            self.assertEqual(app.session_state['source_select'],current)
            db = Store(os.environ['MATHLIB2_DB'])
            risk_id = next(r['id'] for r in db.rows('candidates') if r['payload'].get('semantic_status')=='potential_counterexample')
            db.db.close()
            app.selectbox(key='research_page').select('候选审核').run()
            app.selectbox(key=f'candidate_{current}').select(risk_id).run()
            self.assertFalse(app.exception)
            self.assertTrue(any('潜在边界反例' in w.value for w in app.warning))
            app.selectbox(key='research_page').select('知识库').run()
            self.assertTrue(app.form_submit_button[0].disabled)
            app.selectbox(key='research_page').select('文献管理').run()
            app.selectbox(key=f'material_{current}').select(0).run()
            self.assertFalse(app.exception)
            app.selectbox(key='input_mode').select('当前文献').run()
            app.button(key='run_document').click().run(timeout=30)
            self.assertFalse(app.exception)
            self.assertTrue(app.session_state['last_result']['reused'])
