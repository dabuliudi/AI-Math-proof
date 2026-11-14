import json
import tempfile
import unittest
from pathlib import Path
from mathlib2.store import Store
from mathlib2.workbench import review,state,history,summary,approve_verified
from mathlib2.retrieval import search_mathlib,declaration_index
from mathlib2.planner import ancestors


class WorkflowTests(unittest.TestCase):
    def test_optional_ai_requires_configuration(self):
        from unittest.mock import patch
        from mathlib2.research_ai import configured,suggest
        with patch.dict('os.environ',{'MATHLIB2_RESEARCH_API_URL':''}):
            self.assertFalse(configured())
            with self.assertRaises(ValueError): suggest('n=n')

    def test_review_persists_without_changing_original(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=str(Path(tmp)/'db.sqlite')
            store=Store(path)
            sid=store.add('sources',{'path':'paper.md'})
            cid=store.add('candidates',{'statement':'original','original_statement':'original'},sid)
            review(store,cid,'approved','测试审核者','测试意见',normalized='new text')
            self.assertEqual(store.rows('candidates')[0]['payload']['original_statement'],'original')
            self.assertEqual(state(store,cid)['verification_status'],'unknown')
            with self.assertRaises(ValueError): approve_verified(store,cid,'reviewer','not proved')
            self.assertEqual(summary(store)['formalized'],0)
            store.db.close()
            store=Store(path)
            self.assertEqual(state(store,cid)['normalized_statement'],'new text')
            self.assertEqual(len(history(store,cid)),1)
            review(store,cid,'rejected','测试审核者','拒绝说明')
            self.assertEqual(state(store,cid)['semantic_review_status'],'rejected')
            store.db.close()

    def test_additive_migration_backup(self):
        import sqlite3
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'old.sqlite'
            with sqlite3.connect(path) as db:
                db.execute('CREATE TABLE sources(id INTEGER PRIMARY KEY,payload TEXT NOT NULL)')
                db.execute('INSERT INTO sources VALUES (1,?)',(json.dumps({'original':True}),))
            db.close()
            store=Store(str(path))
            self.assertTrue(Path(str(path)+'.before-v03.bak').exists())
            self.assertEqual(store.rows('sources')[0]['payload'],{'original':True})
            store.db.close()

    def test_retrieval_declaration_provenance(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'Test.lean'
            path.write_text('/- ignored theorem bad : False -/\nnamespace Polynomial\nvariable {k : Type*} [Field k]\ntheorem derivative_fact (a : k[X]) :\n a ∣ a := by\n exact dvd_refl a\nend Polynomial\n',encoding='utf-8')
            r=search_mathlib('Polynomial.derivative_fact',tmp)[0]
            self.assertEqual(r['line'],4)
            self.assertEqual(r['namespace'],'Polynomial')
            self.assertEqual(r['match_kind'],'exact_identifier')
            self.assertEqual(r['equivalence'],'not_established')
            self.assertNotIn('bad',[x['name'] for x in declaration_index(tmp)])
            self.assertIn('k[X]',r['declaration'])

    def test_reverse_trace_filters_inferences(self):
        graph={'nodes':[{'id':1},{'id':2},{'id':3}], 'edges':[
            {'from':1,'to':2,'basis':'explicit'},{'from':3,'to':2,'basis':'rule_hypothesis'}]}
        self.assertEqual(ancestors(graph,2),{1,3})
        self.assertEqual(ancestors(graph,2,False),{1})
