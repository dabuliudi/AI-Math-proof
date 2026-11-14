import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from mathlib2.ingest import ingest
from mathlib2.lean import accepted, valid_statement, LeanWorker
from mathlib2.planner import topological
from mathlib2.provider import MockProvider
from mathlib2.store import Store
from mathlib2.pipeline import run


class CoreTests(unittest.TestCase):
    def test_axiom_gate(self):
        self.assertEqual(accepted("'x' depends on axioms: [propext, Classical.choice, Quot.sound]", 'x', 0)[0], True)
        for output, code in [("'x' depends on axioms: [sorryAx]", 0),
                             ("'x' depends on axioms: [custom]", 0),
                             ("'y' does not depend on any axioms", 0),
                             ("'x' does not depend on any axioms", 1), ('', 0)]:
            self.assertFalse(accepted(output, 'x', code)[0])

    def test_injection_rejected(self):
        self.assertTrue(valid_statement('∀ n : Nat, n + 0 = n'))
        for s in ['True', '∀ n : Nat, n = n\naxiom bad : False', '∀ n : Nat, n = n -- comment', '∀ n : Nat, n = n := by sorry']:
            self.assertFalse(valid_statement(s))

    def test_dag(self):
        self.assertEqual([x['id'] for x in topological([{'id': 1, 'depends_on': [0]}, {'id': 0, 'depends_on': []}])], [0, 1])
        for nodes in [[{'id': 0, 'depends_on': [0]}], [{'id': 0, 'depends_on': [2]}]]:
            with self.assertRaises(ValueError):
                topological(nodes)

    def test_trace(self):
        doc = ingest('samples/nat.md')
        self.assertEqual(len(doc['objects']), 4)
        text = doc['pages'][0][1]
        for obj in doc['objects']:
            self.assertEqual(text[obj['start']:obj['end']], obj['text'])
        self.assertEqual(len(ingest('samples/nat.tex')['objects']), 2)
        self.assertEqual(MockProvider().generate('任意研究论文', 4), [])

    def test_missing_lean_is_unknown_and_persistent(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = str(Path(tmp) / 'db.sqlite')
            store = Store(path)
            worker = LeanWorker()
            worker.lake = None
            with patch.dict(os.environ, {'MATHLIB2_PROVIDER': 'mock'}):
                result = run(store, 'samples/nat.md', worker=worker)
            self.assertEqual([r['status'] for r in result['results']], ['unknown'] * 4)
            with self.assertRaises(ValueError):
                store.approve(1, '审核者', '意见')
            reopened = Store(path)
            self.assertEqual(len(reopened.rows('candidates')), 4)
            reopened.db.close()
            self.assertEqual({e['role'] for e in store.rows('events')},
                             {'conjecture_generation', 'planning', 'proving', 'counterexample_search', 'evaluation'})
            store.db.close()

    def test_evaluation_policy(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = Store(str(Path(tmp) / 'db.sqlite'))
            cid = store.add('candidates', {})
            for p, r, status in [(False, False, 'unknown'), (False, True, 'refuted'), (True, False, 'proved'), (True, True, 'unknown')]:
                self.assertEqual(store.finish(cid, {'accepted': p}, {'accepted': r}), status)
            store.db.close()


@unittest.skipUnless(os.environ.get('MATHLIB2_INTEGRATION') == '1', '需真实 Lean/Mathlib；设置 MATHLIB2_INTEGRATION=1')
class LeanIntegration(unittest.TestCase):
    def test_real_roundtrip(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = Store(str(Path(tmp) / 'db.sqlite'))
            try:
                result = run(store, 'samples/nat.md')
                self.assertEqual([r['status'] for r in result['results']], ['proved', 'proved', 'refuted', 'unknown'])
                store.approve(result['results'][0]['id'], '集成测试', '教学原文与形式化一致')
                self.assertEqual(len(store.rows('verified')), 1)
            finally:
                store.db.close()


if __name__ == '__main__':
    unittest.main()
