import unittest
from mathlib2.structures import extract_page
from mathlib2.ingest import ingest


class StructureTests(unittest.TestCase):
    def test_eight_types_and_offsets(self):
        text = '\n\n'.join(f'{k} {i}. Test statement.\nBody.' for i,k in enumerate(
            ['Definition','Theorem','Lemma','Proposition','Corollary','Proof','Example','Conjecture'],1))
        objs = extract_page(text, 3)
        self.assertEqual(len(objs), 8)
        for obj in objs:
            self.assertEqual(text[obj['start']:obj['end']], obj['original_text'])
            self.assertEqual(obj['page'], 3)

    def test_prose_not_theorems(self):
        text = 'Theorem proving is a research topic.\nWe discuss Lemma 2 in this paper.\nDefinition Given [DEF-GIV]\nThis is called the interview output.'
        self.assertEqual(extract_page(text, 1), [])

    def test_uncertain_heading(self):
        self.assertEqual(extract_page('Theorem:\nSomething incomplete', 1)[0]['recognition_status'], 'uncertain')

    def test_proof_and_latex(self):
        objs = extract_page('Theorem 1.1. Let x = x.\n\nProof of Theorem 1.1. By Lemma 2.\n\nLemma 2. x=x.', 1)
        self.assertEqual([o['object_type'] for o in objs], ['Theorem','Proof','Lemma'])
        self.assertEqual(len(ingest('samples/nat.tex')['objects']), 2)

    def test_task_is_not_theorem(self):
        text = 'Tasks:\n(a) If n is perfect, then kn is abundant for any k ∈ N.\n(b) If p is prime, then p is odd.'
        objs = extract_page(text, 28)
        self.assertEqual(len(objs), 2)
        self.assertTrue(all(o['object_type'] == 'Conjecture' for o in objs))
        self.assertIn('any k ∈ N', objs[0]['original_text'])
