import unittest
from mathlib2.quality import assess_document, normalize
from mathlib2.structures import extract
from mathlib2.candidate import from_object
from mathlib2.planner import document_graph


def assessed(text):
    return assess_document({'pages':[(1,text)],'objects':extract([(1,text)])})


class QualityTests(unittest.TestCase):
    def test_filter_preserves_materials_and_unrelated_exercise(self):
        text = ('An abundant number is an integer n whose divisors add up to more than 2n.\n'
                'A perfect number is an integer n whose divisors add up to exactly 2n.\n'
                'Tasks:\n(a) If n is perfect, then kn is abundant for any k ∈ N.\n'
                '(b) If p1 and p2 are primes, then p1p2 is abundant.\n'
                '1. Prove that 2 + 2 = 4.\n\nFig. 1 Student proof\nTable 2 Scores\n')
        doc = assessed(text)
        self.assertEqual(doc['research_focus'],'abundant_numbers')
        rejected = [o for o in doc['objects'] if not o['candidate_eligible']]
        self.assertTrue(any(o['classification']=='caption' for o in rejected))
        self.assertTrue(any(o['classification']=='out_of_scope' for o in rejected))
        for o in doc['objects']:
            self.assertEqual(text[o['start']:o['end']],o['original_text'])

    def test_semantic_boundary_keeps_original_and_strictness(self):
        text = '## Conjecture 1\nIf n is perfect, then kn is abundant for any k ∈ N.'
        obj = assessed(text)['objects'][0]
        self.assertEqual(obj['semantic_status'],'potential_counterexample')
        self.assertEqual(obj['original_statement'],text)
        self.assertEqual(obj['normalized_statement'],normalize(text))
        self.assertIsNone(obj['lean_statement'])
        self.assertNotIn('k > 1',obj['normalized_statement'])
        self.assertIn('k > 1',obj['proposed_corrections'][0]['statement'])
        obj.update(object_key='x',source_id=1)
        candidate = from_object(obj,1)
        self.assertEqual(candidate['verification_status'],'unknown')
        self.assertEqual(candidate['formalization_status'],'not_formalized')
        for condition in ('k > 1','k ≥ 2','k >= 2'):
            checked = assessed(text+' Assume '+condition+'.')['objects'][0]
            self.assertNotEqual(checked['semantic_status'],'potential_counterexample')
        # 非严格 k ≥ 1 不能排除反例。
        checked = assessed(text+' Assume k ≥ 1.')['objects'][0]
        self.assertEqual(checked['semantic_status'],'potential_counterexample')

    def test_general_document_and_uncertainty(self):
        doc = assessed('## Theorem 1\nFor all x ∈ R, x ≤ x.\n\nTheorem: unclear\n')
        self.assertEqual(doc['research_focus'],'general')
        self.assertTrue(doc['objects'][0]['candidate_eligible'])
        self.assertEqual(doc['objects'][0]['normalized_statement'],'## Theorem 1 For all x ∈ R, x ≤ x.')
        self.assertEqual(doc['objects'][1]['quality_tier'],'Low Confidence')
        self.assertFalse(doc['objects'][1]['candidate_eligible'])

    def test_dependency_categories_and_duplicates(self):
        def c(i,title,statement,kind='Lemma'):
            return dict(candidate_id=i,source_id=1,title=title,statement=statement,
                        object_type=kind,location={'page':1,'start':0})
        nodes = [c(1,'## lemma 1','x=x'), c(2,'## Theorem 2','Apply Lemma 1. According to Proposition 7, x=x.')]
        graph = document_graph(nodes)
        self.assertEqual(graph['edges'][0]['dependency_type'],'Explicit Dependency')
        self.assertEqual(graph['unresolved'][0]['dependency_type'],'Unresolved Reference')
        # 同编号声明不唯一，不能随机选一个。
        self.assertEqual(document_graph(nodes+[c(3,'Lemma 1','y=y')])['edges'],[])
        inferred = document_graph([c(1,'Definition','A perfect number is an integer n.','Definition'),
                                   c(2,'Theorem 2','If n is perfect, x=x.','Theorem')])
        self.assertEqual(inferred['edges'][0]['dependency_type'],'Inferred Dependency')
        self.assertEqual(inferred['edges'][0]['status'],'uncertain')
        self.assertEqual(document_graph([c(1,'Lemma 1','x=x'),c(2,'Theorem 2','x=x')])['edges'],[])
