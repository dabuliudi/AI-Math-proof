import json
import os
import unittest
from pathlib import Path
from mathlib2.formalization import SOURCE,templates,check_template
from mathlib2.planner import validate_graph


class Lemma2Tests(unittest.TestCase):
    def test_independent_construction_and_scope(self):
        t=templates()['mason_lemma2']
        self.assertTrue(t['source'].startswith(SOURCE))
        self.assertEqual(t['provenance']['category'],'New Proof')
        self.assertFalse(t['provenance']['author_code_copied'])
        self.assertIn('ha : a ≠ 0',t['source'])
        for forbidden in ('sorry','admit','axiom ','divRadical_dvd_wronskian_left','divRadical_dvd_wronskian_right','CharZero','b ≠ 0','IsCoprime'):
            self.assertNotIn(forbidden,t['source'])
        self.assertIn('u * r - v * s',t['source'])
        self.assertIn('(mathlib2_mason_lemma1 a ha)',t['source'])

    def test_real_dag_evidence_and_history(self):
        path=Path('reports/lemma2-result.json')
        if not path.exists(): self.skipTest('先运行真实Lemma2实验')
        data=json.loads(path.read_text(encoding='utf-8'))
        self.assertTrue(all(data['history_preserved'].values()))
        self.assertEqual(data['final_state']['approval_status'],'pending')
        graph=data['dag']; validate_graph(graph['nodes'],graph['edges'])
        for e in graph['edges']:
            evidence=e['evidence']; lines=Path(evidence['path']).read_text(encoding='utf-8').splitlines()
            self.assertEqual(lines[evidence['line']-1],evidence['quote'])
            self.assertTrue(evidence['quote'].strip())
            if e['edge_type']=='Proof Dependency': self.assertIn(e['from'].split('.')[-1],evidence['quote'])
        self.assertTrue(data['compile']['accepted'])
        self.assertTrue(data['final_state']['candidate_verified'])

    @unittest.skipUnless(os.environ.get('MATHLIB2_INTEGRATION')=='1','需真实Lean')
    def test_real_compile_all_declarations(self):
        result=check_template('mason_lemma2')
        self.assertTrue(result['accepted'],result)
        audits=result['declaration_audits']
        self.assertEqual(len(audits),4)
        self.assertTrue(all(a['accepted'] for a in audits.values()))
        self.assertEqual(audits['mathlib2_dvd_linear_combination']['axioms'],[])
        self.assertIn('mathlib2_dvd_linear_combination (mathlib2_quotient_dvd_self a)',result['stdout'])
