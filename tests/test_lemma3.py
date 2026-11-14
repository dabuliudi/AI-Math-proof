import copy
import hashlib
import json
import os
import unittest
from pathlib import Path

from pypdf import PdfReader
from mathlib2.alignment import valid_record
from mathlib2.formalization import ROOT, templates, check_template
from mathlib2.lean import ALLOWED_AXIOMS
from mathlib2.planner import validate_graph
from mathlib2.store import Store
from mathlib2.workbench import state


def report(name):
    return json.loads((ROOT / 'reports' / name).read_text(encoding='utf-8'))


class Lemma3Tests(unittest.TestCase):
    def test_scope_and_generation_provenance(self):
        t = templates()['mason_lemma3']
        self.assertEqual(t['provenance']['category'], 'New Proof')
        self.assertFalse(t['provenance']['author_code_copied'])
        self.assertFalse(t['provenance']['autonomous_reasoning_engine'])
        self.assertEqual(t['provenance']['external_ai_api_calls'], 0)
        self.assertIn('AI 生成', t['provenance']['generation_source'])
        for forbidden in ('sorry', 'admit', 'axiom ', 'CharZero', 'mathlib2_mason_lemma1', 'mathlib2_mason_lemma2'):
            self.assertNotIn(forbidden, t['source'])
        target = t['source'].split('theorem mathlib2_mason_lemma3 ')[1].split(':= by')[0]
        self.assertIn('(1 : WithBot ℕ) ≤ a.degree', target)
        self.assertIn('(1 : WithBot ℕ) ≤ (radical a).degree', target)
        self.assertNotIn('a ≠ 0', target)

    def test_actual_paper_traceability(self):
        data = report('lemma3-source.json')
        pdf = ROOT / '2408.15180v2.pdf'
        self.assertEqual(hashlib.sha256(pdf.read_bytes()).hexdigest(), data['pdf_sha256'])
        pages = PdfReader(pdf).pages
        for key in ('statement', 'proof_source'):
            section = data[key]
            text = pages[section['page'] - 1].extract_text()
            self.assertEqual(text[section['start']:section['end']], section['text'])
        self.assertEqual(data['statement']['end'], data['proof_source']['start'])
        self.assertIn('Lemma 3.', data['statement']['text'])
        self.assertIn('natDegree_radical_eq_zero_iff', data['proof_source']['text'])

    def test_multilevel_dag_and_retrieval_evidence(self):
        graph = report('lemma3-dag.json')
        order = validate_graph(graph['nodes'], graph['edges'])
        depths = {}
        for node in order:
            depths[node['id']] = max([depths[d] + 1 for d in node['depends_on']] + [0])
        self.assertEqual(max(depths.values()), graph['proof_depth'])
        self.assertEqual(graph['proof_depth'], 4)
        self.assertEqual(graph['local_proof_depth'], 3)
        self.assertEqual(len(graph['nodes']), 14)
        self.assertEqual(graph['unresolved'], [])
        for edge in graph['edges']:
            evidence = edge['evidence']
            lines = (ROOT / evidence['path']).read_text(encoding='utf-8').splitlines()
            self.assertEqual(lines[evidence['line'] - 1], evidence['quote'])
            self.assertIn(edge['from'].split('.')[-1], evidence['quote'])
            self.assertTrue(edge['used_in_lean'])
            self.assertIn(edge['origin'], ('已有 Lemma 组合', 'Mathlib 定理复用'))
        references = report('lemma3-retrieval.json')['results']
        self.assertEqual(sum(r['used'] for r in references), 9)
        for ref in references:
            path = ROOT / ref['path']
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), ref['sha256'])
            self.assertIn(ref['name'].split('.')[-1], path.read_text(encoding='utf-8').splitlines()[ref['line'] - 1])

    def test_certificate_history_costs_and_approval_gate(self):
        result = report('lemma3-result.json')
        self.assertTrue(all(result['history_preserved'].values()))
        self.assertTrue(result['final_state']['candidate_verified'])
        self.assertEqual(result['final_state']['approval_status'], 'pending')
        source = templates()['mason_lemma3']['source']
        cost = result['costs'][-1]
        expected = sum(bool(line.strip()) and not line.strip().startswith(('import ', 'open ', '#', '--')) for line in source.splitlines())
        self.assertEqual(cost['new_lean_lines'], expected)
        self.assertEqual(cost['new_intermediate_lemmas'], 4)
        self.assertEqual(cost['reused_mathlib_theorems'], 9)
        store = Store(str(ROOT / 'data/mathlib2.sqlite'))
        try:
            for cid, template in ((85, 'mason_lemma1'), (87, 'mason_lemma2'), (89, 'mason_lemma3')):
                candidate = next(row['payload'] for row in store.rows('candidates') if row['id'] == cid)
                candidate = {**candidate, 'candidate_id': cid}
                current = state(store, cid)
                self.assertTrue(valid_record(current['alignment_record'], candidate, current, template))
                changed = copy.deepcopy(current)
                changed['normalized_statement'] += ' altered'
                self.assertFalse(valid_record(current['alignment_record'], candidate, changed, template))
        finally:
            store.db.close()

    @unittest.skipUnless(os.environ.get('MATHLIB2_INTEGRATION') == '1', '需真实 Lean')
    def test_real_compile_and_all_five_axiom_audits(self):
        result = check_template('mason_lemma3')
        self.assertTrue(result['accepted'], result)
        self.assertEqual(result['returncode'], 0)
        self.assertEqual(len(result['declaration_audits']), 5)
        for audit in result['declaration_audits'].values():
            self.assertTrue(audit['accepted'])
            self.assertLessEqual(set(audit['axioms']), ALLOWED_AXIOMS)
        self.assertIn('mathlib2_mason_lemma3_nat a hnat', result['stdout'])
