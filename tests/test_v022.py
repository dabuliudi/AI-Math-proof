import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from mathlib2.pipeline import run
from mathlib2.documents import save_candidates
from mathlib2.ingest import ingest
from mathlib2.quality import assess_document, normalize
from mathlib2.store import Store
from mathlib2.metrics import evaluate
from mathlib2.structures import VERSION
from test_documents import PAPER


class V022Tests(unittest.TestCase):
    @unittest.skipUnless(PAPER.exists(),'必须使用真实论文')
    def test_actual_metrics_stability_and_version_isolation(self):
        truth = json.loads(Path('tests/fixtures/abundant-ground-truth.json').read_text(encoding='utf-8'))
        with tempfile.TemporaryDirectory() as tmp, patch.dict(os.environ,{'MATHLIB2_PROVIDER':'mock'}):
            store = Store(str(Path(tmp)/'db.sqlite'))
            try:
                source = assess_document(ingest(str(PAPER)))
                self.assertEqual(source,assess_document(ingest(str(PAPER))))
                sid = store.add('sources',{'path':str(PAPER),'sha256':source['sha256']})
                old = {'kind':'document','object_key':f'{sid}:0.2.1:old','title':'旧版图注'}
                old_id = store.add('candidates',old,sid)
                store.db.execute('INSERT INTO document_parses VALUES (?,?,?)',(sid,'0.2.1',json.dumps({'old':True})))
                store.db.commit()
                first = run(store,str(PAPER))
                doc = store.document(sid)
                candidates,graph = save_candidates(store,sid,doc)
                self.assertEqual(len(candidates),4)
                self.assertTrue(all(c['parser_version']==VERSION for c in candidates))
                self.assertEqual(store.rows('candidates')[0]['payload'],old)
                self.assertEqual(store.document(sid,'0.2.1'),{'old':True})
                self.assertNotIn(old_id,[n['id'] for n in graph['nodes']])
                second = run(store,str(PAPER))
                self.assertTrue(second['reused'])
                self.assertEqual(first['results'],second['results'])
                self.assertEqual(len(store.rows('candidates')),5)
                self.assertEqual(len(store.rows('math_objects')),39)
                metrics = evaluate(doc,candidates,graph,truth)
                self.assertEqual(metrics['formal_precision']['value'],1)
                self.assertEqual(metrics['formal_recall']['value'],1)
                self.assertEqual(metrics['condition_omission_rate']['numerator'],0)
                self.assertEqual(metrics['condition_omission_rate']['denominator'],11)
                self.assertEqual(metrics['source_traceability']['value'],1)
                self.assertEqual(metrics['caption_false_positive_rate']['numerator'],0)
                self.assertEqual(metrics['inferred_dependency_precision']['value'],1)
                self.assertEqual(metrics['unresolved_reference_recall']['value'],1)
                self.assertIsNone(metrics['explicit_dependency_precision']['value'])
                self.assertEqual(metrics['image_explicit_dependency_recall']['value'],0)
                self.assertFalse(metrics['human_reviewed'])
                for entry in truth['objects']:
                    if entry.get('original'):
                        self.assertEqual(normalize(dict(doc['pages'])[entry['page']][entry['start']:entry['end']]),entry['original'])
                for candidate in candidates:
                    self.assertEqual(candidate['verification_status'],'unknown')
                    self.assertIsNone(candidate['lean_statement'])
                    self.assertEqual(candidate['original_statement'],candidate['statement'])
                risk = next(c for c in candidates if 'If n is perfect' in c['statement'])
                evidence = risk['boundary_checks'][0]['source_evidence'][0]
                self.assertEqual(evidence['page'],9)
                self.assertEqual(dict(doc['pages'])[9][evidence['start']:evidence['end']],evidence['quote'])
                self.assertEqual(first['stages']['lean'],'not_run')
                self.assertEqual(store.rows('verified'),[])
                # 指标必须能抓到条件被删，不能恒定返回100%。
                risk['normalized_statement']=risk['normalized_statement'].replace('any k ∈ N','')
                self.assertEqual(evaluate(doc,candidates,graph,truth)['condition_omission_rate']['numerator'],1)
                with self.assertRaises(ValueError):
                    evaluate({**doc,'sha256':'wrong'},candidates,graph,truth)
            finally:
                store.db.close()

    def test_prose_reference_and_student_case_not_formal(self):
        text = 'Table 3 reports the final scoring.\n## Example 1\nA student case demonstrates a proof.'
        doc = assess_document({'pages':[(None,text)],'objects':__import__('mathlib2.structures',fromlist=['extract']).extract([(None,text)])})
        self.assertTrue(any(o['classification']=='ordinary_reference' for o in doc['objects']))
        self.assertTrue(any(o['classification']=='student_case' for o in doc['objects']))
        self.assertFalse(any(o['candidate_eligible'] for o in doc['objects']))
