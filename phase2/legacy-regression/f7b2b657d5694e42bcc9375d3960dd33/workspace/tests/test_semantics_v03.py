import json
import tempfile
import unittest
from pathlib import Path
from mathlib2.structures import extract, VERSION
from mathlib2.quality import assess_document
from mathlib2.ingest import ingest
from mathlib2.documents import process_document, save_candidates
from mathlib2.store import Store

ROOT=Path(__file__).resolve().parents[1]


class SemanticV03Tests(unittest.TestCase):
    def test_code_and_proof_separation(self):
        text='Lemma 1. For all x, x=x.\nProof. Reflexivity.\n\ntheorem refl_test (x : Nat) : x=x := by rfl\n\ntheorem in Isabelle is discussed.'
        objects=extract([(1,text)])
        lemma=next(o for o in objects if o['object_type']=='Lemma')
        self.assertNotIn('Proof.',lemma['statement_text'])
        self.assertEqual(sum(o['object_type']=='Code' for o in objects),1)
        self.assertTrue(next(o for o in objects if o['object_type']=='Proof')['proof_body'])
        for o in objects:
            self.assertEqual(text[o['start']:o['end']],o['original_text'])

    def test_semantic_fields_and_arithmetic_boundary(self):
        text='## Conjecture 1\nIf p1 and p2 are primes, then p1p2 is abundant.'
        doc=assess_document({'pages':[(1,text)],'objects':extract([(1,text)])})
        o=doc['objects'][0]
        self.assertEqual(o['potential_counterexamples'][0]['value'],'p1=p2=2')
        self.assertEqual(o['original_statement'],text)
        self.assertEqual(o['review_status'],'pending')
        self.assertIsNone(o['lean_statement'])
        for field in ('assumptions','quantifiers','domain_constraints','definitions','boundary_cases'):
            self.assertIsInstance(o[field],list)

    def test_both_real_papers(self):
        cases=[('s40753-021-00140-1.pdf',4),('2408.15180v2.pdf',16)]
        for filename, expected in cases:
            path=ROOT/filename
            self.assertTrue(path.exists(),'真实回归PDF缺失，不能模拟替代')
            doc=assess_document(ingest(str(path)))
            self.assertEqual(doc['quality_summary']['candidate_count'],expected)
            self.assertEqual(doc['quality_summary']['formalized_count'],0)
            self.assertEqual(doc['quality_summary']['uncertain'],sum(o['recognition_status']=='uncertain' for o in doc['objects']))
            for o in doc['objects']:
                self.assertEqual(dict(doc['pages'])[o['page']][o['start']:o['end']],o['original_text'])
            self.assertEqual(doc,assess_document(ingest(str(path))))
            if filename.startswith('2408'):
                lemma=next(o for o in doc['objects'] if o['title'].startswith('Lemma 1.'))
                self.assertEqual(lemma['page'],4)
                self.assertNotIn('Proof.',lemma['statement_text'])
                self.assertIn('polynomial a',lemma['normalized_statement'])
                self.assertTrue(lemma['normalization_changes'])
                self.assertNotIn('characteristic=0',lemma['normalized_statement'])
                self.assertTrue(any(o['object_type']=='Code' and 'divRadical_dvd_derivative' in o['text'] for o in doc['objects']))
            else:
                risks=[o for o in doc['objects'] if o.get('candidate_eligible') and o['semantic_status']=='potential_counterexample']
                self.assertEqual(len(risks),2)

    def test_repeat_does_not_overwrite_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            path=Path(tmp)/'paper.md'; path.write_text('## Lemma 1\nFor every n, n=n.',encoding='utf-8')
            store=Store(str(Path(tmp)/'db.sqlite'))
            try:
                sid,doc,_=process_document(store,path)
                candidates,_=save_candidates(store,sid,doc)
                row=store.rows('candidates')[0]; p=row['payload']
                p.update(normalized_statement='Edited by reviewer',semantic_review_status='approved')
                store.db.execute('UPDATE candidates SET payload=? WHERE id=?',(json.dumps(p),row['id']))
                store.db.commit()
                save_candidates(store,sid,doc)
                updated=store.rows('candidates')[0]['payload']
                self.assertEqual(updated['normalized_statement'],'Edited by reviewer')
                self.assertEqual(updated['semantic_review_status'],'approved')
                self.assertEqual(updated['parser_version'],VERSION)
            finally:
                store.db.close()
