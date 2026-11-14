import hashlib
import json
import os
import sqlite3
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from pypdf import PdfWriter
from pypdf.generic import DictionaryObject, NameObject, DecodedStreamObject
from mathlib2.ingest import ingest
from mathlib2.store import Store
from mathlib2.pipeline import run
from mathlib2.candidate import view
from mathlib2.planner import document_graph, validate_graph

PAPER = Path(os.environ.get('MATHLIB2_PAPER', 'data/uploads/0357be8b67904937aa2d2491b7f8f0f2.pdf'))


def text_pdf(path, text):
    writer = PdfWriter()
    page = writer.add_blank_page(500, 700)
    font = DictionaryObject({NameObject('/Type'):NameObject('/Font'), NameObject('/Subtype'):NameObject('/Type1'), NameObject('/BaseFont'):NameObject('/Helvetica')})
    page[NameObject('/Resources')] = DictionaryObject({NameObject('/Font'):DictionaryObject({NameObject('/F1'):writer._add_object(font)})})
    stream = DecodedStreamObject()
    stream.set_data(('BT /F1 12 Tf 40 600 Td ('+text+') Tj ET').encode())
    page[NameObject('/Contents')] = writer._add_object(stream)
    writer.write(path)


class DocumentTests(unittest.TestCase):
    def test_plain_pdf_and_corrupt(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/'ordinary.pdf'
            text_pdf(path, 'This is an ordinary meeting announcement. Theorem proving is discussed.')
            doc = ingest(str(path))
            self.assertEqual(doc['stages']['text'], 'parsed')
            self.assertEqual(doc['objects'], [])
            path.write_bytes(b'not a pdf')
            self.assertEqual(ingest(str(path))['stages']['text'], 'failed')

    def test_image_only_pdf(self):
        from PIL import Image, ImageDraw
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/'scan.pdf'
            image = Image.new('RGB',(400,300),'white')
            ImageDraw.Draw(image).text((20,20), 'Theorem 1. This text is an image.', fill='black')
            image.save(path, 'PDF')
            result = ingest(str(path))
            self.assertEqual(result['stages']['text'], 'needs_ocr')
            self.assertEqual(result['objects'], [])

    def test_dedup_and_migration(self):
        with tempfile.TemporaryDirectory() as tmp:
            dbpath = Path(tmp)/'db.sqlite'
            old = sqlite3.connect(dbpath)
            old.executescript("CREATE TABLE candidates(id INTEGER PRIMARY KEY, source_id INTEGER, payload TEXT NOT NULL, status TEXT NOT NULL DEFAULT 'unknown'); INSERT INTO candidates VALUES (1,1,'{}','unknown');")
            old.close()
            store = Store(str(dbpath))
            try:
                path = Path(tmp)/'paper.md'
                path.write_text('## Theorem 1\nFor every n, n=n.', encoding='utf-8')
                with patch.dict(os.environ, {'MATHLIB2_PROVIDER':'mock'}):
                    first = run(store,str(path))
                    with patch('mathlib2.documents.ingest', side_effect=AssertionError('不应重新解析')):
                        second = run(store,str(path))
                self.assertEqual(first['source_id'], second['source_id'])
                self.assertTrue(second['reused'])
                self.assertEqual(len(store.rows('sources')), 1)
                self.assertEqual(len(store.rows('math_objects')), 1)
                self.assertEqual(len(store.rows('candidates')), 2)  # 原记录保留
                self.assertEqual(store.rows('candidates')[0]['payload'], {})
                cid = first['results'][0]['id']
                with self.assertRaises(ValueError):
                    store.approve(cid,'审查者','提取成功不能批准')
                c = view(store.rows('candidates')[-1])
                self.assertEqual((c['stage'],c['verification_status']), ('Candidate','unknown'))
            finally:
                store.db.close()

    def test_graph_evidence_and_cycles(self):
        def c(i,title,statement):
            return dict(candidate_id=i,source_id=1,title=title,statement=statement,location={'page':1},object_type='Lemma')
        nodes = [c(1,'Lemma 1','x=x'),c(2,'Theorem 2','By Lemma 1, x=x.')]
        graph = document_graph(nodes)
        self.assertEqual(len(graph['edges']),1)
        self.assertEqual(graph['edges'][0]['basis'],'explicit')
        proof_graph = document_graph([c(1,'Lemma 1','x=x'),c(2,'Theorem 2','x=x'),c(3,'Proof of Theorem 2','By Lemma 1, x=x.')])
        self.assertEqual(proof_graph['edges'][0]['to'],2)
        self.assertEqual(proof_graph['associations'][0]['proof'],3)
        self.assertEqual(document_graph([c(1,'Lemma 1','x=x'),c(2,'Theorem 2','x=x')])['edges'],[])
        with self.assertRaises(ValueError):
            validate_graph(graph['nodes'], [{'from':1,'to':2,'basis':'ai_hypothesis'}, {'from':2,'to':1,'basis':'explicit'}])
        with self.assertRaises(ValueError):
            validate_graph(graph['nodes'], [{'from':1,'to':3,'basis':'explicit'}])

    @unittest.skipUnless(PAPER.exists(), '原始论文不存在；设置 MATHLIB2_PAPER，禁止使用模拟论文代替')
    def test_actual_paper(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = Store(str(Path(tmp)/'paper.sqlite'))
            try:
                with patch.dict(os.environ, {'MATHLIB2_PROVIDER':'mock'}):
                    result = run(store,str(PAPER))
                doc = store.document(result['source_id'])
                self.assertEqual(len(doc['pages']),30)
                self.assertEqual(doc['sha256'],hashlib.sha256(PAPER.read_bytes()).hexdigest())
                self.assertTrue(result['results'])
                definitions = [o for o in doc['objects'] if o['object_type']=='Definition' and o['page']==28]
                self.assertTrue(any('A perfect number' in o['text'] for o in definitions))
                self.assertTrue(any('An abundant number' in o['text'] for o in definitions))
                task = next(o for o in doc['objects'] if '(a) If n is perfect' in o['text'])
                self.assertEqual(task['page'],28)
                self.assertIn('any k ∈ N',task['text'])
                self.assertNotIn('k > 1',task['text'])
                self.assertTrue(any(o['page']==9 and 'k> 1' in o['text'] for o in doc['objects']))
                self.assertTrue(any(o['extraction_method']=='narrative_proof_step' for o in doc['objects']))
                step_object = next(o for o in doc['objects'] if o['extraction_method']=='narrative_proof_step')
                self.assertGreaterEqual(len(step_object['proof_steps']),2)
                pages = dict(doc['pages'])
                for obj in doc['objects']:
                    self.assertEqual(pages[obj['page']][obj['start']:obj['end']],obj['original_text'])
                    self.assertEqual(obj['source_id'],result['source_id'])
                    for step in obj.get('proof_steps',[]):
                        self.assertEqual(pages[step['page']][step['start']:step['end']],step['text'])
                self.assertTrue(all(r['status']=='unknown' for r in result['results']))
                self.assertEqual([e for e in result['dag']['edges'] if e['basis']=='explicit'],[])
                self.assertEqual(len(result['dag']['edges']),3)
                self.assertTrue(all(e['basis']=='rule_hypothesis' for e in result['dag']['edges']))
                self.assertTrue(any(x['reference']=='Lemma 3' for x in result['dag']['unresolved']))
                self.assertEqual(store.rows('verified'),[])
            finally:
                store.db.close()
