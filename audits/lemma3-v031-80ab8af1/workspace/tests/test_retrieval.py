import tempfile
import unittest
from pathlib import Path
from mathlib2.retrieval import search
from mathlib2.provider import HTTPProvider
from unittest.mock import patch
import os


class RetrievalTests(unittest.TestCase):
    def test_source_location(self):
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / 'Basic.lean'
            p.write_text('-- comment\ntheorem add_zero : True := by trivial\n', encoding='utf-8')
            result = search('add_zero', tmp)
            self.assertEqual(result[0]['line'], 2)
            self.assertEqual(result[0]['path'], str(p.resolve()))

    def test_provider_requires_explicit_endpoint(self):
        with patch.dict(os.environ, {'MATHLIB2_API_URL': ''}):
            with self.assertRaises(ValueError):
                HTTPProvider().generate('text', 1)
