"""Regression tests for the non-spoken reference sidecars."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from extract_narration import extract
from reference_metadata import HERE, load_catalog, validate_lecture


class ReferenceMetadataTest(unittest.TestCase):
    def setUp(self):
        self.catalog = load_catalog()
        self.path = next(HERE.glob('053000-*.md'))
        self.item = json.loads((HERE / 'metadata' / '053000.json').read_text(encoding='utf-8'))

    def test_reference_anchor_resolves(self):
        record = validate_lecture(self.path, self.catalog)
        self.assertEqual(len(record['historical_claims']), 1)
        self.assertTrue(record['historical_claims'][0]['start'] < record['historical_claims'][0]['end'])

    def test_sidecars_not_in_tts(self):
        original = extract(self.path)
        record = validate_lecture(self.path, self.catalog)
        self.assertEqual(original, record['narration'])
        self.assertNotIn('pending_primary_passage_comparison', original)
        self.assertNotIn('https://', original)

    def test_text_drift_is_rejected(self):
        with tempfile.TemporaryDirectory() as dirname:
            out = Path(dirname)
            meta = out / 'metadata'
            meta.mkdir()
            bad = copy.deepcopy(self.item)
            bad['historical_claims'][0]['anchor'] = 'This exact source sentence never occurs in the lecture, and should raise a validation error.'
            (meta / '053000.json').write_text(json.dumps(bad), encoding='utf-8')
            with self.assertRaisesRegex(ValueError, 'historical anchor has 0 matches'):
                validate_lecture(self.path, self.catalog, meta)

    def test_confirmation_requires_primary_evidence(self):
        with tempfile.TemporaryDirectory() as dirname:
            meta = Path(dirname) / 'metadata'
            meta.mkdir()
            bad = copy.deepcopy(self.item)
            bad['historical_claims'][0]['audit_status'] = 'primary_passage_confirmed'
            (meta / '053000.json').write_text(json.dumps(bad), encoding='utf-8')
            with self.assertRaisesRegex(ValueError, 'needs reviewer, checked_on and primary_locator'):
                validate_lecture(self.path, self.catalog, meta)

    def test_unknown_source_is_rejected(self):
        with tempfile.TemporaryDirectory() as dirname:
            out = Path(dirname)
            meta = out / 'metadata'
            meta.mkdir()
            bad = copy.deepcopy(self.item)
            bad['historical_claims'][0]['source_ids'] = ['invented-book']
            (meta / '053000.json').write_text(json.dumps(bad), encoding='utf-8')
            with self.assertRaisesRegex(ValueError, 'unknown or missing source'):
                validate_lecture(self.path, self.catalog, meta)


if __name__ == '__main__':
    unittest.main()
