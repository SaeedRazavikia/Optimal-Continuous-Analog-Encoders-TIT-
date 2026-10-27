"""Regression tests for local correspondence integrity; no paper or Lean required."""
from pathlib import Path
import copy
import hashlib
import importlib.util
import json
import tempfile
import unittest

MODULE = Path(__file__).resolve().parents[1] / 'check_correspondence.py'
spec = importlib.util.spec_from_file_location('check_correspondence', MODULE)
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class CorrespondenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / 'formalization'
        (self.root / 'Analog').mkdir(parents=True)
        self.guide = self.root.parent / 'docs' / 'STATEMENTS.md'
        self.guide.parent.mkdir()
        self.guide.write_text(
            '<a id="thm-example"></a>\n'
            '[Theorem 1](https://arxiv.org/html/2610.21536v1#Thmtheorem1)\n'
            '[Proof](https://arxiv.org/html/2610.21536v1#A1.SS1)\n'
            '[Analog.Example.result](../formalization/Analog/Example.lean)\n')
        (self.root / 'Analog' / 'Example.lean').write_text(
            'namespace Analog.Example\ntheorem result : True := by trivial\nend Analog.Example\n')
        (self.root / 'audit_targets.json').write_text(json.dumps(['Analog.Example.result']))
        excerpt = r'\begin{theorem}\label{thm:example}Example statement.\end{theorem}'
        self.catalog = {
            'schema_version': 1,
            'paper': {
                'title': 'Example paper', 'arxiv_id': '2610.21536', 'version': 'v1',
                'url': 'https://arxiv.org/abs/2610.21536v1',
                'html_url': 'https://arxiv.org/html/2610.21536v1',
            },
            'source_snapshot_sha256': '0' * 64,
            'guide': '../docs/STATEMENTS.md',
            'guide_sha256': hashlib.sha256(self.guide.read_bytes()).hexdigest(),
            'statement_count': 1,
            'statements': [{
                'label': 'thm:example', 'aliases': [], 'environment': 'theorem',
                'paper_number': 'Theorem 1',
                'statement_latex': excerpt,
                'statement_sha256': hashlib.sha256(excerpt.encode()).hexdigest(),
                'paper_statement_url': 'https://arxiv.org/html/2610.21536v1#Thmtheorem1',
                'paper_proof_url': 'https://arxiv.org/html/2610.21536v1#A1.SS1',
                'guide_anchor': 'thm-example',
                'lean_declarations': ['Analog.Example.result'],
                'lean_sources': ['Analog/Example.lean'],
                'coverage': 'complete',
            }],
        }
        self.save()

    def save(self):
        (self.root / checker.TARGET).write_text(json.dumps(self.catalog))

    def test_valid_catalog_needs_neither_paper_source_nor_network(self):
        self.assertEqual(checker.validate(self.root)['statement_count'], 1)
        self.assertFalse((self.root.parent / 'Main.tex').exists())

    def test_guide_change_rejected(self):
        self.guide.write_text(self.guide.read_text() + '\nChanged explanation.\n')
        with self.assertRaisesRegex(ValueError, 'Reading guide changed'):
            checker.validate(self.root)

    def test_excerpt_change_rejected(self):
        self.catalog['statements'][0]['statement_latex'] += '\nChanged statement.'
        self.save()
        with self.assertRaisesRegex(ValueError, 'excerpt hash mismatch'):
            checker.validate(self.root)

    def test_unrecorded_declaration_rejected(self):
        self.catalog['statements'][0]['lean_declarations'] = ['Analog.Example.missing']
        self.save()
        with self.assertRaisesRegex(ValueError, 'not audited'):
            checker.validate(self.root)

    def test_missing_declaration_source_rejected(self):
        (self.root / 'Analog' / 'Example.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'source is missing'):
            checker.validate(self.root)

    def test_wrong_source_path_rejected(self):
        self.catalog['statements'][0]['lean_sources'] = ['Analog/Wrong.lean']
        self.save()
        with self.assertRaisesRegex(ValueError, 'source paths do not match'):
            checker.validate(self.root)

    def test_duplicate_statement_rejected(self):
        self.catalog['statements'].append(copy.deepcopy(self.catalog['statements'][0]))
        self.catalog['statement_count'] = 2
        self.save()
        with self.assertRaisesRegex(ValueError, 'Duplicate statement label'):
            checker.validate(self.root)

    def test_inconsistent_arxiv_version_rejected(self):
        self.catalog['paper']['url'] = 'https://arxiv.org/abs/2610.21536v2'
        self.save()
        with self.assertRaisesRegex(ValueError, 'URLs must match'):
            checker.validate(self.root)

    def test_wrong_proof_url_rejected(self):
        self.catalog['statements'][0]['paper_proof_url'] = 'https://arxiv.org/html/2610.21536v2#A1.SS1'
        self.save()
        with self.assertRaisesRegex(ValueError, 'recorded arXiv version'):
            checker.validate(self.root)

    def test_inconsistent_count_rejected(self):
        self.catalog['statement_count'] = 2
        self.save()
        with self.assertRaisesRegex(ValueError, 'Statement count mismatch'):
            checker.validate(self.root)

    def test_update_refreshes_hashes_after_structural_validation(self):
        self.guide.write_text(self.guide.read_text() + '\nReviewed explanation.\n')
        self.catalog['statements'][0]['statement_latex'] += '\n'
        self.save()
        before = copy.deepcopy(self.catalog)
        updated = checker.validate(self.root, update=True)
        self.assertNotEqual(updated['guide_sha256'], before['guide_sha256'])
        self.assertNotEqual(updated['statements'][0]['statement_sha256'],
                            before['statements'][0]['statement_sha256'])
        checker.validate(self.root)

    def test_update_rejects_broken_mapping_without_writing(self):
        self.catalog['statements'][0]['lean_sources'] = ['Analog/Wrong.lean']
        self.save()
        target = self.root / checker.TARGET
        before = target.read_bytes()
        with self.assertRaisesRegex(ValueError, 'source paths do not match'):
            checker.validate(self.root, update=True)
        self.assertEqual(target.read_bytes(), before)

    def test_update_rejects_missing_guide_anchor(self):
        self.guide.write_text(self.guide.read_text().replace('id="thm-example"', 'id="wrong"'))
        with self.assertRaisesRegex(ValueError, 'Missing or duplicate guide anchor'):
            checker.validate(self.root, update=True)

    def test_update_rejects_missing_lean_link(self):
        self.guide.write_text(self.guide.read_text().replace(
            '../formalization/Analog/Example.lean', 'https://example.org/source'))
        with self.assertRaisesRegex(ValueError, 'does not link Lean source'):
            checker.validate(self.root, update=True)

    def test_update_rejects_missing_paper_link(self):
        self.guide.write_text(self.guide.read_text().replace(
            '[Proof](https://arxiv.org/html/2610.21536v1#A1.SS1)', 'Proof omitted'))
        with self.assertRaisesRegex(ValueError, 'does not link paper_proof_url'):
            checker.validate(self.root, update=True)


if __name__ == '__main__':
    unittest.main()
