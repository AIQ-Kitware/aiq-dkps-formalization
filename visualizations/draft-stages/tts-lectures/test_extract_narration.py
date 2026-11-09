"""Tests for the source-Markdown-to-speech extraction boundary."""
from pathlib import Path
import tempfile
import unittest

from extract_narration import extract


class NarrationExtractionTest(unittest.TestCase):
    def test_headings_and_emphasis_not_spoken(self):
        text = ("# Title\n<!-- BEGIN SPOKEN LECTURE -->\n"
                "## Principle\nA *short* and **precise** explanation.\n"
                "**Definition:** An *operator*.\n"
                "<!-- END SPOKEN LECTURE -->\n## Appendix\n"
                "**Unspoken source note**\n")
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'lesson.md'
            path.write_text(text)
            spoken = extract(path)
        self.assertIn('Principle\nA short and precise explanation.', spoken)
        self.assertIn('Definition: An operator.', spoken)
        self.assertNotIn('*', spoken)
        self.assertNotIn('Appendix', spoken)

    def test_plain_asterisk_math_is_not_deleted(self):
        text = ('<!-- BEGIN SPOKEN LECTURE -->\n'
                'In a displayed comment: a * b means product.\n'
                '<!-- END SPOKEN LECTURE -->')
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'math.md'
            path.write_text(text)
            spoken = extract(path)
        self.assertIn('a * b', spoken)

    def test_raw_math_markers_rejected(self):
        text = ('<!-- BEGIN SPOKEN LECTURE -->\n'
                'Unsupported $${x+y}$$ notation\n'
                '<!-- END SPOKEN LECTURE -->')
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / 'math.md'
            path.write_text(text)
            with self.assertRaisesRegex(ValueError, 'non-spoken markup'):
                extract(path)


if __name__ == '__main__':
    unittest.main()
