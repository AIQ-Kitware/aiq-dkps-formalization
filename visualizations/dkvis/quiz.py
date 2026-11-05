"""Authored multiple-choice questions shared by slides, speech and video timing."""
import yaml

from dkvis.deck_spec import uses
from dkvis.lectures import lecture_path, load_index
from dkvis.presentation.paths import ROOT

SCENES = ('ReviewQuestion1', 'ReviewQuestion2')


def questions(deck):
    key = next((k for k, row in load_index().items() if row['deck'] == deck), None)
    if key is None:
        return []
    path = (ROOT/lecture_path(key)).with_name('quiz.yaml')
    if not path.exists():
        return []
    rows = yaml.safe_load(path.read_text())['questions']
    if len(rows) != len(SCENES):
        raise ValueError(f'{path}: author exactly {len(SCENES)} review questions')
    for row in rows:
        if not 3 <= len(row['choices']) <= 4 or not 0 <= row['correct'] < len(row['choices']):
            raise ValueError(f'{path}: invalid choices or correct-answer index')
        if not 0 <= row.get('think_seconds', 8) <= 60:
            raise ValueError(f'{path}: thinking time must be between 0 and 60 seconds')
    return rows


def quiz_uses():
    return uses('dkvis.learning.review.scenes', SCENES)
