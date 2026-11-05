"""Compatibility API for the original matching transcript workflow.

New lessons use dkvis.presentation.narration and declare their transcript in
DeckSpec, rather than giving the shared reader a topic-specific default.
"""
import sys

from dkvis.decks.matching import SCENES
from dkvis.presentation.narration import (
    Narration, export as _export, main, read_deck_narration as _read_deck_narration,
    read_narration as _read_narration,
)
from dkvis.presentation.paths import ROOT

from dkvis.lectures import lecture_path

SOURCE = ROOT / lecture_path('matching_study')


def read_narration(path=SOURCE, *, scenes=SCENES):
    return _read_narration(path, scenes=scenes)


def read_deck_narration(deck_name='matching-proof'):
    return _read_deck_narration(deck_name)


def export(out, *, theme='dark', deck_name='matching-proof'):
    return _export(out, theme=theme, deck_name=deck_name)


if __name__ == '__main__':
    main(['--deck', 'matching-proof', *sys.argv[1:]])
