"""Named presentation compositions of reusable Manim slide scenes."""

from __future__ import annotations

from dkvis.deck_spec import DeckSpec
from dkvis.decks.comprehensive import COMPREHENSIVE
from dkvis.decks.kitware_talk import KITWARE_TALK
from dkvis.decks.reference import REFERENCE_DECKS
from dkvis.decks.study import STUDY

DECKS: dict[str, DeckSpec] = {
    **REFERENCE_DECKS,
    KITWARE_TALK.name: KITWARE_TALK,
    COMPREHENSIVE.name: COMPREHENSIVE,
    STUDY.name: STUDY,
}


def get_deck(name: str) -> DeckSpec:
    try:
        return DECKS[name]
    except KeyError:
        raise KeyError(f"unknown deck {name!r}; choose from {sorted(DECKS)!r}") from None
