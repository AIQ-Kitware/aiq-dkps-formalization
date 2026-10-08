"""Deck registry.

Scene implementations live outside this package.  Decks only compose them.
"""

from __future__ import annotations

from dkvis.deck_spec import DeckSpec
from dkvis.decks.friday import FRIDAY
from dkvis.decks.reference import REFERENCE_DECKS
from dkvis.decks.study import STUDY

DECKS: dict[str, DeckSpec] = {
    **REFERENCE_DECKS,
    FRIDAY.name: FRIDAY,
    STUDY.name: STUDY,
}


def get_deck(name: str) -> DeckSpec:
    try:
        return DECKS[name]
    except KeyError:
        raise KeyError(f"unknown deck {name!r}; choose from {sorted(DECKS)!r}") from None
