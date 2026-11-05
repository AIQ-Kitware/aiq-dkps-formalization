"""Named presentation compositions of reusable Manim slide scenes."""

from __future__ import annotations

from dkvis.deck_spec import DeckSpec
from dkvis.decks.comprehensive import COMPREHENSIVE
from dkvis.decks.kitware_talk import KITWARE_TALK
from dkvis.decks.novelty import NOVELTY_TOUR
from dkvis.decks.matching import MATCHING_PROOF
from dkvis.decks.matching_talk import MATCHING_PROOF_TALK
from dkvis.decks.reference import REFERENCE_DECKS
from dkvis.decks.study import STUDY
from dkvis.decks.prerequisites import PREREQUISITES

DECKS: dict[str, DeckSpec] = {
    **REFERENCE_DECKS,
    KITWARE_TALK.name: KITWARE_TALK,
    COMPREHENSIVE.name: COMPREHENSIVE,
    NOVELTY_TOUR.name: NOVELTY_TOUR,
    MATCHING_PROOF.name: MATCHING_PROOF,
    MATCHING_PROOF_TALK.name: MATCHING_PROOF_TALK,
    STUDY.name: STUDY,
    **{deck.name: deck for deck in PREREQUISITES},
}


def get_deck(name: str) -> DeckSpec:
    try:
        return DECKS[name]
    except KeyError:
        raise KeyError(f"unknown deck {name!r}; choose from {sorted(DECKS)!r}") from None
