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
from dkvis.decks.operators import OPERATORS
from dkvis.decks.sine_theta_lecture import SINE_THETA_LECTURE
from dkvis.decks.history import HISTORY_OVERVIEW
from dkvis.decks.yws import YWS
from dkvis.decks.pvm import PVM
from dkvis.decks.history_people import PEOPLE_FOUNDATIONS,PEOPLE_OPERATORS

DECKS: dict[str, DeckSpec] = {
    **REFERENCE_DECKS,
    KITWARE_TALK.name: KITWARE_TALK,
    COMPREHENSIVE.name: COMPREHENSIVE,
    NOVELTY_TOUR.name: NOVELTY_TOUR,
    MATCHING_PROOF.name: MATCHING_PROOF,
    MATCHING_PROOF_TALK.name: MATCHING_PROOF_TALK,
    STUDY.name: STUDY,
    SINE_THETA_LECTURE.name: SINE_THETA_LECTURE,
    HISTORY_OVERVIEW.name: HISTORY_OVERVIEW,
    YWS.name: YWS,
    PVM.name: PVM,
    PEOPLE_FOUNDATIONS.name: PEOPLE_FOUNDATIONS,
    PEOPLE_OPERATORS.name: PEOPLE_OPERATORS,
    **{deck.name: deck for deck in PREREQUISITES},
    **{deck.name: deck for deck in OPERATORS},
}


def get_deck(name: str) -> DeckSpec:
    try:
        return DECKS[name]
    except KeyError:
        raise KeyError(f"unknown deck {name!r}; choose from {sorted(DECKS)!r}") from None
