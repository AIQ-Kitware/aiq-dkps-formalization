"""Numbered narrated edition of the preserved short sine-theta reference talk."""
from dkvis.deck_spec import DeckSpec,uses
from dkvis.decks.reference import SHORT
from dkvis.lectures import lecture_path
from dkvis.quiz import quiz_uses

SINE_THETA_LECTURE=DeckSpec(
    name='sine-theta-lecture',
    description='The short sine-theta visuals with authored narration and study questions.',
    footer='Davis–Kahan sine theta: residuals and spectral separation',
    narration=lecture_path('sine_theta'),
    slides=uses('dkvis.learning.sine_theta.scenes',SHORT.scene_names)+quiz_uses(),
)
