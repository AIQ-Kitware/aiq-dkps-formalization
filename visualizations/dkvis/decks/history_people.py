"""Two independently narrated introductions to the people behind the subject."""
from dkvis.deck_spec import DeckSpec,uses
from dkvis.lectures import lecture_path
from dkvis.quiz import quiz_uses

PEOPLE_FOUNDATIONS=DeckSpec(
    name='history-people-foundations',description='Portraits and lives of Sylvester, Jordan, Rayleigh, Ritz, and Weyl.',
    footer='People behind the mathematics: geometry, sound, approximation',
    narration=lecture_path('history_people_foundations'),
    slides=uses('dkvis.learning.history_people.scenes',[
        'PfTitle','PfIntro','PfSylvester','PfJordan','PfRayleigh','PfRitz','PfWeyl',
        'PfConnections','PfSummary','PfCreditsOne','PfCreditsTwo'])+quiz_uses(),
)
PEOPLE_OPERATORS=DeckSpec(
    name='history-people-operators',description='Portraits and lives of Sz.-Nagy, Halmos, Kato, Davis, and Kahan.',
    footer='People behind the mathematics: operators and reliable computation',
    narration=lecture_path('history_people_operators'),
    slides=uses('dkvis.learning.history_people.scenes',[
        'PoTitle','PoIntro','PoSznagy','PoHalmos','PoKato','PoDavis','PoKahan',
        'PoConnections','PoSummary','PoCreditsOne','PoCreditsTwo'])+quiz_uses(),
)
