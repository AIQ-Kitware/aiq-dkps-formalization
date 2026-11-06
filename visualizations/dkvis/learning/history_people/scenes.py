"""Two standalone biographical episodes with attributed, proportionally shown portraits."""
from pathlib import Path
import yaml
from manim import DOWN, VGroup
from dkvis.components.lesson import LessonSlide, LessonTitle, stack
from dkvis.components.attributed_image import add_attributed_image,latex_plain
from dkvis.presentation.external_assets import catalog,fetch
from dkvis.slide_style import CURRENT,MUTED,GAP,para,tex

PEOPLE=yaml.safe_load(Path(__file__).with_name('people.yaml').read_text())
FOUNDATIONS=['sylvester','jordan','rayleigh','ritz','weyl']
OPERATORS=['sznagy','halmos','kato','davis','kahan']


def prepare(refresh=False):
    fetch(refresh=refresh)


class PersonSlide(LessonSlide):
    person=''
    stage=1
    def body(self):
        self.start();p=PEOPLE[self.person]
        add_attributed_image(self,self.person)
        top=VGroup(tex(p['life'],size=29,color=GAP),
                   para(latex_plain(p['places']),width=5.5,size=25,color=CURRENT),
                   para(latex_plain(p['human']),width=5.5,size=25))
        top.arrange(DOWN,buff=.24)
        self.put(top,'right',y=1.0,height=2.35)
        self.beat()
        publication=VGroup(tex('Publication in our story',size=23,color=CURRENT),
                          para(latex_plain(p['publication']),width=5.5,size=23))
        publication.arrange(DOWN,buff=.18)
        self.put(publication,'right',y=-1.05,height=1.45)
        self.takeaway(p['role'])


class Credits(LessonSlide):
    people=()
    stage=3
    def body(self):
        self.start();rows=[]
        for key in self.people:
            row=catalog()[key]
            title=tex(PEOPLE[key]['name'],size=25,color=CURRENT)
            credit=para(latex_plain(row['creator']+' · '+row['license']+' · Scaled; no new crop.'),width=11.6,size=21)
            links=para(latex_plain(row['short_source']+' · '+row['license_url'].removeprefix('https://')),width=11.6,size=18,color=MUTED)
            rows.append(VGroup(title,credit,links).arrange(DOWN,buff=.10))
        self.put(VGroup(*rows).arrange(DOWN,buff=.30),y=.35,height=4.0)
        self.takeaway('Creators, source pages, and license terms stay with every image when shared.')


class FoundationsSlide(LessonSlide):lesson_deck='history-people-foundations'
class OperatorsSlide(LessonSlide):lesson_deck='history-people-operators'


class PfTitle(LessonTitle):
    lesson_deck='history-people-foundations'
    series_title='People behind the mathematics · Part 1'
    title_lines=('Geometry, sound,', 'and approximation')
    subtitle='Sylvester · Jordan · Rayleigh · Ritz · Weyl'


class PoTitle(LessonTitle):
    lesson_deck='history-people-operators'
    series_title='People behind the mathematics · Part 2'
    title_lines=('Operators and', 'reliable computation')
    subtitle='Sz.-Nagy · Halmos · Kato · Davis · Kahan'


class PfIntro(FoundationsSlide):
    def body(self):
        self.start()
        self.put(stack(tex('Five people; several routes into mathematics',size=33),
                       para('Engineering, physical experiments, algebra, university teaching, and the institutions that made research possible.',width=10.8,size=29),
                       tex('Who?  Where?  Which publication?  Why does it matter here?',size=28,color=CURRENT),buff=.5),y=.4,height=3.7)
        self.takeaway('A theorem name is an invitation to meet a person, not a complete biography.')


class PoIntro(OperatorsSlide):
    def body(self):
        self.start()
        self.put(stack(tex('People who organized a changing subject',size=33),
                       para('Operator theory, mathematical physics, exposition, academic freedom, and numerical reliability.',width=10.8,size=29),
                       tex('Portrait dates and publication dates are recorded separately.',size=27,color=CURRENT),buff=.5),y=.4,height=3.7)
        self.takeaway('Different careers meet in related questions without forming one simple line of influence.')


class PfSylvester(PersonSlide):lesson_deck='history-people-foundations';person='sylvester'
class PfJordan(PersonSlide):lesson_deck='history-people-foundations';person='jordan'
class PfRayleigh(PersonSlide):lesson_deck='history-people-foundations';person='rayleigh'
class PfRitz(PersonSlide):lesson_deck='history-people-foundations';person='ritz'
class PfWeyl(PersonSlide):lesson_deck='history-people-foundations';person='weyl'
class PoSznagy(PersonSlide):lesson_deck='history-people-operators';person='sznagy'
class PoHalmos(PersonSlide):lesson_deck='history-people-operators';person='halmos'
class PoKato(PersonSlide):lesson_deck='history-people-operators';person='kato'
class PoDavis(PersonSlide):lesson_deck='history-people-operators';person='davis'
class PoKahan(PersonSlide):lesson_deck='history-people-operators';person='kahan'


class PfConnections(FoundationsSlide):
    stage=2
    def body(self):
        self.start()
        self.put(stack(tex('Rayleigh–Ritz: separate people and publications',size=30),
                       tex('Sylvester and Cayley: a documented friendship',size=30),
                       tex('Jordan: engineering alongside research',size=30),
                       tex('Weyl: several mathematical subjects in one career',size=30),buff=.4),y=.4,height=3.7)
        self.takeaway('Distinguish a modern compound name from an actual collaboration.')


class PoConnections(OperatorsSlide):
    stage=2
    def body(self):
        self.start()
        self.put(stack(tex('Teaching and texts: Sz.-Nagy and Halmos',size=30),
                       tex('Physics and operators: Kato',size=30),
                       tex('Research and public commitments: Davis',size=30),
                       tex('Numerical trust: Kahan',size=30),
                       tex('1969 announcement → 1970 Davis–Kahan paper'.replace('→',r'$\to$'),size=29,color=CURRENT),buff=.34),y=.4,height=3.7)
        self.takeaway('The joint paper sits within distinct careers and a broader mathematical community.')


class PfSummary(FoundationsSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Sylvester: matrix equations',size=31),
                       tex('Jordan: geometry of spaces',size=31),
                       tex('Rayleigh and Ritz: physical problems and approximation',size=29),
                       tex('Weyl: spectral values and a wider mathematical life',size=29),
                       para('Continue with projections, principal angles, eigenvalue stability, and residuals.',width=11,size=27),buff=.30),y=.35,height=3.8)
        self.takeaway('Remember one person, one publication, and one mathematical question together.')


class PoSummary(OperatorsSlide):
    stage=3
    def body(self):
        self.start()
        self.put(stack(tex('Sz.-Nagy: compare nearby projections',size=30),
                       tex('Halmos: organize two-subspace geometry',size=30),
                       tex('Kato: follow spectral spaces',size=30),
                       tex('Davis: a program on subspace separation and rotation',size=29),
                       tex('Kahan: reliable numerical computation',size=30),
                       para('Next: spectral projections, Sylvester estimates, Davis–Kahan, and the statistical continuation.',width=11,size=26),buff=.27),y=.35,height=3.9)
        self.takeaway('Biographies orient the story; the technical lectures explain the statements and proofs.')


class PfCreditsOne(Credits):lesson_deck='history-people-foundations';people=FOUNDATIONS[:3]
class PfCreditsTwo(Credits):lesson_deck='history-people-foundations';people=FOUNDATIONS[3:]
class PoCreditsOne(Credits):lesson_deck='history-people-operators';people=OPERATORS[:3]
class PoCreditsTwo(Credits):lesson_deck='history-people-operators';people=OPERATORS[3:]
