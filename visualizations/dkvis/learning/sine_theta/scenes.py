"""Bind authored speech to the preserved reference scenes' animation builds.

The reference implementations retain their original notes and behavior. This
edition inherits their visual bodies and substitutes one authored beat at each
existing say() boundary, forwarding external-video/loop options unchanged.
"""
from dkvis import slides_sine_theta as source
from dkvis import slides_sine_theta_3d as three_d
from dkvis import slides_prop44 as prop44
from dkvis.components.lesson import LessonTitle,scripts


def prepare(refresh=False):
    three_d.prepare(refresh=refresh)


class _NarratedReference:
    lesson_deck='sine-theta-lecture'

    @property
    def narration(self):
        return scripts(self.lesson_deck)[type(self).__name__]

    def construct(self):
        self._spoken_build=0
        super().construct()
        if self._spoken_build!=len(self.narration.beats):
            raise ValueError(f'Animation/transcript mismatch: {type(self).__name__}')

    def say(self,notes,**kwargs):
        if self._spoken_build>=len(self.narration.beats):
            raise ValueError(f'Too many animation builds: {type(self).__name__}')
        authored=self.narration.beats[self._spoken_build]
        self._spoken_build+=1
        super().say(authored,**kwargs)


class S00TitleShort(LessonTitle):
    lesson_deck='sine-theta-lecture'
    series_title='Spectral perturbation theory'
    title_lines=('How far can an eigenvector turn?',)
    subtitle='Residuals and spectral separation control subspace error.'


class S00bSetting(_NarratedReference,source.S00bSetting): pass
class S01Ellipse(_NarratedReference,source.S01Ellipse): pass
class S02Perturb(_NarratedReference,source.S02Perturb): pass
class S03bWanted(_NarratedReference,source.S03bWanted): pass
class S03NoGap(_NarratedReference,source.S03NoGap): pass
class S03cUnstable(_NarratedReference,source.S03cUnstable): pass
class S04Angle(_NarratedReference,source.S04Angle): pass
class S05Residual(_NarratedReference,source.S05Residual): pass
class S06Gap(_NarratedReference,source.S06Gap): pass
class S07Theorem(_NarratedReference,source.S07Theorem): pass
class S08Why(_NarratedReference,source.S08Why): pass
class S11Payoff(_NarratedReference,source.S11Payoff): pass
class D01Planes(_NarratedReference,three_d.D01Planes): pass
class S12Lean(_NarratedReference,source.S12Lean): pass
class P01Claim(_NarratedReference,prop44.P01Claim): pass
class P02Counterexample(_NarratedReference,prop44.P02Counterexample): pass
class S14Summary(_NarratedReference,source.S14Summary): pass
