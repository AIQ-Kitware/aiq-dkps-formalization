"""Adapted reference scenes bind authored notes without losing clip options."""
import pytest
pytest.importorskip('manim')
from dkvis.learning.sine_theta.scenes import _NarratedReference
from dkvis.presentation.narration import Narration


class VisualBody:
    def construct(self):
        self.recorded=[]
        self.say('Old first notes.')
        self.say('Old second notes.',src='orbit.mp4',loop=True)

    def say(self,notes,**kwargs):
        self.recorded.append((notes,kwargs))


class Narrated(_NarratedReference,VisualBody):
    @property
    def narration(self):
        return self.script


def test_notes_follow_authored_beats_and_preserve_external_video_options():
    scene=Narrated()
    scene.script=Narration('','','',('New first notes.','New second notes.'))
    scene.construct()
    assert scene.recorded==[('New first notes.',{}),('New second notes.',dict(src='orbit.mp4',loop=True))]


@pytest.mark.parametrize('beats',[('One beat.',),('One.','Two.','Three.')])
def test_build_count_mismatch_fails_before_video_synthesis(beats):
    scene=Narrated();scene.script=Narration('','','',beats)
    with pytest.raises(ValueError,match='builds|mismatch'):
        scene.construct()
