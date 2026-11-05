"""Numerical and actual FFmpeg behavior of the reusable audio processing layer."""
import shutil
import wave

import numpy as np
import pytest

from dkvis.presentation import audio_quality as aq
from dkvis.presentation.tts import resolve_profile


def test_window_levels_and_short_final_window():
    times, db = aq.levels(np.r_[np.ones(100), np.full(25, .1)], 1000)
    assert times == pytest.approx([0, .1])
    assert db == pytest.approx([0, -20])
    assert not len(aq.levels([], 1000)[0])


def test_opening_excess_and_silence():
    steady = aq.signal_summary(np.full(6000, .1), 1000)
    burst = aq.signal_summary(np.r_[np.full(2000, .4), np.full(4000, .1)], 1000)
    silent = aq.signal_summary(np.zeros(6000), 1000)
    assert steady['opening_excess_db'] == pytest.approx(0)
    assert burst['opening_excess_db'] == pytest.approx(20*np.log10(4))
    assert silent['opening_excess_db'] is None
    assert silent['rail_samples'] == 0


def test_profile_inherits_and_overrides_audio_settings():
    doc = {'postprocess': {'enabled': True, 'ratio': 2.5}, 'profiles': {'a': {
        'endpoint': 'http://localhost', 'model': 'x', 'voice': 'x', 'response_format': 'wav',
        'postprocess': {'ratio': 3}}}}
    processing = resolve_profile(doc, 'a')['postprocess']
    assert processing['enabled'] and processing['ratio'] == 3
    assert processing['target_lufs'] == -18
    with pytest.raises(ValueError):
        aq.settings({'ratio': float('nan')})


@pytest.mark.skipif(not shutil.which('ffmpeg'), reason='requires FFmpeg')
def test_processing_controls_onset_level_and_preserves_samples(tmp_path, monkeypatch):
    monkeypatch.setattr(aq, 'CACHE', tmp_path/'measurements')
    rate = 24000
    t = np.arange(rate*8)/rate
    # A sustained loud opening followed by a much quieter sustained body.
    signal = np.sin(2*np.pi*220*t)*np.where(t < 2, .5, .05)
    raw = tmp_path/'raw.wav'
    with wave.open(str(raw), 'wb') as stream:
        stream.setparams((1, 2, rate, 0, 'NONE', 'not compressed'))
        stream.writeframes((signal*32767).astype('<i2').tobytes())
    original = raw.read_bytes()
    processed = aq.process_chunk(raw, tmp_path/'processed')
    before, after = aq.measure(raw), aq.measure(processed)
    assert raw.read_bytes() == original
    assert after['seconds'] == pytest.approx(before['seconds'], abs=1/48000)
    assert after['opening_excess_db'] < before['opening_excess_db']-3
    # Peak protection can prevent exact loudness matching on extreme dynamics.
    assert abs(after['loudness']['input_i']+18) < 1.5
    assert after['loudness']['input_tp'] <= -1.3
    assert aq.process_chunk(raw, tmp_path/'processed') == processed
    other = aq.process_chunk(raw, tmp_path/'processed', {'target_lufs': -21})
    assert other != processed
    assert aq.process_chunk(raw, tmp_path/'processed', {'enabled': False}) == raw
