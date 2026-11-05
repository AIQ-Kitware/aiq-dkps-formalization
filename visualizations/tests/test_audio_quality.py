"""Numerical and actual FFmpeg behavior of the reusable audio processing layer."""
import shutil
import wave

import numpy as np
import pytest

from dkvis.presentation import audio_quality as aq
from dkvis.presentation.tts import resolve_profile, narrator_id


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


def test_edge_fades_keep_length_and_body_and_remove_steps():
    from dkvis.presentation.media import edge_fades
    samples = np.full(2000, 12000, dtype=np.int16)
    corrected = edge_fades(samples, 48000, 8)
    assert len(corrected) == len(samples)
    assert corrected[0] == corrected[-1] == 0
    assert corrected[500:1500].tolist() == samples[500:1500].tolist()
    assert np.max(np.abs(np.diff(corrected.astype(float)))) < 40
    assert samples[0] == 12000  # input is preserved
    assert np.array_equal(edge_fades(samples, 48000, 0), samples)


@pytest.mark.skipif(not shutil.which('ffmpeg'), reason='requires FFmpeg')
def test_narration_assembly_preserves_gaps_and_handles_sample_rates(tmp_path):
    from dkvis.presentation.media import assemble_narration
    raw = tmp_path/'raw.wav'
    with wave.open(str(raw), 'wb') as stream:
        stream.setparams((1, 2, 24000, 0, 'NONE', 'not compressed'))
        stream.writeframes(np.full(2400, 10000, dtype='<i2').tobytes())
    builds = [dict(audio=raw, start=.1, end=.3), dict(audio=raw, start=.3, end=.5)]
    output = assemble_narration([dict(builds=builds)], tmp_path/'assembled.wav', total_seconds=.6)
    with wave.open(str(output), 'rb') as stream:
        result = np.frombuffer(stream.readframes(stream.getnframes()), dtype='<i2')
        assert stream.getframerate() == 48000
    assert len(result) == 28800
    assert np.all(result[:4800] == 0)
    assert result[4800] == result[9599] == result[14400] == result[19199] == 0
    assert result[6000] == result[16000] == 10000
    assert np.all(result[19200:] == 0)
    with pytest.raises(ValueError, match='refusing to truncate'):
        assemble_narration([dict(builds=[dict(audio=raw, start=0, end=.05)])], tmp_path/'bad.wav')


def test_narrator_name_tracks_reference_voice_and_actual_model():
    doc={'profiles':{'crall':dict(endpoint='http://localhost',model='breeze-tts2',
         voice='crall-math-dk',narrator_voice='crall',response_format='wav')}}
    settings=resolve_profile(doc,'crall')
    assert narrator_id(settings)=='crall-breeze-tts2'
    assert settings['profile']=='crall'  # stable cache namespace
    assert narrator_id(resolve_profile(doc,'crall',{'model':'another-model'}))=='crall-another-model'
    assert narrator_id(resolve_profile(doc,'crall',{'voice':'another-speaker'}))=='another-speaker-breeze-tts2'
    assert narrator_id(dict(profile='kokoro',model='kokoro',voice='af_heart'))=='kokoro'
