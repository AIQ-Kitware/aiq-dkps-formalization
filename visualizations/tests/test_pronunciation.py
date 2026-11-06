"""Pronunciation hints change synthesis, while canonical text and cache stay honest."""
import importlib
import io
import json
import pytest
from dkvis.presentation import audio
from dkvis.presentation.captions import speech_parts
from dkvis.presentation.pronunciation import speech_text, validate_replacements
from dkvis.presentation.tts import resolve_profile

RULES={'nonnegative':'non-negative','orthonormal':'ortho-normal','eigenvectors':'eigen-vectors'}


def test_whole_word_hints_preserve_case_and_do_not_cascade():
    text='Orthonormal EIGENVECTORS are nonnegative; nonnegatively is different.'
    assert speech_text(text,RULES)=='Ortho-normal EIGEN-VECTORS are non-negative; nonnegatively is different.'
    assert speech_text('nonnegative',{'nonnegative':'non-negative','non-negative':'other'})=='non-negative'
    assert speech_text(text,{})==text
    for values in [[], {'word':''}, {'word':'hint','Word':'other'}]:
        with pytest.raises(ValueError):validate_replacements(values)


def test_model_defaults_and_explicit_client_overrides():
    document=dict(profiles=dict(demo=dict(endpoint='http://test.invalid',model='breeze-tts2',voice='demo',response_format='wav')),
                  pronunciations={'breeze-tts2':RULES})
    assert resolve_profile(document,'demo')['pronunciation_replacements']==RULES
    assert resolve_profile(document,'demo',{'pronunciation_replacements':{}})['pronunciation_replacements']=={}
    assert resolve_profile(document,'demo',{'model':'kokoro'})['pronunciation_replacements']=={}
    with pytest.raises(ValueError):resolve_profile(document,'demo',{'pronunciation_replacements':[]})


def test_synthesis_cache_and_captions_keep_separate_texts(tmp_path,monkeypatch):
    monkeypatch.setenv('DKVIS_RENDER_TIMING_LOG',str(tmp_path/'timings.jsonl'))
    module=importlib.import_module('dkvis.presentation.timing')
    monkeypatch.setattr(module,'_CURRENT',module.TimingLog())
    monkeypatch.setattr(audio,'duration',lambda path:.5)
    calls=[]
    def request(req,**kwargs):
        calls.append(json.loads(req.data))
        response=io.BytesIO(b'audio');response.headers={'Content-Type':'audio/wav'}
        return response
    monkeypatch.setattr(audio.urllib.request,'urlopen',request)
    common=dict(endpoint='http://test.invalid',model='breeze-tts2',voice='demo',language=None,timeout=2,
                request_settings=dict(instruction='Orthonormal lecture.',ref_text='nonnegative reference'))
    text='Orthonormal eigenvectors are nonnegative.'
    path=audio.speech(text,tmp_path/'clip',pronunciation_replacements=RULES,**common)
    assert calls[0]['input']=='Ortho-normal eigen-vectors are non-negative.'
    assert calls[0]['instruction']=='Orthonormal lecture.'
    assert calls[0]['ref_text']=='nonnegative reference'  # Reference transcripts must match their audio.
    assert path.with_suffix('.txt').read_text().strip()==text
    metadata=json.loads(path.with_suffix('.json').read_text())
    assert metadata['tts_text']==calls[0]['input'] and metadata['display_text']==text
    assert speech_parts(tmp_path,path)[0]['text']==text
    assert audio.speech(text,tmp_path/'clip',pronunciation_replacements={**RULES,'unused':'un-used'},**common)==path
    assert len(calls)==1  # An unused hint does not invalidate the actual request.
    changed=audio.speech(text,tmp_path/'clip',pronunciation_replacements={**RULES,'orthonormal':'ortho normal'},**common)
    assert changed!=path and len(calls)==2
    # Identical synthesis input can have a different canonical transcript.
    alias=audio.speech(calls[0]['input'],tmp_path/'clip',pronunciation_replacements={},**common)
    assert alias!=path and alias.with_suffix('.txt').read_text().strip()==calls[0]['input']
    assert speech_parts(tmp_path,path)[0]['text']==text


def test_shipped_pls_contains_only_accepted_aliases():
    from dkvis.presentation.pronunciation import load_pls_aliases
    from dkvis.presentation.paths import ROOT
    assert load_pls_aliases(ROOT/'pronunciations/breeze-tested-en-us.pls')=={
        'nonnegative':'non-negative','eigenvectors':'eigen-vectors'}


def test_config_relative_pls_and_local_speaker_override(tmp_path,monkeypatch):
    from dkvis.presentation import tts
    monkeypatch.setattr(tts,'load_env',lambda:None)
    template='''<lexicon version="1.0" xmlns="http://www.w3.org/2005/01/pronunciation-lexicon" xml:lang="en-US"><lexeme><grapheme>orthonormal</grapheme><alias>{}</alias></lexeme></lexicon>'''
    (tmp_path/'baseline.pls').write_text(template.format('baseline hint'))
    (tmp_path/'local.pls').write_text(template.format('local hint'))
    config=tmp_path/'tts.toml'
    config.write_text('''[profiles.demo]
endpoint="http://test.invalid"
model="breeze-tts2"
voice="demo"
response_format="wav"
[pronunciation_lexicons]
breeze-tts2="baseline.pls"
''')
    document=tts.load_profiles(config)
    assert resolve_profile(document,'demo')['pronunciation_replacements']=={'orthonormal':'baseline hint'}
    assert resolve_profile(document,'demo',{'pronunciation_lexicon':str(tmp_path/'local.pls')})['pronunciation_replacements']=={'orthonormal':'local hint'}
    assert resolve_profile(document,'demo',{'pronunciation_replacements':{}})['pronunciation_replacements']=={}
    assert resolve_profile(document,'demo',{'model':'kokoro'})['pronunciation_replacements']=={}


def test_text_adapter_rejects_native_phoneme_entries(tmp_path):
    from dkvis.presentation.pronunciation import load_pls_aliases
    path=tmp_path/'phonemes.pls'
    path.write_text('''<lexicon version="1.0" xmlns="http://www.w3.org/2005/01/pronunciation-lexicon" alphabet="ipa" xml:lang="en-US"><lexeme><grapheme>example</grapheme><phoneme>ɛɡzæmpəl</phoneme></lexeme></lexicon>''')
    with pytest.raises(ValueError,match='native engine support'):load_pls_aliases(path)
