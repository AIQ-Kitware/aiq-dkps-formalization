"""Align known English narration to audio; inference dependencies load only on use.

The acoustic model supplies frame probabilities. A CTC Viterbi path follows the
known transcript, including blank states and repeated-letter constraints. This
estimates timing; it does not certify pronunciation or transcript correctness.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess
import numpy as np
from dkvis.presentation.audio_quality import fingerprint
from dkvis.presentation.timing import timing

MODEL = 'facebook/wav2vec2-base-960h'
VERSION = 1


def transcript_words(text):
    result=[]
    for match in re.finditer(r"[A-Za-z]+(?:['’][A-Za-z]+)*|\d+(?:\.\d+)?", text):
        normalized=match[0].replace('’',"'").upper()
        if match[0][0].isdigit():
            from num2words import num2words
            normalized='|'.join(re.findall(r"[A-Z']+",num2words(match[0]).upper()))
        result.append(dict(text=match[0], normalized=normalized,
                           char_start=match.start(), char_end=match.end()))
    if not result:
        raise ValueError('Cannot align an empty English transcript')
    return result


def ctc_path(log_probs, tokens, blank=0):
    """Return a frame-to-state path for blank/token/blank/... CTC states."""
    log_probs=np.asarray(log_probs)
    tokens=np.asarray(tokens,dtype=int)
    if not len(tokens) or log_probs.ndim!=2 or not len(log_probs):
        raise ValueError('Alignment needs frames and transcript tokens')
    labels=np.full(2*len(tokens)+1,blank,dtype=int); labels[1::2]=tokens
    if labels.min()<0 or labels.max()>=log_probs.shape[1]:
        raise ValueError('Transcript token is outside the acoustic vocabulary')
    skip=np.zeros(len(labels),dtype=bool)
    skip[2:]=(labels[2:]!=blank)&(labels[2:]!=labels[:-2])
    previous=np.full(len(labels),-np.inf); previous[0]=0
    trace=np.zeros((len(log_probs),len(labels)),dtype=np.uint8)
    for t,emission in enumerate(log_probs):
        step=np.r_[-np.inf,previous[:-1]]
        jump=np.r_[[-np.inf,-np.inf],previous[:-2]]
        jump[~skip]=-np.inf
        choices=np.vstack([previous,step,jump])
        move=np.argmax(choices,axis=0)
        previous=choices[move,np.arange(len(labels))]+emission[labels]
        trace[t]=move
    state=len(labels)-2+int(previous[-1]>previous[-2])
    if not np.isfinite(previous[state]):
        raise ValueError('Audio has too few frames for this transcript')
    states=np.empty(len(log_probs),dtype=int)
    for t in range(len(log_probs)-1,-1,-1):
        states[t]=state
        state-=int(trace[t,state])
    if state!=0:
        raise ValueError('Incomplete forced-alignment path')
    return states,labels


class Aligner:
    def __init__(self, model=MODEL, revision=None, threads=4):
        self.name=model; self.revision=revision; self.threads=threads
        self._model=None

    def load(self):
        if self._model is not None:return
        try:
            import torch
            from transformers import AutoProcessor, AutoModelForCTC
        except ImportError as error:
            raise RuntimeError('Install the align extra (CPU torch and transformers) for forced alignment') from error
        torch.set_num_threads(self.threads)
        with timing().measure('alignment_model_load',model=self.name):
            self.processor=AutoProcessor.from_pretrained(self.name,revision=self.revision)
            self._model=AutoModelForCTC.from_pretrained(self.name,revision=self.revision).eval()
        self.revision=getattr(self._model.config,'_commit_hash',None) or self.revision

    def align(self, audio, text, cache):
        self.load()
        words=transcript_words(text)
        key=hashlib.sha256(json.dumps(dict(version=VERSION,audio=fingerprint(audio),text=text,
            model=self.name,revision=self.revision),sort_keys=True).encode()).hexdigest()
        cache=Path(cache); cache.mkdir(parents=True,exist_ok=True)
        path=cache/f'{key}.json'
        if path.exists():
            timing().record('alignment_cache',0,cache_hit=True,file=str(path))
            return json.loads(path.read_text())
        import torch
        with timing().measure('forced_alignment',model=self.name,words=len(words),audio=str(audio)):
            raw=subprocess.run(['ffmpeg','-v','error','-i',str(audio),'-f','f32le','-ac','1','-ar','16000','pipe:1'],capture_output=True,check=True).stdout
            samples=np.frombuffer(raw,dtype='<f4').copy()
            inputs=self.processor(samples,sampling_rate=16000,return_tensors='pt')
            with torch.inference_mode():
                logits=self._model(**inputs).logits[0]
                probs=torch.log_softmax(logits,dim=-1).numpy()
            target='|'.join(w['normalized'] for w in words)
            vocabulary=self.processor.tokenizer.get_vocab()
            unknown=set(target)-vocabulary.keys()
            if unknown:raise ValueError(f'Unsupported alignment characters: {unknown}')
            tokens=[vocabulary[c] for c in target]
            states,labels=ctc_path(probs,tokens,self.processor.tokenizer.pad_token_id)
            ratio=len(samples)/16000/len(probs)
            cursor=0
            for word in words:
                char_states=2*np.arange(cursor,cursor+len(word['normalized']))+1
                frames=np.flatnonzero(np.isin(states,char_states))
                if not len(frames):raise ValueError('Transcript word has no aligned frames')
                word.update(start=float(frames[0]*ratio),end=float((frames[-1]+1)*ratio),
                    score=float(np.exp(probs[frames,labels[states[frames]]]).mean()))
                cursor+=len(word['normalized'])+1
            recognized=self.processor.batch_decode(logits.argmax(dim=-1).unsqueeze(0))[0]
            result=dict(version=VERSION,key=key,audio_sha256=fingerprint(audio),text=text,
                        model=self.name,revision=self.revision,seconds=len(samples)/16000,
                        words=words,recognized=recognized)
            path.write_text(json.dumps(result,indent=2)+'\n')
            return result


def phrase_crop(alignment, target_seconds=6, tail=True):
    """Choose complete words, preferring a nearby sentence/clause boundary."""
    words=alignment['words']; text=alignment['text']
    if tail:
        end=len(words); start=end-1
        while start>0 and words[-1]['end']-words[start]['start']<target_seconds:
            start-=1
        # Avoid including the end of the previous clause when a nearby boundary exists.
        for i in range(start,min(end-1,start+4)):
            gap=text[words[i]['char_end']:words[i+1]['char_start']]
            if re.search(r'[.!?;:]',gap):start=i+1;break
    else:
        start=0;end=1
        while end<len(words) and words[end-1]['end']-words[0]['start']<target_seconds:
            end+=1
    begin=max(0,words[start]['start']-.06)
    finish=min(alignment['seconds'],words[end-1]['end']+.1)
    return dict(start=begin,end=finish,text=text[words[start]['char_start']:words[end-1]['char_end']],
                words=[dict(w) for w in words[start:end]],min_score=min(w['score'] for w in words[start:end]))
