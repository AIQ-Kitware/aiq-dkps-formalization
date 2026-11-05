# Davis–Kahan sine theta: narrated course edition

Deck **`sine-theta-lecture`**, lecture **003750**, reuses the eighteen core
scenes of the preserved `sine-theta-short` reference composition and appends
Qwen's two study questions. Its expanded narration takes roughly 25 minutes
before animation and thinking pauses; the original live talk was paced for
fifteen minutes.

From `visualizations/`:

```bash
make slides DECK=sine-theta-lecture
make text DECK=sine-theta-lecture
make video DECK=sine-theta-lecture TTS_PROFILE=crall-math-dk-v2-breeze-tts2 SKIP_RENDER=1
```

It is included in `make lectures-video`. Restart an older library server to
load the new deck registration. The numbered transcript and quiz live under
[`lectures/003750_sine_theta/`](../../../lectures/003750_sine_theta/lecture.md).

The original transcript by `qwen3.8-27b-dbirks-hyperqwen-long` had been attached
to a non-indexed reference deck, whose rendered notes still contained its old
presenter speech. Merely adding `DeckSpec.narration` does not synchronize those
notes, and the video preflight correctly refuses mismatched clips.

The local adapters inherit the existing visual bodies and substitute authored
speech at each original `say()` boundary. They check the exact build count and
forward external video/loop options. The title uses the common short cover and
model disclosure. Shared video production retains its strict note-to-transcript
check; it does not silently rewrite stale slide metadata.

`provenance.yaml` distinguishes Qwen's transcript/quiz authorship, inherited
visual implementations, and GPT-6.1-Sol's integration and limited corrections.
The original reference composition remains an eighteen-scene slide deck.
