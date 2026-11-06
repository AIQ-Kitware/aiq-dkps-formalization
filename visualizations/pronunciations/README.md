# Mathematical pronunciation notes and lexicons

These are reported problems in some Breeze TTS 2 voices. A word appearing here
is not evidence that every voice gets it wrong, nor that a proposed spelling
works for every speaker. Listening evidence comes from Jon's lecture reviews.

| Word | Reported spelling remedy | Evidence and current use |
| --- | --- | --- |
| adjoint | — | Problem reported; no verified remedy yet. |
| nonnegative | non-negative | Reported improvement; active Breeze alias. |
| orthonormal | ortho-normal | Pronunciation improves, but the speaker can pause too much inside the word. Tentative; excluded from defaults. |
| Frobenius | — | Problem reported; no verified remedy yet. |
| eigenvectors | eigen-vectors | Reported improvement; active Breeze alias. |
| Hermitian | — | Problem reported; no verified remedy yet. |
| Hilbert | — | Problem reported; no verified remedy yet. |
| Laplacian | — | Problem reported; no verified remedy yet. |
| matrix | — | Problem reported; no verified remedy yet. |

## Standard machinery plus curated exceptions

Store accepted spelling remedies in the standard
[W3C PLS format](https://www.w3.org/TR/pronunciation-lexicon/), using `grapheme`
and `alias`. The active [Breeze lexicon](breeze-tested-en-us.pls) contains only
the two accepted aliases. The local adapter reads spelling aliases and applies
the existing whole-word, case-insensitive replacement behavior. It is a limited
text adapter, not a full PLS processor: it rejects phoneme and grammatical-role
entries rather than pretending a text-only model can interpret them.

[Misaki](https://github.com/hexgrad/misaki) provides Kokoro's grapheme-to-phoneme
machinery and explicit pronunciation annotations; [Phonemizer](https://bootphon.github.io/phonemizer/)
can obtain phonemes through standard backends such as eSpeak. Those tools can
provide a baseline and, where supported by an engine's API, native pronunciation
control. The current Breeze server accepts ordinary text; adding IPA to its input
would not establish correct pronunciation. It still needs listening-tested aliases.
No native Misaki/phoneme adapter has been added to our client by this change.

For each new remedy, compare the unmodified word and candidate in a natural
mathematical sentence. Listen for pronunciation, stress, unwanted pauses and
neighboring-word effects. Record the model and reference voice locally when
identifying details are private. A result for one voice should remain scoped to
that voice unless further listening supports wider use. Unverified words remain
in the table above; they do not receive guessed default substitutions.

## Per-speaker experiments

Use a local PLS file to augment the baseline aliases with that speaker's tested
remedies. Select it without registering a private voice in the repository:

```bash
make video DECK=operators-rayleigh-ritz TTS_PROFILE=breeze \
  TTS_SETTINGS='{"pronunciation_lexicon":"/absolute/path/to/local-speaker.pls"}'
```

Add the usual endpoint, model and voice arguments. A selected file replaces the
model's lexicon; copy the baseline entries if they should remain active. Paths
inside `tts.toml` are relative to that config file, while an absolute path works
for a private file. Its expanded aliases are recorded with the generated audio.
Keep private speaker identifiers and observations in ignored local storage.

An explicit `pronunciation_replacements` map takes precedence over the PLS file.
For a deliberate trial of the tentative orthonormal remedy:

```bash
make video DECK=operators-rayleigh-ritz TTS_PROFILE=breeze \
  TTS_SETTINGS='{"pronunciation_replacements":{"nonnegative":"non-negative","eigenvectors":"eigen-vectors","orthonormal":"ortho-normal"}}'
```

An empty map disables all hints. Canonical transcripts and captions remain
unchanged, and only requests with changed synthesis text need new audio. Existing
recordings retain their current pronunciation until rebuilt.
