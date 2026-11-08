# Repo-backed audio lecture reader

## Run on the LAN

```bash
cd /home/joncrall/code/aiq-dkps-formalization/visualizations
make serve
```

Open `http://127.0.0.1:8001/audio` on the server or
`http://<toothbrush-LAN-IP>:8001/audio` from a phone or another computer.
`make serve PORT=8002` changes the listener port if 8001 is occupied.
The server binds `0.0.0.0` on the LAN; do not expose this unauthenticated
service to the public Internet.

## Speech profile and voice selection

**Kokoro is the default for the audio reader.** It uses
`KOKORO_TTS_ENDPOINT` from `.env`; on the supplied machine that is
`http://192.168.222.38:8880/v1/audio/speech`. The fixed profile fallback
is `http://127.0.0.1:8880/v1/audio/speech`.

**Crall Math DK v2 (Breeze)** is another built-in profile; it uses
`CRALL_TTS_ENDPOINT` or falls back to
`http://127.0.0.1:8821/v1/audio/speech`, matching the existing Breeze
container's published port. Its native WAV responses are converted to MP3
using FFmpeg. Other `tts.toml` profiles are listed as available options.

The reader's selection does not change `DKVIS_TTS_PROFILE` or
`MATCHING_TTS_PROFILE`, which remain the production narration settings.
An optional `DKVIS_AUDIO_TTS_PROFILE` changes the *initial reader default*;
`make serve AUDIO_TTS_PROFILE=...` does the same for one run. Browsers
remember their selected profile and voice separately.

### Register a custom voice

1. Ensure the target TTS service already supports the voice ID. Some servers
   expose IDs through `/v1/audio/voices` or `/v1/voices`.
2. In `/audio`, choose that TTS profile and expand **Register a custom voice**.
3. Enter the voice ID and, optionally, a readable display label. Click
   **Register voice**. The voice becomes selectable immediately.

Voice registration adds a name to the reader. A custom reference voice must
first be configured or installed on the corresponding TTS service. Registered
IDs and labels persist under `audio-cache/registered-voices.json`. The registry
contains no uploaded voice samples; browser clients cannot change server URLs.
Additional server profiles are configured in the shared `tts.toml` file.

## Follow the text while listening

The player displays the current sentence above its playback controls and
highlights the sentence in the **complete lecture transcript**. Every page is
visible together, with the active page marked. Click a sentence anywhere in
the lecture to seek near it (generating its audio page if needed), or enable
**Auto-scroll transcript** to follow along while listening.

The **Entire lecture** timeline shows elapsed time, remaining time, and
lecture-wide percentage, even while some pages have not yet been synthesized.
Before all page durations are known, time is estimated from spoken word counts
and calibrated with the measured durations of played pages. Measured durations
are remembered for the selected lecture, transcript revision, voice, and speech
speed; once all pages are known, the full timeline reports measured time.
The global slider seeks across audio pages, while the native audio slider seeks
within the selected page. Playback speed affects elapsed/remaining wall time.

The sentence highlight is estimated from
sentence-length weighting and MP3 playback progress; the speech server currently
does not supply word or sentence timestamps. The displayed source text is the
same extracted text sent for speech generation, before voice-specific
pronunciation replacements are applied.

Speech pages now default to **1,200 characters** (previously 420), so a page
contains several connected paragraphs before the player advances. Set
`DKVIS_AUDIO_PAGE_CHARS` in `visualizations/.env` to an integer from 250 through
1,500 to change the page length, then restart `make serve`. Larger pages reduce
interruptions but take longer to synthesize on the first play.

The reader supports manual page navigation, browser audio seeking, adjustable
synthesis/playback speed, optional next-page prefetch, automatic advancement,
and **Cache whole lecture**. The canonical narration extractor strips
non-spoken mathematical appendices; reference sidecars appear only as related
reading links. MP3 cache keys include transcript content, model, voice, speed,
profile, endpoint, and synthesis options. Editing a lecture automatically
produces a new cache key.

## API

| Method | Route | Purpose |
| --- | --- | --- |
| GET | `/audio` | Mobile-friendly lecture reader |
| GET | `/api/audio-lectures` | List repository transcripts |
| GET | `/api/audio-lectures/{id}` | Spoken transcript, pages, and readings |
| GET | `/api/audio-profiles` | Configured TTS profiles and reader default |
| GET | `/api/audio-voices?profile=kokoro` | Advertised and registered voices |
| POST | `/api/audio-voices/register` | Register `{profile, voice, label}` |
| GET | `/api/audio-health?profile=kokoro` | Connectivity for a selected profile |
| GET | `/api/audio-lectures/{id}/pages/{page}?profile=kokoro&voice=af_heart&speed=1` | Cached-generation status |
| POST | `/api/audio-lectures/{id}/pages/{page}/render` | Generate MP3 with selected `{profile, voice, speed}` |
| GET | `/api/audio-lectures/{id}/pages/{page}/audio?profile=kokoro&voice=af_heart&speed=1` | Seekable MP3 |

The server controls upstream endpoints; web clients select only predefined
profiles, voice IDs, and synthesis speed. Audio generation uses a bounded
worker queue and deduplicates requests for the same cache key.

## Tests

```bash
cd /home/joncrall/code/aiq-dkps-formalization/visualizations
uv run --extra serve --extra test pytest -q \
    tests/test_audio_lecture_library.py tests/test_media_server.py
python3 draft-stages/tts-lectures/extract_narration.py --check \
    draft-stages/tts-lectures/[0-9]*-*.md
```

Production smoke test: play the first Kokoro page from `/audio`, then select
**Crall Math DK v2 (Breeze)** and play the same page. Verify that the browser
uses the two distinct cached MP3s and the live transcript follows seeking.
