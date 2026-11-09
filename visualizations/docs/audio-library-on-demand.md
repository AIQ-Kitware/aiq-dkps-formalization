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

**Crall Math DK v2 (Breeze)** is the default for the audio reader. Its
profile ID is `crall-math-dk-v2-breeze-tts2`, and the voice ID sent to the
server is `crall-math-dk-v2`. It uses
`CRALL_TTS_ENDPOINT` or falls back to
`http://127.0.0.1:8821/v1/audio/speech`, matching the existing Breeze
container's published port. Its native WAV responses are converted to MP3
using FFmpeg. Other `tts.toml` profiles are listed as available options.

**Kokoro (`af_alloy`)** remains an available option through
`KOKORO_TTS_ENDPOINT` (falling back to
`http://127.0.0.1:8880/v1/audio/speech`).

The reader uses the public profile unless overridden, in order, by the
`--audio-tts-profile` / `make serve AUDIO_TTS_PROFILE=...` argument,
`DKVIS_AUDIO_TTS_PROFILE`, or `DKVIS_TTS_PROFILE`. The browser's profile
selection does not modify environment variables. Browsers remember explicitly
selected profiles and voices; change the profile dropdown if a previous
selection is retained.

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
Additional server profiles are configured in the ignored `tts.local.toml`
file, or in an explicit configuration selected with `make serve
TTS_CONFIG=/path/to/tts.toml`. The browser does not accept endpoint URLs.

For example, to use a TTS server on this machine without altering shared
`tts.toml`, add the following to `visualizations/tts.local.toml`:

```toml
[profiles.kokoro]
endpoint = "http://127.0.0.1:8880/v1/audio/speech"
```

The machine-local file is an **overlay**: it retains all unspecified settings
from the shared profile, including model, voice, response format and request
options. An explicit local `endpoint` also replaces the inherited
`endpoint_env` lookup; set `endpoint_env` in that same table to use an
environment variable instead. You can also add a separate named profile:

```toml
[profiles.local-kokoro]
display_name = "Local Kokoro"
model = "kokoro"
voice = "af_alloy"
response_format = "mp3"
endpoint = "http://127.0.0.1:8880/v1/audio/speech"
```

New names appear in the profile dropdown after restarting `make serve`.
The reader defaults to the public Breeze profile. A voice previously chosen in
the browser stays selected until changed. `TTS_CONFIG` instead selects a
complete, independent TOML file (no automatic overlay).

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
are remembered for the selected lecture, transcript revision, page size,
page count, pagination revision, voice, and speech speed; once all pages are known, the full timeline
reports measured time.
The global slider seeks across audio pages, while the native audio slider seeks
within the selected page. Playback speed affects elapsed/remaining wall time.

The sentence highlight is estimated from
sentence-length weighting and MP3 playback progress; the speech server currently
does not supply word or sentence timestamps. The displayed source text is the
same extracted text sent for speech generation, before voice-specific
pronunciation replacements are applied.

Speech pages now default to **600 characters** (previously 1,200). The paginator preserves whole sentences when they fit and prefers paragraph boundaries; only an individual sentence longer than the configured limit must be divided at word breaks. Changing the pagination algorithm revision invalidates the audio cache and the browser’s stored duration estimates. Set
`DKVIS_AUDIO_PAGE_CHARS` in `visualizations/.env` to an integer from 250 through
1,500 to change the page length, then restart `make serve`. Larger pages reduce interruptions but take longer to synthesize on the first play.
For Breeze TTS 2, the reader now requests server-managed **paragraph80**
long-form synthesis by default. It sends the complete page, with the existing
sentence-aware pagination and paragraph breaks, to the updated local-ai
server. The server groups intact sentences toward 80 words, with a 110-word
hard maximum, uses CFG 1.0 without a delivery instruction, and joins verified
PCM passages with boundary-aware pauses. The reader confirms the server's
`paragraph80-v1` response policy and keeps measured passage timing markers
for transcript playback. Existing cached recordings from the previous short
request policy are invalidated by a distinct synthesis cache key.

**Upgrade the local-ai Breeze container before using the updated DKPS reader.**
The reader rejects a Breeze response that lacks the long-form policy header,
so an old server cannot silently generate or cache truncated long requests.
To temporarily revert the DKPS reader to its former short-request behavior,
set `DKVIS_AUDIO_BREEZE_LONG_FORM=0` and restart `make serve`.

For other non-Kokoro endpoints, or Breeze with the opt-out setting, each page
is independently synthesized from short **12-word / 140-character** requests. In that legacy mode, each accepted request is also
limited to at most **12 seconds** of audio before retrying at smaller sizes,
subject to any lower service limit. The page audio is assembled only after
all requests finish. Set `DKVIS_AUDIO_SEGMENT_WORDS=6` in `.env` for an
especially truncation-prone custom voice, then restart the server. Optional
`DKVIS_AUDIO_SEGMENT_CHARS` and `DKVIS_AUDIO_SEGMENT_SECONDS` offer the other
limits. These checks cannot establish whether every word was spoken: the local
TTS server supplies audio without verified word-level alignment.

The audio cache identity explicitly includes the page-size setting, pagination
algorithm version, lecture ID, page index, and the page's text, as well as TTS
settings. Changing the page size regenerates page recordings even where the
text on an individual page happens to stay the same. Breeze synthesis limits
are separately part of its cache identity. Older files can remain on disk but
are not returned for new keys; a separate cache cleanup can reclaim space.
If `.env` explicitly sets `DKVIS_AUDIO_PAGE_CHARS=1200`, change that value to
`600` to use the new page length.

The reader supports manual page navigation, browser audio seeking, adjustable
synthesis/playback speed, optional next-page prefetch, automatic advancement,
and **Cache whole lecture**. The canonical narration extractor strips
non-spoken mathematical appendices; reference sidecars appear only as related
reading links. MP3 cache keys include page size, pagination version, page
address, transcript content, model, voice, speed, profile, endpoint, and
synthesis options. Editing a lecture automatically
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

## Course tracks

The reader offers three routes. **G1 · Manim** opens the existing presentation/video browser at `/`. **G2 · Comprehensive audio** opens `/audio?track=g2`, with all 150 standalone lectures. **G3 · Paper audio** opens `/audio?track=g3`, with 26 paper-focused lectures and its own introduction. G3 starts with a fast spectral-geometry crash course, develops the supporting proofs, and ends with six result-focused recordings: the four angle theorems, Proposition 4.4's counterexample, and real transport matching.

Both audio tracks share playback controls, Kokoro/Crall profiles, custom voices, and non-spoken learning references. They have separate transcript directories and audio caches. Switching tracks preserves G2's original identifiers and cached audio. Track selection uses a fixed server-side allowlist rather than arbitrary filesystem paths.

The G3 sequence and its G2 source correspondence are in `draft-stages/tts-paper/track.json`; the course is documented in `draft-stages/tts-paper/README.md`. The first G3 draft reuses 25 edited G2 recordings and adds a newly written paper-track introduction.

### Breeze playback completeness and follow-along timing

For non-Kokoro local profiles, speech pages are synthesized as smaller,
verified requests rather than one long request. The server rejects valid media
files that hit the configured TTS duration ceiling, retries implausibly short
segments, and checks that the final MP3 duration matches the sum of decoded
segments. These checks help detect incomplete audio before publishing a page.
The cache identity for non-Kokoro speech has changed, so previously cached
Breeze clips are not reused.

The browser highlights transcript sentences using the measured boundaries of
each synthesized segment, interpolating within a segment. This improves on
whole-page text-length estimates but is not phoneme/word forced alignment.
Page forwarding remains tied to the HTML audio element's actual `ended` event.

### Plain-text transcript for external TTS readers

Each audio lecture offers **Plain text / copy all** above the full transcript.
The link opens a new tab with only the canonical spoken narration and no audio
controls, speech-page boundaries, Markdown source metadata, or annotations.
Select all and copy the page into a local TTS reader. Both tracks are supported:

- `/api/audio-lectures/000000/transcript.txt?track=g2`
- `/api/audio-lectures/000000/transcript.txt?track=g3`

These endpoints do not synthesize audio or use the TTS cache.

### Browser audio cache identity and live diagnosis

The page audio URL includes the server-generated `key` returned by the
`/api/audio-lectures/{id}/pages/{page}` status response. That key includes the
page size, pagination version, profile, voice, and synthesis settings. Only
keyed URLs are advertised as immutable; legacy URLs without `key` are `no-store`.
An obsolete keyed URL returns 404 rather than serving a newly generated page
under an old address. This prevents the browser from replaying old audio after
server-side pagination or generation changes.

To check what the running **G2** reader is actually doing:

```bash
curl -s 'http://127.0.0.1:8001/api/audio-lectures/000000?track=g2' \
  | python -c 'import json,sys; d=json.load(sys.stdin); print("page_chars:", d["page_chars"], "page_count:", d["page_count"], "first_page_words:", len(d["pages"][0].split()))'
curl -s 'http://127.0.0.1:8001/api/audio-profiles' | python -m json.tool
curl -s 'http://127.0.0.1:8001/api/audio-health?profile=foobar-v1-breeze-tts2' \
  | python -m json.tool
```

The health endpoint reports effective `page_chars`, `speech_max_chars`,
`speech_max_words`, and `speech_max_seconds` for that particular profile. The
voice chosen in the web reader can override the profile's default voice, but
it does *not* change the profile-specific request instruction. Select the
actual Foobar profile if you want its configured `instruction`, rather than
selecting Foobar's voice within the Crall profile. In normal service mode
`tts.local.toml` is merged with `tts.toml`; avoid passing
`TTS_CONFIG=tts.local.toml` unless you intentionally want to load only the
private file.

An assembled 600-character audio page can legitimately last roughly one
minute, especially for a slow custom narrator; the 12-second synthesis limit
is enforced **per request segment**, not on the assembled page. A page that
stops mid-sentence still indicates missing speech and needs further diagnosis
at the segment level.

## Generation queue, estimated completion, and cached-page inventory

The `/audio` reader displays readiness for every page of the current lecture,
a percent of cached **pages** (not a percent of generated audio duration),
and active/queued speech jobs. The lecture selector also displays ready/total
page counts for the selected track, profile, voice, and synthesis speed. A
recording generated for a different cache identity is not counted as ready.

Press **Play page** for interactive priority, **Cache whole lecture** for
background generation, or enable prefetch for lowest priority. These requests
share the existing per-profile DKPS worker queue (two workers, maximum eight
outstanding jobs). The Breeze server maintains its own one-worker queue across
clients. Its passage counts are returned during generation and displayed in
the reader. Explicit playback is prioritized ahead of queued prefetch and
background cache jobs; a passage already running on the GPU is not preempted.

**Stop generation** cancels unfinished jobs belonging to the selected lecture.
Individual queue entries also provide **Cancel lecture** for an older lecture.
Queued DKPS work is removed immediately. Running paragraph80 work forwards a
`DELETE` request to the local-ai job API; the server stops between passages.
Already cached pages remain available. Pausing playback does not, by itself,
cancel generation.

The backend records wall time per successfully generated page in
`audio-cache/generation-times.sqlite3` and estimates remaining work using the
median seconds per word of recent recordings made with matching settings.
Until enough samples exist, it uses a preliminary 0.6 s/word estimate. ETAs
include an approximate queue wait and can change if the model retries a
passage. A running job that outlasts its estimate reports the elapsed overrun,
not a misleading zero-second ETA. The database stores hashes of synthesis settings, word counts, and
wall times; it does not store voice identifiers or transcript text.

Reader endpoints (all configured-profile lookups):

- `GET /api/audio-generation/inventory?track=g2&profile=...&voice=...&speed=1&lecture_id=000000`:
  exact cached-page states, queue items, cache percentage, and ETA information.
- `GET /api/audio-generation/catalog?track=g2&profile=...&voice=...&speed=1`:
  ready/total counts for the lecture list.
- `POST /api/audio-lectures/{id}/pages/{page}/render`: existing API accepts
  optional `purpose` (`playback`, `cache`, or `prefetch`).
- `POST /api/audio-generation/cancel`: accepts `track`, `profile`, `voice`,
  `speed`, and `lecture_id`, and cancels unfinished work for that lecture and
  synthesis configuration.

For paragraph80, this integration requires a local-ai Breeze server supporting
`/v1/audio/jobs`. Deploy the server overlay first. To temporarily retain the
previous blocking Breeze synthesis API while keeping DKPS status and cache
inventory, set `DKVIS_AUDIO_BREEZE_JOB_API=0` and restart the reader. That
compatibility mode cannot interrupt an HTTP synthesis already underway; it
still cancels queued jobs and refuses to publish cancelled pages.
