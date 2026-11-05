# Shared presentation production

Use `python -m dkvis.presentation {list,slides,text,video,audio,serve}`. Deck manifests,
not this package, select the mathematics, scenes, and transcript. The package
can be imported without Manim, VTK, or a speech server; rendering loads those
dependencies only when needed.

| File | Responsibility |
| --- | --- |
| `build.py` | Manim rendering, asset preparation, HTML/PDF export and final-frame handouts |
| `narration.py` | Read the manifest-selected transcript; export slide/build text and a manifest |
| `audio.py` | Speech requests, sentence-aware chunking, cutoff retries, cache keys and lossless joins |
| `serve.py` / `library.html` | Local media catalog, chapter lookup, embedded viewers and range-capable file serving |
| `audio_quality.py` | Cached loudness/peak measurements, onset/boundary review reports, compression and two-pass normalization |
| `video.py` | Check clip/note alignment, synchronize builds with audio, write chapters and assemble the video |
| `tts.py` | Load `tts.toml`, ignored `.env` and CLI configuration |
| `media.py` | Media duration and FFmpeg concat-list helpers |
| `timing.py` | Shared append-only operation timings and per-run summaries |
| `paths.py` | Resolve the visualization root without relying on the caller's working directory |

Keep speech chunking and caching independent of lesson content. Preserve the
server-duration guard, full-audio-plus-pause video length, and exact note/build
preflight when changing production code. TTS profiles are shared across decks.
`DKVIS_TTS_PROFILE` selects a machine-local default; `MATCHING_TTS_PROFILE`
remains a fallback for existing `.env` files. Private endpoints never belong in
tracked files or logged settings.

Outputs retain the established `renders/<deck>*` and `slides-<deck>/` layout,
including the `-light` suffix for the light theme. Audio remains under each
deck's `<deck>-narrated/audio/<profile>/` directory, with content-based request
keys. Timings retain `renders/logs/render-timings.jsonl`. Existing artifacts
can be reused when their embedded notes match the transcript.

The old `dkvis.build_slides`, `dkvis.matching_narration`,
`dkvis.matching_video`, and `render_matching_video.sh` commands only preserve
existing invocation patterns. Maintained callers use this package and
`render_video.sh`. The wrappers contain no production logic.


## Measure and repair existing audio

From `visualizations/`, with FFmpeg/FFprobe installed:

```bash
uv run python -m dkvis.presentation audio analyze renders/prereq-projections.narrated.mp4 \
  --timeline renders/prereq-projections-narrated/timeline-crall.json \
  --out renders/audio-quality/projections-analysis

uv run python -m dkvis.presentation audio repair renders/prereq-projections.narrated.mp4 \
  --timeline renders/prereq-projections-narrated/timeline-crall.json \
  --out renders/audio-quality/projections-corrected
```

Choose a fresh output directory for each repair. Open `report.html` for original
and corrected video players, clickable RMS plots, and timestamped candidate
issues. `report.json` retains the numerical measurements. Repair writes
`leveled.mp4`, a lossless `leveled.wav`, processed request chunks and a new
timeline. Originals remain available. The video stream and chapters are copied;
speech lengths, pauses and slide timestamps are preserved. This requires neither
the speech server nor Manim. Analysis also accepts a WAV/MP3 without a timeline;
request-boundary diagnostics require a timeline and its source audio.

Measurements include integrated loudness (LUFS), true peak (dBTP), loudness
range (LU), sample peaks, near-rail samples and a 100 ms RMS envelope. The latter
uses decoded mono audio; near-rail samples flag a possible saturation problem,
not proof of clipping in the original multichannel signal. For each request,
we compare the 90th percentile of active RMS windows in its first two seconds
with the remaining body. Boundary checks compare the preceding request's last
two active seconds with the next request's first two. A difference above 6 dB
is a listening candidate. Windows below −55 dBFS are excluded; this is a level
gate, not speech recognition. Natural emphasis, phonetics and breathy endings
can trigger flags. The report helps locate issues; it does not certify speech
quality, identity consistency, pronunciation or completeness.

Exact request membership comes from `.parts.json` join sidecars. Older renders
use `audio_join` entries in `renders/logs/render-timings.jsonl`. Keep those logs
and the raw audio cache with a render: if a joined file has no provenance, repair
refuses to guess its request boundaries.

## Configure processing and speech delivery

`tts.toml` has a shared `[postprocess]` table; override individual values in
`[profiles.NAME.postprocess]`. Future `video` runs automatically process cached
raw speech with these settings. Set `enabled = false` to bypass processing.
The initial speech preset uses:

- a 60 Hz high-pass filter;
- preliminary per-request level matching, with a maximum upward gain of 24 dB
  before compression;
- a gentle compressor: −20 dBFS threshold, 2.5:1 ratio, 5 ms attack, 180 ms release;
- measured two-pass FFmpeg `loudnorm`, targeting −18 LUFS and −1.5 dBTP, with a
  7 LU loudness-range target. Peak protection may prevent exact target loudness.

The preliminary gain cap is not a total amplification limit: the final
normalizer can add gain. Compression and normalization cannot repair a clipped
source or change an excited intonation into a calm one. The final AAC encode can
slightly overshoot the WAV's true-peak target; the report measures the finished
MP4 as well as the chunks. See FFmpeg's [loudnorm](https://ffmpeg.org/ffmpeg-filters.html#loudnorm)
and [acompressor](https://ffmpeg.org/ffmpeg-filters.html#acompressor) documentation.

Raw request keys depend on speech text/model/settings. Processing keys depend
on raw content, processing settings and FFmpeg version, so changing loudness or
compression reuses speech while rebuilding its processed copies. A different
prompt or chunk size requires new speech. All caches, reports, WAVs, MP4s and
operation logs live under ignored `renders/`; commit only source/configuration.
Timing records include measurement, processing and remux durations, cache hits,
and processing settings, alongside the existing speech and video timings. Nested
operation times overlap and must not be added to estimate wall time.

The Crall profile now allows up to 110 words / 750 characters per request, with
the existing 60-second cutoff detection and subdivision retained. Its prompt asks
for warm, clear delivery at steady conversational loudness with restrained
emphasis. Explicit `cfg_scale = 2.0` reduces the instruction-conditioned server
default of 4.0 observed in the current local Breeze implementation. These are
starting settings for the next synthesis/listening comparison; the offline
repairs measure only the mechanical processing, not the revised prompt.


## Render different narrators concurrently

Final videos include the configured narrator identity, for example
`renders/001000_prereq-projections.crall-breeze-tts2.narrated.mp4` and
`renders/001000_prereq-projections.kokoro.narrated.mp4`. By default this is the
profile name; `narrator_voice` combines a reference-speaker label with the model.
Use separate profiles for separate narrators. A custom `--output` must also be distinct for each run.

Build the shared visual slides once, then narrate them in parallel:

```bash
./render_video.sh --deck prereq-projections --tts-profile crall --skip-render &
./render_video.sh --deck prereq-projections --tts-profile kokoro --skip-render &
wait
```

Run `make slides DECK=prereq-projections` first if the slide clips need rebuilding.
Concurrent Manim builds of the same deck share visual output paths, so use
`--skip-render` for both narration runs. Narration exports, audio caches, clips,
concat lists, chapters, timelines and final videos are profile-specific.
Preview clips and assembly metadata are also separate from full runs. Two runs
using the same profile still share its caches and outputs; run those sequentially.

Use `renders/<deck>-narrated/timeline-<narrator>.json` for analysis and repair
(or `timeline-<narrator>.preview.json` for a preview). New renders no longer write
the ambiguous `timeline.json` alias. Existing videos and timelines retain their
old names until explicitly rebuilt; the legacy unsuffixed video is not updated.


## Avoid clicks at narration boundaries

The default `postprocess.edge_fade_ms = 8.0` ramps each speech request to and
from zero over eight milliseconds. The final assembly also ramps the edges of
individual narrated builds. No samples or slide pauses are removed. Set this
value to zero to disable the fades.

Final videos now assemble a lossless `narration-<profile>.wav` directly from the
source speech at the build timestamps, then encode that complete track to AAC
once. The video stream is still copied. The independently encoded audio in the
intermediate video clips is not used for the final soundtrack. This avoids
carrying separate AAC priming/padding boundaries into the full presentation.
The lossless assembly is profile-specific, including a separate preview variant.

To apply only the boundary treatment to an existing video, preserving its levels
and compression:

```bash
uv run python -m dkvis.presentation audio repair \
  renders/prereq-projections.kokoro.narrated.mp4 \
  --timeline renders/prereq-projections-narrated/timeline-kokoro.json \
  --profile kokoro --edges-only --out renders/audio-quality/projections-clicks
```

As with other repairs, choose a fresh output directory. The report now lists
nonzero source edges above −50 dBFS. Such an edge can click when joined to
silence; it is not proof that a listener will hear a click. A fade cannot remove
an artifact already inside a spoken word. Listen to the comparison before
replacing a previously rendered video. Originals are preserved. Each report keeps an `original` media snapshot and a
timeline snapshot so a concurrent new render cannot change its comparison.


## Local library server

`make serve` (or `python -m dkvis.presentation serve` with the `serve` extra)
starts the read-only catalog and player for `renders/`. See the
[quick start](../../README.md#browse-and-watch-rendered-material) for ports,
network binding and directory options. Static media uses Starlette's byte-range
implementation; keep that behavior when modifying the server. HTML asset paths
remain relative under `/files/`, and PDFs use the browser's built-in viewer.

The catalog scans one selected folder at a time and lists only registered decks.
Loose preview clips and orphan transcript exports do not become lecture entries.
Lecture titles and ordering
come from the existing YAML index. Narrated MP4 names select their own profile's
timeline; previews use preview timelines, repaired videos use their neighboring
timeline, and MP4 metadata supplies a fallback. No video is transcoded by this
server. Position storage includes the file's modification time, so a new render
does not inherit an old version's timing. The `serve` extra stays independent of
Manim and TTS dependencies. Run its HTTP tests with `uv run --extra serve --extra
test pytest -q tests/test_media_server.py`.


## Narrator names and native captions

The `crall` configuration profile now writes public video, timeline, and
transcript variants named `crall-breeze-tts2`. Its `narrator_voice = "crall"`
setting combines the reference-speaker label with the selected model. Changing
`--model` also changes that public name; overriding `--voice` uses the
new voice identifier instead of the configured reference-speaker label. For a new reference
voice, give it its own profile and `narrator_voice` setting.

Keep using `TTS_PROFILE=crall` in commands. Raw audio, processed audio, and encoded
segment caches retain their existing profile directories; the public rename does
not itself require new synthesis or encoding. Existing videos keep their old
filenames and recorded provenance until rebuilt.

Captions use the browser video player's native CC/subtitles menu, including in
fullscreen. They start off. Availability and placement of the menu depend on the
browser; no separate page checkbox is needed. Caption words are the recorded TTS
input, with approximate timing within each request.

Timestamp buttons seek 50 milliseconds inside the selected passage (less for
a very short passage). This avoids displaying the preceding video frame when
an exact boundary falls between frames or browser timestamps are rounded.


## Viewer feedback

The lecture library has a feedback box below navigation and above the spoken
transcript. **Save feedback** stores one JSON record per submission in
`visualizations/feedback/` by default, outside the disposable `renders/` tree.
This is viewer-authored data: back it up separately; it is ignored by Git.
For a custom media directory, feedback defaults to a sibling `feedback/` folder.
Use `serve --feedback-directory /path/to/feedback` to choose another location
outside the publicly served media tree.

Records include feedback text, UTC submission time, the stable lecture ID,
the selected file/narrator, its generation metadata and SHA-256 fingerprint,
and the playback timestamp and chapter. The timestamp is captured when typing
starts. Original generation attribution and current lecture source attribution
are stored separately. HTML and PDF views can receive feedback too; lectures
with no rendered media receive lecture-level feedback.

Drafts are saved locally in the browser for each selected file generation and
restored when switching lectures or voices. A failed save leaves the text in
place. If a file was regenerated after the viewer selected it, saving is rejected
rather than attributing the old feedback to the new video; copy the draft before
refreshing and reviewing the updated lecture. Restart the server after updating
the Python code; no media rebuild is needed for the feedback UI.
