# Shared presentation production

Use `python -m dkvis.presentation {list,slides,text,video,audio}`. Deck manifests,
not this package, select the mathematics, scenes, and transcript. The package
can be imported without Manim, VTK, or a speech server; rendering loads those
dependencies only when needed.

| File | Responsibility |
| --- | --- |
| `build.py` | Manim rendering, asset preparation, HTML/PDF export and final-frame handouts |
| `narration.py` | Read the manifest-selected transcript; export slide/build text and a manifest |
| `audio.py` | Speech requests, sentence-aware chunking, cutoff retries, cache keys and lossless joins |
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
