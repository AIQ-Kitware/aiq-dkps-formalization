# Shared presentation production

Use `python -m dkvis.presentation {list,slides,text,video}`. Deck manifests,
not this package, select the mathematics, scenes, and transcript. The package
can be imported without Manim, VTK, or a speech server; rendering loads those
dependencies only when needed.

| File | Responsibility |
| --- | --- |
| `build.py` | Manim rendering, asset preparation, HTML/PDF export and final-frame handouts |
| `narration.py` | Read the manifest-selected transcript; export slide/build text and a manifest |
| `audio.py` | Speech requests, sentence-aware chunking, cutoff retries, cache keys and lossless joins |
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
