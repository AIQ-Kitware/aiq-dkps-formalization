# Davis--Kahan visualizations

Executable geometric visualizations and narrated learning material for the
Davis--Kahan formalization and its transport extensions. The library includes
sine-theta geometry, the other angle bounds, the Proposition 4.4 counterexample
and repair, and the real matching proof. Numerical examples are shared by the
renderers rather than reimplemented in individual presentations.

This directory is not part of the Lean build. It is a companion for developing
intuition, figures, talks, and manuscript animations. Numerical assertions here
do not replace the Lean proofs.

The [lecture project vision and history plan](docs/planning/lecture-project-vision-and-history.md)
sets the north star: the entire Davis–Kahan paper, this project's extensions,
and the prerequisites needed to understand them, with a learning map progressively
validated against Lean 4 proofs. Useful lectures can be drafted before that
formal correspondence is complete.

## Where to start

| Task | Read or edit |
| --- | --- |
| Write or revise lecture content | [Lecture style rules](LECTURE_STYLE_RULES.md), then the [authoring guide](dkvis/learning/README.md) |
| Find a lecture and its prerequisites | [Lecture index](lectures/index.yaml); generated [lecture navigation](lectures/README.md) |
| Change a transcript, quiz, or model attribution | The lecture's numbered folder under `lectures/` |
| Change its scenes or numerical examples | Its topic under `dkvis/learning/` |
| Choose scene order or register a deck | `dkvis/decks/` |
| Change rendering, TTS, captions, feedback, or the player | [Production guide](dkvis/presentation/README.md) and `dkvis/presentation/` |
| Change shared layout or Lean code rendering | [Component guide](dkvis/components/README.md) and [implementation notes](briefs/slide-authoring.md) |
| Look up an older scene, VTK explorer, or mathematical illustration | [Detailed scene reference](SCENE_REFERENCE.md) |

Authored source belongs in Git. `renders/`, `media/`, and `slides-*/` are
regenerable outputs. `.env` holds local settings; `tts.toml` holds shared TTS
profiles. Viewer feedback lives separately in the ignored `feedback/` directory:
it is authored data to back up, not a render cache to clean.

## Setup

This Python project is independent of the Lean build and supports Python
3.11–3.13. From `visualizations/`, install the parts needed for slides, serving,
and tests:

```bash
uv sync --extra slides --extra serve --extra test
```

Add `--extra vtk` for the VTK scenes. Manim also needs the host's Cairo, Pango,
FFmpeg, and LaTeX packages. The [production guide](dkvis/presentation/README.md)
explains the common commands and TTS configuration.

## Render narrated lectures

From `visualizations/`, start a configured TTS server and render a lecture or
all registered lectures in dependency order:

```bash
make video DECK=operators-sylvester TTS_PROFILE=crall-math-dk-v2-breeze-tts2
make lectures-video TTS_PROFILE=crall-math-dk-v2-breeze-tts2
make prerequisites-video TTS_PROFILE=crall-math-dk-v2-breeze-tts2  # prerequisite series only
```

`crall-math-dk-v2-breeze-tts2` uses the v2 reference sample with Breeze TTS 2;
`kokoro` uses Kokoro. The web UI labels voices as `<reference>-<model>`
(for example, `crall-math-dk-v2-breeze-tts2` or `af_heart-kokoro`). The
Kokoro profile requires `KOKORO_TTS_ENDPOINT` in the environment or this
directory's `.env`. For a local CPU server on port 8881:

```bash
KOKORO_TTS_ENDPOINT=http://127.0.0.1:8881/v1/audio/speech \
  make lectures-video TTS_PROFILE=kokoro
```

See `services/tts/README.md` in the local-ai repository for provisioning
Breeze and Kokoro. Use `SKIP_RENDER=1` only when the slide visuals
for all selected lectures already exist; it avoids rebuilding those visuals
when running another narration profile concurrently. Profiles use separate
audio and video outputs. Completed speech chunks and video segments are cached,
so rerunning after interruption reuses matching work; the interrupted request
must finish again. A batch stops at the first failure and can be rerun.

### Reference identity and generation provenance

Use a reference basename plus model for a cloned-voice profile, such as
`crall-math-dk-v2-breeze-tts2`. Its request specifies voice `crall-math-dk-v2`
and model `breeze-tts2`; the server loads `crall-math-dk-v2.wav` and
`crall-math-dk-v2.txt`. This is the new default in `tts.toml`. The legacy `crall`
profile still requests the original `crall-math-dk` reference.

New output suffixes and web-UI labels include the actual reference/voice and
model. A new basename gives v2 separate speech caches and video outputs; it does
not require `REFRESH_AUDIO=1`. Existing files retain their original names.

Generation sidecars and timeline chunks retain request settings, reference
filenames, and available server runtime/model revisions. Set
`DKVIS_TTS_REFERENCE_DIR` in ignored `.env` to a local reference folder to also
record file sizes, modification dates, and the reference transcript text. Local
observations are labelled as such; unavailable runtime metadata stays explicit.
Full TTS configuration and audio-processing settings accompany each new video.
See the [production guide](dkvis/presentation/README.md#reference-and-generation-records)
for the distinction between build-time settings and the original synthesis of
cached chunks. Reference samples are identified by their versioned basenames;
no reference-file hashing is added.

### Regenerate audio after changing a voice reference

Replacing the reference recording or reference transcript on the Breeze server
under the same voice name does **not** invalidate cached speech. Request keys
include the speech text, endpoint, model, voice name, and request settings;
they do not include the server's reference files.

From `visualizations/`, force fresh speech and rebuild one narrated video:

```bash
make video DECK=prereq-basics TTS_PROFILE=crall-math-dk-v2-breeze-tts2 SKIP_RENDER=1 REFRESH_AUDIO=1
```

For every indexed lecture:

```bash
make lectures-video TTS_PROFILE=crall-math-dk-v2-breeze-tts2 SKIP_RENDER=1 REFRESH_AUDIO=1
```

`SKIP_RENDER=1` reuses existing slide renders; omit it if those also need updating.
`REFRESH_AUDIO=1` resynthesizes all speech in the selected lecture(s), processes
it, and reassembles the videos. It replaces matching raw speech-cache files.
Leave the flag off for normal cached builds. Alternatively, a new server voice
name changes the request key and keeps its raw speech distinct.

The equivalent direct command is:

```bash
./render_video.sh --deck prereq-basics --tts-profile crall-math-dk-v2-breeze-tts2 --skip-render --refresh-audio
```

## Browse and watch rendered material

From `visualizations/`, start the media library:

```bash
make serve                         # http://127.0.0.1:8000
make serve PORT=8001                # use another port beside an existing server
```

The page lists videos by narrator, HTML presentations, and PDF handouts. It has
native video seeking, playback-speed controls, skip buttons, remembered playback
positions, links to particular times, and chapters from the matching render
timeline (or embedded MP4 chapters). HTML and PDFs open in the same viewer or in
a separate tab. Use **Browse folders** for repair reports and nested outputs;
**Refresh** discovers new renders. No Manim or speech server is required.

The server supports HTTP byte ranges, so seeking can fetch the needed part of a
video instead of waiting for a complete download. This uses Starlette's
[FileResponse support](https://starlette.dev/responses/).

```bash
uv run --isolated --extra serve python -m dkvis.presentation serve --port 8001
# Optional: access from another machine on your network.
make serve HOST=0.0.0.0 PORT=8001
# Optional: choose another media directory.
uv run --isolated --extra serve python -m dkvis.presentation serve --directory /path/to/media
```

The server uses an isolated Python environment, so starting it does not change
the environment used by concurrent render jobs.

**After adding a new lecture, restart the server and refresh the browser.**
The running Python process retains its deck registrations and cached lecture
index. For example, a server started before `000010` was added cannot discover
that new deck using the page's Refresh button alone. New or replaced renders
of an already registered deck do appear after Refresh, without a server restart.


The default directory is this project's `renders/`, independent of the current
working directory. The default address is loopback. Stop with Ctrl+C. Playback
positions and speeds are stored in the browser. The feedback form saves comments
on the server in the separate, Git-ignored `feedback/` directory. Files still being
replaced by a render appear with their new version after refresh.

The library has one entry per registered deck. Loose preview and diagnostic
clips are excluded from the catalog; their files remain available by direct URL.
Select a narration voice or switch to HTML slides, PDF slides, or the PDF handout
inside that entry. Deck IDs remain stable
when the lecture organizer changes an ordering number. Transcript and document
links open the raw files in another tab.

The spoken-transcript panel shows the text used by the selected video, with
clickable timestamps for replaying a mispronounced passage. It recovers existing
TTS requests from their raw/processed/joined audio sidecars; it does not substitute
a newly edited script for old audio. The current authored transcript is a
separately labelled link. Captions are optional and **off by default**; enable them through the player's
CC toggle beside the playback controls. Native subtitle options remain available
in the player menu. Playback speed can be set up to 4×. Captions use
the same speech text, with approximate timing within each TTS chunk; no ASR or
new TTS calls are required. If historical speech caches are gone, the panel
reports missing or partial coverage instead of inventing a transcript.

Expand **Generated components and dates** for file links and timestamps. New
exports record generation dates; older artifacts fall back to file-modification
times. Speech dates refer to the actual cached chunks used by that narration.
**Slide and transcript model provenance** separates current source attribution
from the snapshot recorded when an artifact was generated. Missing historical
metadata and unknown model variants stay explicitly unknown.

New video timelines retain speech text, chunk boundaries, and durations so captions/transcripts
survive later audio-cache cleanup. The renderers write ignored
`<artifact>.metadata.json` sidecars containing generation time, source revision,
model attribution, and relevant rendering or TTS model/voice settings. Private
TTS endpoints are excluded. These records accompany their artifacts when the
organizer renumbers exports. Source attribution lives in each lecture's tracked
`provenance.yaml`; see [the authoring guide](dkvis/learning/README.md#model-attribution).
Restart the server after updating its Python code, then refresh the browser.

### Updating one scene

For a lecture that has already been built, edit the scene and its corresponding
narration section, then run from `visualizations/`:

```bash
make video DECK=prereq-complementary-projection TTS_PROFILE=crall-math-dk-v2-breeze-tts2 UPDATE_SCENES="CpSplit"
```

This renders only `CpSplit`, exports the complete HTML/PDF/handout, and assembles
the **full lecture**. Multiple names are allowed inside the quotes. The separate
`SCENES="..."` / `--scenes` video option still makes a selected-scene **preview**.
Do not combine `UPDATE_SCENES` with `SKIP_RENDER=1`. If model attribution changes,
include the cover too, for example `UPDATE_SCENES="CpTitle CpSplit"`, to refresh
its model badge. Scene selection is explicit rather than an automatic source
dependency analysis.

For slides alone, use `make slides DECK=... SCENES="CpSplit"`. After that, a
`make video DECK=... TTS_PROFILE=crall-math-dk-v2-breeze-tts2 SKIP_RENDER=1` reassembles the current
pieces. Changing a shared visual style, adding slides, or changing their order
can affect every scene's chrome and should use a full render instead.

Encoded narration segments are now cached using hashes of the actual visual
and audio files, plus FPS, pauses, encoder settings and FFmpeg version. Cache
hits also verify the output bytes. Text/settings-based TTS caches and audio
processing caches remain separate. Old segments without an input manifest need
one encoding pass to establish a trustworthy cache. Subsequent runs reuse
unchanged segments; they still assemble the full lossless narration and final
MP4 with current chapters and transcript metadata. Hashing reads the files but
does not rerender or re-encode them.

Lecture covers display the same vector robot used by the Kitware talk, an
LLM-generated disclosure, and separate recorded slide/transcript model names.
Missing model variants remain explicitly unrecorded. Matching presentations now
also have dedicated short covers. The badge is visual; title narration remains
just the main concept.

Git is the history for authored scenes, transcripts, model attribution, and
rendering code. For example, `git log --follow -- lectures/001500_complementary_projection/lecture.md`
from `visualizations/` follows the transcript through renames. Artifact metadata
continues to record source revisions and generation settings; generated videos
are not archived as a historical library or committed to Git.

A rebuilt slide cover appears in an existing MP4 only after video assembly.
The player resumes saved playback positions; seek to 0:00 to check the opening.

## Learning modules and a shared production pipeline

The [prerequisite lecture series](dkvis/learning/PREREQUISITES.md) contains
six narrated modules: a basic mathematics refresher, subspaces and projections, complementary projections
and geometric error, singular values
and displacement cost, the matrix exponential, and
feasible variations and stationarity. They have independent introductions, historical context, worked
visual explanations, summaries, and self-checks. Each indexed lecture now ends
with two multiple-choice questions: spoken choices, eight seconds to think,
then a highlighted answer and explanation. Pause for more time when needed.
The questions and speech live together in each lecture folder’s `quiz.yaml`. `make prerequisites` builds
all six, including TTS-ready text; it does not contact a speech server.

Every indexed lecture supplies its own local setting and notation. The Lean
closing section shows one fact per slide: symbolic formula, visible scope,
JuliaMono code with syntax colors, and a green library-proof application. Full
Lean context and imports stay in the copyable `facts.lean` files. Set
`DKVIS_LEAN_FONT` to use another installed font. Each lecture's numerical
considerations are an explicitly optional bonus after the core/Lean material and
before its study questions.

The [lecture library](lectures/README.md) is indexed by `lectures/index.yaml`.
Its prerequisites determine a NetworkX topological order. The organizer
preserves existing six-digit folder numbers and fills gaps for new lessons;
an explicit `--rebalance` restores 001000, 002000, 003000, ... spacing.

```bash
uv run python -m dkvis.lectures                     # preview
uv run python -m dkvis.lectures --apply             # allocate folders; preserve numbers
uv run python -m dkvis.lectures --rebalance --apply # deliberately renumber
```

Python imports, deck IDs, scene folders, and speech caches use stable names.
Public HTML, PDF, and video filenames carry their six-digit lecture prefix.
Applying the organizer also renames existing public exports without rebuilding
their contents; existing videos need a new video build to include the questions.
Decks resolve their transcript paths from stable lecture IDs, so folder moves
do not require editing import statements or hard-coded paths. The generated
library catalog is refreshed when the organizer is applied.
The catalog and per-lecture navigation READMEs are generated and gitignored;
run `uv run python -m dkvis.lectures --apply` after cloning to recreate them.

[The module catalog](dkvis/learning/README.md) maps learning goals and
prerequisites to existing material and documents how to author a module.
[Real matching](dkvis/learning/matching/README.md) is the first complete topic
package: its scenes and numerical model live in the topic package; its two
transcripts live in the indexed lecture folders. Frozen reference presentations retain their content, order, and output names.
The indexed matching lectures also receive the review questions and public prefixes.

The [accepted operator-foundation series](dkvis/learning/operators/README.md)
adds min-max/Weyl stability, operator absolute value/polar decomposition, and
Sylvester equations with ordered spectral separation. `make operators` builds
all three with speech text; the topic guide links the accepted Tau Ceti modules
and distinguishes DKPS adaptations from independent implementations.

From this directory:

```bash
make list
make slides DECK=matching-proof-talk
make text DECK=matching-proof-talk
make video DECK=matching-proof-talk TTS_PROFILE=kokoro
```

The same commands work for a new deck once it is registered. `slides` renders
Manim scenes, exports portable HTML/PDF/handout, and exports any authored
transcript. `text` needs neither Manim rendering nor a speech server. `video`
uses the configurable speech server and joins the narration to the animations.
Only decks declaring a transcript are offered for narration; older decks
remain available as slides.

The common Python entry point is `python -m dkvis.presentation`:

```bash
uv run python -m dkvis.presentation list
uv run python -m dkvis.presentation text --deck matching-proof-talk
./render_video.sh --deck matching-proof-talk --skip-render --tts-profile kokoro
```

`make slides` uses the Manim extras. For decks using VTK, install that extra too,
or run with it explicitly:

```bash
uv run --extra vtk --extra slides python -m dkvis.presentation slides part2-3d --handout
```

Source ownership is split as follows:

| Location | Owns |
| --- | --- |
| `lectures/<number>_<topic>/` | Authored transcripts, quizzes, model provenance, and Lean companions |
| `dkvis/learning/<topic>/` | Lesson scenes, numerical examples, learning goals and source references |
| `dkvis/decks/` | Presentation composition, ordering, depth, footer, and transcript selection |
| `dkvis/components/`, `dkvis/slide_style.py`, `dkvis/notation.py`, `dkvis/palette.py` | Shared visual primitives, layout, notation and colors |
| `dkvis/presentation/` | Slide export, transcript parsing, TTS configuration, audio/video production, timings and output paths |

The older `slides_*.py`, numerical models, and VTK demos keep their locations
until a topic is deliberately migrated. They are working source material, not
duplicate implementations to discard. Old build and matching commands remain
small compatibility entry points; new content uses the shared pipeline.

Each narrated deck declares `DeckSpec.narration`, a path relative to
`visualizations/`. Its ordered scene sections and animation beats are checked
against the rendered notes before speech is requested. No matching-specific
list remains in the production tools. Rendered outputs and audio stay ignored;
source scenes, scripts, manifests, and source references belong in Git.

## YWS population-gap lecture

**`yws-population-gap`** (003875) explains Theorem 2 through a residual sandwich,
population spectral blocks, and orthogonal frame alignment. It includes checked
Lean applications and the corrected rectangular extension. See the
[YWS guide](dkvis/learning/yws/README.md) for the transcript, source correspondence,
and build commands.

```bash
make video DECK=yws-population-gap TTS_PROFILE=crall-math-dk-v2-breeze-tts2
```

## People behind the mathematics

Two portrait-based companions introduce careers, publications, and mathematical
connections: **`history-people-foundations`** (000670) and
**`history-people-operators`** (000835). See the [people guide](dkvis/learning/history_people/README.md).
Images carry visible attribution and license/source links; only the
[selection manifest](dkvis/assets/history-images.yaml) and access logic are
committed. The [asset-store guide](docs/EXTERNAL_ASSETS.md) explains offline
rendering and rsync, wormhole, or IPFS transfer of images with their source records.

## Historical overview

**`history-overview`** (000505) introduces the people and publications behind
subspace geometry, Davis–Kahan, YWS, and the transport extensions, with a brief
Quench application. It has a standalone transcript, publication cards, and two
study questions. See the [history guide](dkvis/learning/history/README.md) for
source records, concise historical triage, and build commands.

```bash
make video DECK=history-overview TTS_PROFILE=crall-math-dk-v2-breeze-tts2
```

## Narrated sine-theta lecture

The numbered course uses **`sine-theta-lecture`** (003750), the narrated edition
of the short reference visuals with Qwen's transcript and study questions:

```bash
make video DECK=sine-theta-lecture TTS_PROFILE=crall-math-dk-v2-breeze-tts2
```

It is also included in `make lectures-video`. The eighteen-scene
`sine-theta-short` remains the original reference presentation. A separate
transcript file must be both registered in the course and bound to the animation
builds before it can produce a narrated course video. See the
[topic guide](dkvis/learning/sine_theta/README.md) for sources, attribution, and
incremental render commands.

## Validation and scene references

Run the tests from `visualizations/`:

```bash
uv run --extra serve --extra test pytest -q
```

The [detailed scene reference](SCENE_REFERENCE.md) preserves the mathematical
walkthroughs, reference-deck commands, and VTK examples formerly included here.
It is a lookup document; new lectures use the shared authoring and production
workflow linked above.

**`operators-pvm`** (002916) introduces projection-valued measures through
spectral windows, scalar energy measures, and integration. Continuous and
unbounded examples explain strong convergence and operator domains. Three
accepted Tau Ceti laws appear alongside their symbolic statements. See the
[PVM guide](dkvis/learning/pvm/README.md) for sources, transcript, and rendering.
