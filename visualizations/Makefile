# Build the Davis--Kahan slide decks and demos.  Run from visualizations/.
#
#   make                 # list targets
#   make all             # short deck + every part + the full deck, 1080p30, HTML + standalone HTML + PDF
#   make final           # the same at the full 1080p60
#   make rebuild         # clean, then make all
#   make short           # the preserved 15-minute reference deck
#   make kitware         # completed short talk, plus portable standalone HTML
#   make comprehensive   # complete narrative collection, plus portable standalone HTML
#   make study           # earlier long-form learning composition
#   make part3           # one part of the full talk, with its own HTML (part1 ... part7)
#   make full            # every part, then the full deck assembled from them
#   make full SCENES="S05Residual S08Why"   # re-render only those scenes, reconvert
#   make short QUALITY=l # fast 480p draft
#   make clean-short     # remove one deck's outputs so the next build starts fresh
#   make full THEME=light  # light background; outputs get a -light suffix beside the dark ones
#   make standalone      # single-file HTML (videos embedded) of every built deck and part
#   make handout         # one-page-per-scene PDFs of every built deck and part
#   make serve           # browse audio lectures, videos, slides and PDFs
#
# Indexed lectures add their six-digit order prefix to public output filenames.
# Every reference deck writes renders/<deck>.html (+ .pdf, .handout.pdf, <deck>_assets/) and keeps
# its rendered scenes in slides-<deck>/ (with THEME=light: <deck>-light).  renders/<deck>.html needs the
# <deck>_assets/ folder beside it; renders/<deck>.standalone.html does not.

UV      ?= uv
RUN     := $(UV) run --extra vtk --extra slides --extra test
SLIDES_RUN := $(UV) run --extra slides
DECK ?=
QUALITY ?= h
# 1080p renders at 30 fps unless asked for more (FPS=60, or `make final`); drafts keep the quality's own rate.
FPS     ?= $(if $(filter l m,$(QUALITY)),,30)
JOBS    ?=
PDF     ?= 1
UPDATE_SCENES ?=
SCENES  ?=
TTS_PROFILE ?=
TTS_CONFIG ?=
TTS_ENDPOINT ?=
TTS_MODEL ?=
TTS_VOICE ?=
TTS_LANGUAGE ?=
TTS_RESPONSE_FORMAT ?=
TTS_TIMEOUT ?=
TTS_INSTRUCTION ?=
TTS_REQUEST ?=
TTS_SETTINGS ?=
EXPERIMENT_SCENES ?= RrCompress RrQuotient RrSolve
CONDITIONING_MODES ?= original previous anchored
VOICE_DIR ?=
REFERENCE_AUDIO ?= $(VOICE_DIR)/crall-math-dk-v2.wav
REFERENCE_TEXT ?= $(VOICE_DIR)/crall-math-dk-v2.txt
EXPERIMENT_ARGS ?=
VIDEO_ARGS ?=
# Keep each TTS value (including spaces or apostrophes) one shell argument.
shell_quote = '$(subst ','"'"',$(1))'
TTS_FLAGS = $(if $(TTS_CONFIG),--tts-config $(call shell_quote,$(TTS_CONFIG))) \
            $(if $(TTS_PROFILE),--tts-profile $(call shell_quote,$(TTS_PROFILE))) \
            $(if $(TTS_ENDPOINT),--endpoint $(call shell_quote,$(TTS_ENDPOINT))) \
            $(if $(TTS_MODEL),--model $(call shell_quote,$(TTS_MODEL))) \
            $(if $(TTS_VOICE),--voice $(call shell_quote,$(TTS_VOICE))) \
            $(if $(TTS_LANGUAGE),--language $(call shell_quote,$(TTS_LANGUAGE))) \
            $(if $(TTS_RESPONSE_FORMAT),--response-format $(call shell_quote,$(TTS_RESPONSE_FORMAT))) \
            $(if $(TTS_TIMEOUT),--timeout $(call shell_quote,$(TTS_TIMEOUT))) \
            $(if $(TTS_INSTRUCTION),--instruction $(call shell_quote,$(TTS_INSTRUCTION))) \
            $(if $(TTS_REQUEST),--request-json $(call shell_quote,$(TTS_REQUEST))) \
            $(if $(TTS_SETTINGS),--tts-settings-json $(call shell_quote,$(TTS_SETTINGS)))
PORT ?= 8001
HOST ?= 0.0.0.0
AUDIO_TTS_PROFILE ?=
AUDIO_TTS_ENDPOINT ?=
SKIP_RENDER ?= 0
REFRESH_AUDIO ?= 0
# dark or light.  Colors come from dkvis/palette.py (per role and theme) and
# dkvis/notation.py (the role of each symbol).
THEME   ?= dark
export DKVIS_THEME := $(THEME)
SUFFIX  := $(if $(filter dark,$(THEME)),,-$(THEME))

BUILD_FLAGS := --quality $(QUALITY) $(if $(FPS),--fps $(FPS)) $(if $(JOBS),--jobs $(JOBS)) \
               $(if $(filter 1,$(PDF)),--pdf --handout) $(if $(SCENES),--scenes $(SCENES))

# Short target name -> deck name in dkvis/build_slides.py.
DECK_short := sine-theta-short
DECK_full  := sine-theta-full
DECK_part1 := part1-sine-theta
DECK_part2 := part2-3d
DECK_part3 := part3-family
DECK_part4 := part4-prop44
DECK_part5 := part5-process
DECK_part6 := part6-summary
DECK_part7 := part7-glossary
DECK_kitware       := kitware-talk
DECK_comprehensive := comprehensive
DECK_study         := study
DECK_novelty       := novelty-tour
DECK_matching      := matching-proof
DECK_matching-talk := matching-proof-talk
PARTS             := part1 part2 part3 part4 part5 part6 part7
WORKING           := kitware comprehensive study novelty
DECKS      := short full $(PARTS) $(WORKING) matching matching-talk

.DEFAULT_GOAL := help
.PHONY: help setup all rebuild working $(DECKS) $(addprefix clean-,$(DECKS)) $(addprefix present-,$(DECKS)) \
        $(addprefix standalone-,$(DECKS)) standalone $(addprefix handout-,$(DECKS)) handout parts final draft assets app test clean distclean list slides text resources video tts-experiment serve prerequisites operators lectures-video prerequisites-video matching-text matching-video matching-talk-text matching-talk-video

help:
	@awk '/^#/ { sub(/^# ?/, ""); print; next } { exit }' $(firstword $(MAKEFILE_LIST))
	@echo; echo 'Targets:'
	@echo '  tts-experiment     compare original/previous/composite references with phrase-aligned visuals'
	@echo '  list               list all presentations and transcript availability'
	@echo '  serve              browse all 150 audio lectures at /audio plus existing renders'
	@echo '                     AUDIO_TTS_PROFILE overrides reader default (kokoro); AUDIO_TTS_ENDPOINT overrides its URL; TTS_CONFIG selects an ignored private profile config'
	@echo '  operators          build the three accepted operator-foundation lectures'
	@echo '  prerequisites      build the ordered prerequisite lectures and speech text'
	@echo '  prerequisites-video narrate the prerequisite series; TTS_PROFILE=crall-math-dk-v2-breeze-tts2 selects the lecture voice'
	@echo '  lectures-video     narrate every lecture in YAML dependency order'
	@echo '  slides DECK=name   render a presentation and export its transcript when present'
	@echo '  text DECK=name     export slide/build speech text without rendering or TTS'
	@echo '  resources          export all Learn more companions; DECK=name selects one'
	@echo '  video DECK=name    render and narrate; TTS_PROFILE selects a server from tts.toml'
	@echo '                     TTS_CONFIG=tts.local.toml selects an ignored private config instead'
	@echo '                     TTS_ENDPOINT/MODEL/VOICE/LANGUAGE/RESPONSE_FORMAT/TIMEOUT override its settings'
	@echo '                     TTS_INSTRUCTION and TTS_REQUEST (JSON) customize API fields; VIDEO_ARGS passes other CLI flags'
	@echo '                     TTS_SETTINGS (JSON) overrides other client settings, including chunking and postprocessing'
	@echo '    UPDATE_SCENES="Scene" renders just that edit and reassembles the full lecture'
	@echo '  setup              uv sync with the vtk, slides and test extras'
	@echo '  all                short, every part and full, then standalone HTML for each'
	@echo '  final              all at the full 1080p60 (all renders 1080p30)'
	@echo '  rebuild            clean, then all (a from-scratch re-render)'
	@echo '  short              the preserved 15-minute reference deck'
	@echo '  kitware            completed short talk; also build a portable standalone HTML'
	@echo '  comprehensive      all unique scenes, ordered by topic; also build standalone HTML'
	@echo '  study              previous long-form self-study composition'
	@echo '  novelty            standalone deck for the new optimization mathematics'
	@echo '  matching           detailed matching proof; standalone HTML, PDF and narration text'
	@echo '  matching-text      export one plain-text narration file per slide'
	@echo '  matching-video     render a narrated video; TTS_PROFILE selects a server from tts.toml'
	@echo '  matching-talk      separate proof talk with two review questions; HTML, PDF, handout, and narration'
	@echo '  matching-talk-text export the compact talk as slide/build TTS text'
	@echo '  matching-talk-video render the compact talk with the configured TTS profile'
	@echo '  working            build kitware, comprehensive, study, and novelty'
	@echo '  part1 ... part7    one part of the full talk, rendered and converted on its own:'
	@echo '                       1 sin Theta, 2 3D, 3 tan/sin2/tan2 Theta, 4 Prop 4.4, 5 process, 6 summary, 7 notation'
	@echo '  full               every part, then the full deck assembled from their renders'
	@echo '  clean-<deck>       remove one deck'"'"'s renders and scene folder'
	@echo '  present-<deck>     present a built deck live with manim-slides'
	@echo '  standalone-<deck>  write renders/<deck>.standalone.html with the videos embedded (no re-render)'
	@echo '  standalone         standalone HTML for short, full and every part'
	@echo '  handout-<deck>     write renders/<deck>.handout.pdf, one page per scene (no re-render)'
	@echo '  handout            handouts for short, full and every part'
	@echo '  draft              short + full at 480p, no PDF'
	@echo '  assets             re-render the VTK stills and movies the 3D slides use'
	@echo '  app                open the interactive 3D sin-theta demo'
	@echo '  test               run the model tests'
	@echo '  clean              remove all renders, scene folders and manim videos'
	@echo '  distclean          clean, plus the LaTeX and VTK asset caches'
	@echo 'Variables: QUALITY=l|m|h|p|k (default h)  FPS=30|60 (default 30 at h)'
	@echo '           JOBS=n (comprehensive defaults to 2; other decks: one per CPU)'
	@echo '           PDF=0|1 (default 1; also the handout)  SCENES="S05Residual ..."  THEME=dark|light'

setup:
	$(UV) sync --extra vtk --extra slides --extra test

all: short full
	$(MAKE) standalone

final:
	$(MAKE) all FPS=60

rebuild:
	$(MAKE) clean
	$(MAKE) all

draft:
	$(MAKE) all QUALITY=l PDF=0

short study $(PARTS):
	$(RUN) python -m dkvis.presentation slides $(DECK_$@) $(BUILD_FLAGS)

# Render a modest number of LaTeX-heavy novelty scenes concurrently unless
# JOBS is explicitly provided. The generic builder otherwise starts one job
# per CPU, which can be excessive for a presentation full of MathTex labels.
novelty:
	$(RUN) python -m dkvis.presentation slides $(DECK_$@) $(BUILD_FLAGS) $(if $(JOBS),,--jobs 2)

list:
	$(UV) run python -m dkvis.presentation list

prerequisites:
	@for deck in $$($(UV) run python -c 'from dkvis.decks.prerequisites import PREREQUISITES; print(" ".join(d.name for d in PREREQUISITES))'); do \
	    $(MAKE) slides DECK=$$deck || exit 1; \
	done
operators:
	@for deck in $$($(UV) run python -c 'from dkvis.decks.operators import OPERATORS; print(" ".join(d.name for d in OPERATORS))'); do \
	    $(MAKE) slides DECK=$$deck || exit 1; \
	done

lectures-video prerequisites-video:
	@decks="$$($(UV) run python -c 'import sys; from dkvis.lectures import lecture_decks; print(" ".join(lecture_decks("prerequisites" if sys.argv[1] == "prerequisites-video" else None)))' $@)" || exit $$?; \
	for deck in $$decks; do \
	    $(MAKE) video DECK=$$deck || exit 1; \
	done

slides:
	$(if $(DECK),,$(error Set DECK to a presentation name; use make list))
	$(SLIDES_RUN) python -m dkvis.presentation slides $(DECK) $(BUILD_FLAGS) $(if $(JOBS),,--jobs 2) --one-file

resources:
	$(SLIDES_RUN) python -m dkvis.presentation resources $(if $(DECK),--deck $(call shell_quote,$(DECK)))

text:
	$(if $(DECK),,$(error Set DECK to a presentation name; use make list))
	$(UV) run python -m dkvis.presentation text --deck $(DECK) --theme $(THEME)

# Long-passage conditioning comparison, with phrase-aligned existing Manim clips.
tts-experiment:
	@test -n "$(DECK)" || { echo 'Set DECK to a registered narrated deck'; exit 2; }
	@test -d $(call shell_quote,$(VOICE_DIR)) || { echo 'Set VOICE_DIR to the server-shared reference directory'; exit 2; }
	$(UV) run --extra slides --extra align python -m dkvis.presentation experiment --deck $(call shell_quote,$(DECK)) --scenes $(EXPERIMENT_SCENES) --modes $(CONDITIONING_MODES) --voice-dir $(call shell_quote,$(VOICE_DIR)) --reference-audio $(call shell_quote,$(REFERENCE_AUDIO)) --reference-text $(call shell_quote,$(REFERENCE_TEXT)) $(TTS_FLAGS) $(if $(filter 1,$(REFRESH_AUDIO)),--refresh-audio) $(EXPERIMENT_ARGS)

video:
	$(if $(DECK),,$(error Set DECK to a presentation name; use make list))
	./render_video.sh --deck $(DECK) --quality $(QUALITY) --fps $(if $(FPS),$(FPS),30) --jobs $(if $(JOBS),$(JOBS),2) $(if $(filter 1,$(SKIP_RENDER)),--skip-render) $(if $(filter 1,$(REFRESH_AUDIO)),--refresh-audio) $(TTS_FLAGS) $(if $(SCENES),--scenes $(SCENES)) $(if $(UPDATE_SCENES),--update-scenes $(UPDATE_SCENES)) $(VIDEO_ARGS)

matching matching-talk:
	$(MAKE) slides DECK=$(DECK_$@)

matching-text matching-talk-text:
	$(MAKE) text DECK=$(DECK_$(@:%-text=%))

matching-video matching-talk-video:
	$(MAKE) video DECK=$(DECK_$(@:%-video=%))

# Long and completed talk decks always produce portable, single-file HTML.
# The comprehensive deck is large: default to a modest two render processes
# rather than starting one Manim/LaTeX/VTK pipeline per CPU. JOBS overrides it.
kitware:
	$(RUN) python -m dkvis.presentation slides $(DECK_$@) $(BUILD_FLAGS)
	$(MAKE) standalone-kitware THEME=$(THEME)

comprehensive:
	$(RUN) python -m dkvis.presentation slides $(DECK_$@) $(BUILD_FLAGS) $(if $(JOBS),,--jobs 2)
	$(MAKE) standalone-comprehensive THEME=$(THEME)

working: $(WORKING)

parts: $(PARTS)

# Render every part's scenes in one parallel pool, assemble the full deck from them,
# then convert each part to its own HTML (and PDF/handout) without rendering again.
full:
	$(RUN) python -m dkvis.presentation slides $(DECK_full) $(BUILD_FLAGS)
	for part in $(foreach p,$(PARTS),$(DECK_$(p))); do \
	    $(RUN) python -m dkvis.presentation slides $$part --no-render $(if $(filter 1,$(PDF)),--pdf --handout) || exit 1; \
	done

$(addprefix clean-,$(DECKS)):
	@public="$$($(SLIDES_RUN) python -c 'from dkvis.lectures import lecture_output_name; print(lecture_output_name("$(DECK_$(@:clean-%=%))"))')" || exit $$?; \
	    rm -rf slides-$(DECK_$(@:clean-%=%))$(SUFFIX) "renders/$${public}$(SUFFIX)".* \
	    "renders/$${public}$(SUFFIX)_assets"

$(addprefix present-,$(DECKS)):
	$(RUN) manim-slides present --folder slides-$(DECK_$(@:present-%=%))$(SUFFIX) \
	    $$($(RUN) python -m dkvis.presentation slides $(DECK_$(@:present-%=%)) --list)

standalone: standalone-short standalone-full $(addprefix standalone-,$(PARTS))

$(addprefix standalone-,$(DECKS)):
	$(RUN) python -m dkvis.presentation slides $(DECK_$(@:standalone-%=%)) --no-render --one-file

handout: handout-short handout-full $(addprefix handout-,$(PARTS))

$(addprefix handout-,$(DECKS)):
	$(RUN) python -m dkvis.presentation slides $(DECK_$(@:handout-%=%)) --no-render --handout

assets:
	$(RUN) python -m dkvis.vtk_sine_theta_3d --slide-assets media/vtk3d$(SUFFIX)

app:
	$(RUN) python -m dkvis.vtk_sine_theta_3d

test:
	$(RUN) --extra serve pytest -q tests

# manim's partial-movie cache lives in media/videos; removing it forces every
# animation to re-render.  The LaTeX cache (media/Tex) and the VTK assets
# (media/vtk3d) are content-addressed or regenerated on demand, so plain
# `clean` keeps them; `distclean` removes them too.
clean:
	rm -rf renders slides slides-* media/videos media/images media/texts

distclean: clean
	rm -rf media .pytest_cache .ruff_cache


# Seekable media library, HTML slides and PDFs; no Manim/TTS required.
serve:
	$(UV) run --isolated --extra serve python -m dkvis.presentation serve --host $(HOST) --port $(PORT) $(if $(AUDIO_TTS_PROFILE),--audio-tts-profile $(call shell_quote,$(AUDIO_TTS_PROFILE))) $(if $(AUDIO_TTS_ENDPOINT),--audio-tts-endpoint $(call shell_quote,$(AUDIO_TTS_ENDPOINT))) $(if $(TTS_CONFIG),--tts-config $(call shell_quote,$(TTS_CONFIG)))
