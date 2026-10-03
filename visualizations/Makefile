# Build the Davis--Kahan slide decks and demos.  Run from visualizations/.
#
#   make                 # list targets
#   make all             # short deck + every part + the full deck, 1080p30, HTML + standalone HTML + PDF
#   make final           # the same at the full 1080p60
#   make rebuild         # clean, then make all
#   make short           # the 15-minute deck
#   make part3           # one part of the full talk, with its own HTML (part1 ... part7)
#   make full            # every part, then the full deck assembled from them
#   make full SCENES="S05Residual S08Why"   # re-render only those scenes, reconvert
#   make short QUALITY=l # fast 480p draft
#   make clean-short     # remove one deck's outputs so the next build starts fresh
#   make full THEME=light  # light background; outputs get a -light suffix beside the dark ones
#   make standalone      # single-file HTML (videos embedded) of every built deck and part
#   make handout         # one-page-per-scene PDFs of every built deck and part
#
# Every deck writes renders/<deck>.html (+ .pdf, .handout.pdf, <deck>_assets/) and keeps
# its rendered scenes in slides-<deck>/ (with THEME=light: <deck>-light).  renders/<deck>.html needs the
# <deck>_assets/ folder beside it; renders/<deck>.standalone.html does not.

UV      ?= uv
RUN     := $(UV) run --extra vtk --extra slides --extra test
QUALITY ?= h
# 1080p renders at 30 fps unless asked for more (FPS=60, or `make final`); drafts keep the quality's own rate.
FPS     ?= $(if $(filter l m,$(QUALITY)),,30)
JOBS    ?=
PDF     ?= 1
SCENES  ?=
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
PARTS      := part1 part2 part3 part4 part5 part6 part7
DECKS      := short full $(PARTS)

.DEFAULT_GOAL := help
.PHONY: help setup all rebuild $(DECKS) $(addprefix clean-,$(DECKS)) $(addprefix present-,$(DECKS)) \
        $(addprefix standalone-,$(DECKS)) standalone $(addprefix handout-,$(DECKS)) handout parts final draft assets app test clean distclean

help:
	@awk '/^#/ { sub(/^# ?/, ""); print; next } { exit }' $(firstword $(MAKEFILE_LIST))
	@echo; echo 'Targets:'
	@echo '  setup              uv sync with the vtk, slides and test extras'
	@echo '  all                short, every part and full, then standalone HTML for each'
	@echo '  final              all at the full 1080p60 (all renders 1080p30)'
	@echo '  rebuild            clean, then all (a from-scratch re-render)'
	@echo '  short              the 15-minute deck'
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
	@echo 'Variables: QUALITY=l|m|h|p|k (default h)  FPS=30|60 (default 30 at h)  JOBS=n (default: one per CPU)'
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

short $(PARTS):
	$(RUN) python -m dkvis.build_slides $(DECK_$@) $(BUILD_FLAGS)

parts: $(PARTS)

# Render every part's scenes in one parallel pool, assemble the full deck from them,
# then convert each part to its own HTML (and PDF/handout) without rendering again.
full:
	$(RUN) python -m dkvis.build_slides $(DECK_full) $(BUILD_FLAGS)
	for part in $(foreach p,$(PARTS),$(DECK_$(p))); do \
	    $(RUN) python -m dkvis.build_slides $$part --no-render $(if $(filter 1,$(PDF)),--pdf --handout) || exit 1; \
	done

$(addprefix clean-,$(DECKS)):
	rm -rf slides-$(DECK_$(@:clean-%=%))$(SUFFIX) renders/$(DECK_$(@:clean-%=%))$(SUFFIX).* \
	    renders/$(DECK_$(@:clean-%=%))$(SUFFIX)_assets

$(addprefix present-,$(DECKS)):
	$(RUN) manim-slides present --folder slides-$(DECK_$(@:present-%=%))$(SUFFIX) \
	    $$($(RUN) python -m dkvis.build_slides $(DECK_$(@:present-%=%)) --list)

standalone: standalone-short standalone-full $(addprefix standalone-,$(PARTS))

$(addprefix standalone-,$(DECKS)):
	$(RUN) python -m dkvis.build_slides $(DECK_$(@:standalone-%=%)) --no-render --one-file \
	    --html renders/$(DECK_$(@:standalone-%=%))$(SUFFIX).standalone.html

handout: handout-short handout-full $(addprefix handout-,$(PARTS))

$(addprefix handout-,$(DECKS)):
	$(RUN) python -m dkvis.build_slides $(DECK_$(@:handout-%=%)) --no-render --handout

assets:
	$(RUN) python -m dkvis.vtk_sine_theta_3d --slide-assets media/vtk3d$(SUFFIX)

app:
	$(RUN) python -m dkvis.vtk_sine_theta_3d

test:
	$(RUN) pytest -q tests

# manim's partial-movie cache lives in media/videos; removing it forces every
# animation to re-render.  The LaTeX cache (media/Tex) and the VTK assets
# (media/vtk3d) are content-addressed or regenerated on demand, so plain
# `clean` keeps them; `distclean` removes them too.
clean:
	rm -rf renders slides slides-* media/videos media/images media/texts

distclean: clean
	rm -rf media .pytest_cache .ruff_cache
