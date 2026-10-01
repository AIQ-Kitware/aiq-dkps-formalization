# Build the Davis--Kahan slide decks and demos.  Run from visualizations/.
#
#   make                 # list targets
#   make all             # short + full decks, 1080p60, HTML + standalone HTML + PDF
#   make rebuild         # clean, then make all
#   make short           # one deck (also: full, deck-2d, 3d, prop44)
#   make full SCENES="S05Residual S08Why"   # re-render only those scenes, reconvert the deck
#   make short QUALITY=l # fast 480p draft
#   make clean-short     # remove one deck's outputs so the next build starts fresh
#   make standalone      # single-file HTML (videos embedded) of the built short + full decks
#
# Every deck writes renders/<deck>.html (+ .pdf, + <deck>_assets/) and keeps
# its rendered scenes in slides-<deck>/.  renders/<deck>.html needs the
# <deck>_assets/ folder beside it; renders/<deck>.standalone.html does not.

UV      ?= uv
RUN     := $(UV) run --extra vtk --extra slides --extra test
QUALITY ?= h
PDF     ?= 1
SCENES  ?=

BUILD_FLAGS := --quality $(QUALITY) $(if $(filter 1,$(PDF)),--pdf) $(if $(SCENES),--scenes $(SCENES))

# Short target name -> deck name in dkvis/build_slides.py.
DECK_short   := sine-theta-short
DECK_full    := sine-theta-full
DECK_deck-2d := sine-theta
DECK_3d      := sine-theta-3d
DECK_prop44  := prop44
DECKS        := short full deck-2d 3d prop44

.DEFAULT_GOAL := help
.PHONY: help setup all rebuild $(DECKS) $(addprefix clean-,$(DECKS)) $(addprefix present-,$(DECKS)) \
        $(addprefix standalone-,$(DECKS)) standalone draft assets app test clean distclean

help:
	@awk '/^#/ { sub(/^# ?/, ""); print; next } { exit }' $(firstword $(MAKEFILE_LIST))
	@echo; echo 'Targets:'
	@echo '  setup              uv sync with the vtk, slides and test extras'
	@echo '  all                build the short and full decks, then their standalone HTML'
	@echo '  rebuild            clean, then all (a from-scratch re-render)'
	@echo '  short | full       the 15-minute deck | the full deck'
	@echo '  deck-2d            the full deck without the VTK scenes'
	@echo '  3d | prop44        the 3D section | the Proposition 4.4 section alone'
	@echo '  clean-<deck>       remove one deck'"'"'s renders and scene folder'
	@echo '  present-<deck>     present a built deck live with manim-slides'
	@echo '  standalone-<deck>  write renders/<deck>.standalone.html with the videos embedded (no re-render)'
	@echo '  standalone         standalone-short + standalone-full'
	@echo '  draft              short + full at 480p, no PDF'
	@echo '  assets             re-render the VTK stills and movies the 3D slides use'
	@echo '  app                open the interactive 3D sin-theta demo'
	@echo '  test               run the model tests'
	@echo '  clean              remove all renders, scene folders and manim videos'
	@echo '  distclean          clean, plus the LaTeX and VTK asset caches'
	@echo 'Variables: QUALITY=l|m|h|p|k (default h)  PDF=0|1 (default 1)  SCENES="S05Residual ..."'

setup:
	$(UV) sync --extra vtk --extra slides --extra test

all: short full
	$(MAKE) standalone

rebuild:
	$(MAKE) clean
	$(MAKE) all

draft:
	$(MAKE) all QUALITY=l PDF=0

$(DECKS):
	$(RUN) python -m dkvis.build_slides $(DECK_$@) $(BUILD_FLAGS)

$(addprefix clean-,$(DECKS)):
	rm -rf slides-$(DECK_$(@:clean-%=%)) renders/$(DECK_$(@:clean-%=%)).* renders/$(DECK_$(@:clean-%=%))_assets

$(addprefix present-,$(DECKS)):
	$(RUN) manim-slides present --folder slides-$(DECK_$(@:present-%=%)) \
	    $$($(RUN) python -m dkvis.build_slides $(DECK_$(@:present-%=%)) --list)

standalone: standalone-short standalone-full

$(addprefix standalone-,$(DECKS)):
	$(RUN) python -m dkvis.build_slides $(DECK_$(@:standalone-%=%)) --no-render --one-file \
	    --html renders/$(DECK_$(@:standalone-%=%)).standalone.html

assets:
	$(RUN) python -m dkvis.vtk_sine_theta_3d --slide-assets media/vtk3d

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
