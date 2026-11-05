PYTHON ?= python3
CUTOFF ?=
ACCOUNTING_CUTOFF_ARG := $(if $(strip $(CUTOFF)),--cutoff $(CUTOFF),)

.PHONY: all accounting bibliometrics counterexample-figure teaching-figures figures paper-figures paper author-paper overleaf submission matching-study literature dependency-snapshots clean

TEACHING_PGF = figures/Fig1.pgf figures/Fig3.pgf
FIGURE_STYLE = scripts/figure_style.py math_symbol_colors.tex
FIGURE_MODELS = ../../visualizations/dkvis

all: paper

# Refresh ignored working analyses and derived tables explicitly.
accounting:
	$(PYTHON) scripts/build_all.py $(ACCOUNTING_CUTOFF_ARG)

# Networked, explicit refresh of the dated OpenAlex observations and their
# ignored TeX/CSV views. The normal manuscript build never contacts OpenAlex.
bibliometrics:
	$(PYTHON) scripts/fetch_openalex_bibliometrics.py

# The manuscript and editor builds regenerate missing/stale figures offline.
paper: paper-figures
	latexmk -pdf paper.tex

author-paper: paper-figures
	latexmk -pdf -jobname=paper-author -pretex='\def\DKUseAuthorStyle{1}' paper.tex

overleaf: paper
	$(PYTHON) scripts/package_manuscript.py overleaf

submission: paper-figures
	$(PYTHON) scripts/package_manuscript.py submission

# Expanded offline derivations, built separately from the article.
matching-study:
	latexmk -pdf matching_proof_study.tex

paper-figures: $(TEACHING_PGF) figures/Fig2.pgf

$(TEACHING_PGF): scripts/build_teaching_figures.py $(FIGURE_STYLE) $(FIGURE_MODELS)/palette.py $(FIGURE_MODELS)/novelty_math.py $(FIGURE_MODELS)/sine_theta_story.py $(FIGURE_MODELS)/sine_theta.py

figures/Fig1.pgf:
	$(PYTHON) scripts/build_teaching_figures.py --figure sine-theta

figures/Fig3.pgf:
	$(PYTHON) scripts/build_teaching_figures.py --figure matching

figures/Fig2.pgf: scripts/build_counterexample_figure.py $(FIGURE_STYLE) $(FIGURE_MODELS)/prop44.py
	$(PYTHON) scripts/build_counterexample_figure.py

# Explicit refresh also recreates optional standalone PDF/SVG exports.
counterexample-figure:
	$(PYTHON) scripts/build_counterexample_figure.py

teaching-figures:
	$(PYTHON) scripts/build_teaching_figures.py

figures: counterexample-figure teaching-figures

dependency-snapshots:
	$(PYTHON) scripts/build_dependency_analysis.py

literature: dependency-snapshots
	latexmk -pdf literature_review.tex

clean:
	latexmk -C paper.tex
	latexmk -C matching_proof_study.tex
	latexmk -C literature_review.tex
	rm -rf generated
