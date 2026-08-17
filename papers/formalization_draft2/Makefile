PYTHON ?= python3

.PHONY: all accounting bibliometrics paper literature clean

all: paper

accounting:
	$(PYTHON) scripts/build_all.py

bibliometrics:
	$(PYTHON) scripts/fetch_openalex_bibliometrics.py

# Generated analysis artifacts are intentionally gitignored, so a paper build
# always reconstructs them from the repository evidence first.
paper: accounting
	latexmk -pdf paper.tex

literature: accounting
	latexmk -pdf literature_review.tex

clean:
	latexmk -C paper.tex
	latexmk -C literature_review.tex
	rm -rf generated
