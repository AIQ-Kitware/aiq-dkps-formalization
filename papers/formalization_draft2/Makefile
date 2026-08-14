PYTHON ?= python3

.PHONY: all accounting paper clean

all: paper

accounting:
	$(PYTHON) scripts/build_all.py

# Generated analysis artifacts are intentionally gitignored, so a paper build
# always reconstructs them from the repository evidence first.
paper: accounting
	latexmk -pdf paper.tex

clean:
	latexmk -C paper.tex
	rm -rf generated
