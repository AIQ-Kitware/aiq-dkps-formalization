PYTHON ?= python3

.PHONY: all accounting paper clean test

all: accounting paper

accounting:
	$(PYTHON) scripts/build_all.py

paper:
	latexmk -pdf paper.tex

test:
	$(PYTHON) -m unittest discover -s scripts -p 'test_*.py'

clean:
	latexmk -C paper.tex
