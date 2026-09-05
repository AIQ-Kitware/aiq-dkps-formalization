SHELL := /bin/bash
.PHONY: all sources paper public clean check-prose

all: paper

sources:
	python3 scripts/build_practitioner_accounts.py
	python3 scripts/build_evidence.py

paper: sources
	@set -e; \
	if command -v bibtex >/dev/null 2>&1; then \
		latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex; \
	elif command -v bibtex8 >/dev/null 2>&1; then \
		latexmk -pdf -interaction=nonstopmode -halt-on-error -e '$${bibtex} = "bibtex8 %O %B";' paper.tex; \
	else \
		pdflatex -interaction=nonstopmode -halt-on-error paper.tex; \
		pdflatex -interaction=nonstopmode -halt-on-error paper.tex; \
	fi

public: sources
	@set -e; \
	if command -v bibtex >/dev/null 2>&1; then \
		latexmk -pdf -interaction=nonstopmode -halt-on-error paper_public.tex; \
	elif command -v bibtex8 >/dev/null 2>&1; then \
		latexmk -pdf -interaction=nonstopmode -halt-on-error -e '$${bibtex} = "bibtex8 %O %B";' paper_public.tex; \
	else \
		pdflatex -interaction=nonstopmode -halt-on-error paper_public.tex; \
		pdflatex -interaction=nonstopmode -halt-on-error paper_public.tex; \
	fi

check-prose:
	python3 scripts/check_prose.py

clean:
	latexmk -C paper.tex || true
	latexmk -C paper_public.tex || true
	rm -f paper.bbl paper.blg paper_public.bbl paper_public.blg
