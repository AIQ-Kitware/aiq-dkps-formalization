SHELL := /bin/bash
.PHONY: all sources paper public clean check-prose check-publication-activity \
	survey-publication-activity check-publication-survey \
	self-test-publication-survey check-layout anonymize-repo

BUILD_DIR := build

LATEXMK_FLAGS := \
	-pdf \
	-interaction=nonstopmode \
	-halt-on-error \
	-outdir=$(BUILD_DIR)

PDFLATEX_FLAGS := \
	-interaction=nonstopmode \
	-halt-on-error \
	-output-directory=$(BUILD_DIR)

all: paper

sources:
	python3 scripts/build_practitioner_accounts.py
	python3 scripts/build_semantic_alignment_candidates.py
	python3 scripts/build_evidence.py

paper: sources
	@mkdir -p $(BUILD_DIR)
	@set -e; \
	if command -v bibtex >/dev/null 2>&1; then \
		latexmk $(LATEXMK_FLAGS) paper.tex; \
	elif command -v bibtex8 >/dev/null 2>&1; then \
		latexmk $(LATEXMK_FLAGS) -e '$${bibtex} = "bibtex8 %O %B";' paper.tex; \
	else \
		pdflatex $(PDFLATEX_FLAGS) paper.tex; \
		pdflatex $(PDFLATEX_FLAGS) paper.tex; \
	fi

public: sources
	@mkdir -p $(BUILD_DIR)
	@set -e; \
	if command -v bibtex >/dev/null 2>&1; then \
		latexmk $(LATEXMK_FLAGS) paper_public.tex; \
	elif command -v bibtex8 >/dev/null 2>&1; then \
		latexmk $(LATEXMK_FLAGS) -e '$${bibtex} = "bibtex8 %O %B";' paper_public.tex; \
	else \
		pdflatex $(PDFLATEX_FLAGS) paper_public.tex; \
		pdflatex $(PDFLATEX_FLAGS) paper_public.tex; \
	fi

clean:
	rm -rf $(BUILD_DIR)

check-layout: paper public
	python3 scripts/check_layout.py

check-prose:
	python3 scripts/check_prose.py

check-publication-activity:
	python3 scripts/check_lean_publication_activity.py

survey-publication-activity:
	python3 scripts/refresh_lean_publication_activity.py survey

check-publication-survey:
	python3 scripts/refresh_lean_publication_activity.py survey --require-alignment

self-test-publication-survey:
	python3 scripts/refresh_lean_publication_activity.py self-test

anonymize-repo:
	python3 scripts/anonymize_repo.py

clean:
	latexmk -C paper.tex || true
	latexmk -C paper_public.tex || true
	rm -f paper.bbl paper.blg paper_public.bbl paper_public.blg
