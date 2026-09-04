SHELL := /bin/bash

.PHONY: all paper related-work evidence clean check-prose
all: paper related-work

paper: generated/semantic_reversal_macros.tex
	@set -e; \
	if command -v bibtex >/dev/null 2>&1; then \
		latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex; \
	elif command -v bibtex8 >/dev/null 2>&1; then \
		latexmk -pdf -interaction=nonstopmode -halt-on-error \
			-e '$$bibtex = "bibtex8 %O %B";' paper.tex; \
	else \
		echo "warning: bibtex/bibtex8 unavailable; building draft with unresolved bibliography" >&2; \
		pdflatex -interaction=nonstopmode -halt-on-error paper.tex; \
		pdflatex -interaction=nonstopmode -halt-on-error paper.tex; \
	fi

related-work:
	@set -e; \
	if command -v bibtex >/dev/null 2>&1; then \
		latexmk -pdf -interaction=nonstopmode -halt-on-error related_work_semantic_alignment.tex; \
	elif command -v bibtex8 >/dev/null 2>&1; then \
		latexmk -pdf -interaction=nonstopmode -halt-on-error \
			-e '$$bibtex = "bibtex8 %O %B";' related_work_semantic_alignment.tex; \
	else \
		echo "warning: bibtex/bibtex8 unavailable; building related-work memo with unresolved bibliography" >&2; \
		pdflatex -interaction=nonstopmode -halt-on-error related_work_semantic_alignment.tex; \
		pdflatex -interaction=nonstopmode -halt-on-error related_work_semantic_alignment.tex; \
	fi

evidence:
	python3 scripts/reconstruct_semantic_reversals.py

generated/semantic_reversal_macros.tex:
	@mkdir -p generated
	python3 scripts/reconstruct_semantic_reversals.py

check-prose:
	python3 scripts/check_prose.py

clean:
	latexmk -C paper.tex || true
	latexmk -C related_work_semantic_alignment.tex || true
	rm -f paper.bbl paper.blg related_work_semantic_alignment.bbl related_work_semantic_alignment.blg
