PYTHON ?= python3

.PHONY: all accounting bibliometrics paper literature clean

all: paper

# Refresh ignored working analyses plus the small tracked manuscript snapshots
# derived from them. This is explicit so an ordinary paper build never dirties
# tracked snapshot files.
accounting:
	$(PYTHON) scripts/build_all.py

# Networked, explicit refresh of the OpenAlex raw response and its tracked
# compact/TeX snapshots. The normal manuscript build never contacts OpenAlex.
bibliometrics:
	$(PYTHON) scripts/fetch_openalex_bibliometrics.py

# Manuscript builds consume the checked-in snapshots and are offline.
paper:
	latexmk -pdf paper.tex

literature:
	latexmk -pdf literature_review.tex

clean:
	latexmk -C paper.tex
	latexmk -C literature_review.tex
	rm -rf generated
