# Derived manuscript tables and observation data

Generated TeX tables/macros and CSV views in this directory are gitignored.
The Python generators and their input evidence remain tracked. The main paper
does not consume these optional analysis tables. `make literature` regenerates
the dependency tables used by the literature review.

Detailed working CSV/JSON inventories, diagnostic reports, and raw API responses
belong under `../generated/` and are also gitignored. The dated
`openalex_bibliometrics.json` remains tracked as external observation data:
querying the service again cannot reproduce a past observation.

- `make accounting` refreshes ignored repository-derived TeX macros and tables.
- `make literature` prepares the ignored dependency macros and table.
- `make bibliometrics` explicitly refreshes the tracked observation JSON and
  the ignored citation-trend CSV/TeX views and bibliometric macros, while
  leaving the raw response under `../generated/`. Review changes to the
  observation data before committing them.
