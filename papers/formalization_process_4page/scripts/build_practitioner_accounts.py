#!/usr/bin/env python3
"""Validate and regenerate the public-account snapshot used by the paper."""
from __future__ import annotations

import csv
import json
import re
from pathlib import Path
from urllib.parse import urlparse

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ACCOUNTS_CSV = ROOT / 'data' / 'practitioner_accounts.csv'
ACTIVITY_CSV = ROOT / 'data' / 'lean_publication_activity.csv'
SCHEMA_PATH = ROOT / 'data' / 'practitioner_accounts.schema.json'
BIB_PATH = ROOT / 'references.bib'
OUT_MD = ROOT / 'notes' / 'practitioner_accounts.md'
OUT_TEX = ROOT / 'generated' / 'practitioner_account_macros.tex'


def load_csv(path: Path):
    with path.open(newline='', encoding='utf8') as f:
        return list(csv.DictReader(f))


def yes_count(rows, key):
    return sum(r[key] == 'yes' for r in rows)


def qualified_count(rows, key):
    return sum(r[key] == 'qualified' for r in rows)


def validate(rows):
    schema = json.loads(SCHEMA_PATH.read_text(encoding='utf8'))
    expected = list(schema['columns'])
    actual = list(rows[0]) if rows else []
    if actual != expected:
        raise SystemExit(
            'practitioner_accounts.csv columns differ from schema:\n'
            f'expected={expected}\nactual={actual}'
        )

    ids = [r['id'] for r in rows]
    if len(ids) != len(set(ids)):
        dup = sorted({x for x in ids if ids.count(x) > 1})
        raise SystemExit('Duplicate account ids: ' + ', '.join(dup))

    categorical = schema['categorical_values']
    boolean_fields = [
        'multiple_ai_tools', 'separate_ai_review', 'source_defect_found',
        'counterexample_used', 'persistent_project_state', 'posthoc_understanding',
    ]
    required_text = [
        'id', 'date', 'author', 'title', 'source_type', 'target', 'human_role',
        'observation', 'source_note', 'source_url', 'citation_key',
    ]
    errors = []
    for i, r in enumerate(rows, 2):
        for key in required_text:
            if not r[key].strip():
                errors.append(f'row {i}: blank {key}')
        if r['source_type'] not in categorical['source_type']:
            errors.append(f'row {i}: bad source_type={r["source_type"]!r}')
        if r['reported_lean_experience'] not in categorical['reported_lean_experience']:
            errors.append(f'row {i}: bad reported_lean_experience={r["reported_lean_experience"]!r}')
        if r['reads_generated_lean'] not in categorical['reads_generated_lean']:
            errors.append(f'row {i}: bad reads_generated_lean={r["reads_generated_lean"]!r}')
        for key in boolean_fields:
            if r[key] not in categorical['boolean_like']:
                errors.append(f'row {i}: bad {key}={r[key]!r}')
        if r['semantic_mismatch'] not in categorical['semantic_mismatch']:
            errors.append(f'row {i}: bad semantic_mismatch={r["semantic_mismatch"]!r}')
        parsed = urlparse(r['source_url'])
        if parsed.scheme != 'https' or not parsed.netloc:
            errors.append(f'row {i}: source_url must be https: {r["source_url"]!r}')
    if errors:
        raise SystemExit('\n'.join(errors))


def main():
    rows = load_csv(ACCOUNTS_CSV)
    if not rows:
        raise SystemExit('No practitioner accounts found')
    validate(rows)
    accounts = [r for r in rows if r['source_type'] != 'human_study']
    studies = [r for r in rows if r['source_type'] == 'human_study']

    bib = BIB_PATH.read_text(encoding='utf8')
    bib_keys = set(re.findall(r'@[A-Za-z]+\s*\{\s*([^,]+),', bib))
    missing = sorted({r['citation_key'] for r in rows} - bib_keys)
    if missing:
        raise SystemExit('Missing bibliography keys: ' + ', '.join(missing))

    activity = load_csv(ACTIVITY_CSV)
    by_month = {r['month']: int(r['papers_indexed']) for r in activity}
    expected_months = [f'2025-{m:02d}' for m in range(1, 13)] + [f'2026-{m:02d}' for m in range(1, 8)]
    if list(by_month) != expected_months:
        raise SystemExit('lean_publication_activity.csv must contain complete Jan 2025--Jul 2026 months in order')
    total_2025 = sum(v for k, v in by_month.items() if k.startswith('2025-'))
    jan_jul_2026 = sum(v for k, v in by_month.items() if '2026-01' <= k <= '2026-07')
    mean_2025 = total_2025 / 12
    mean_jan_jul_2026 = jan_jul_2026 / 7
    rate_ratio = mean_jan_jul_2026 / mean_2025

    macros = {
        'PractitionerAccountCount': len(accounts),
        'AccountStudyCount': len(studies),
        'AccountSemanticMismatchCount': yes_count(accounts, 'semantic_mismatch'),
        'AccountSemanticMismatchQualifiedCount': qualified_count(accounts, 'semantic_mismatch'),
        'AccountSourceDefectCount': yes_count(accounts, 'source_defect_found'),
        'AccountCounterexampleCount': yes_count(accounts, 'counterexample_used'),
        'AccountSeparateAIReviewCount': yes_count(accounts, 'separate_ai_review'),
        'AccountPersistentStateCount': yes_count(accounts, 'persistent_project_state'),
        'AccountPosthocUnderstandingCount': yes_count(accounts, 'posthoc_understanding'),
        'AccountNoLeanReadCount': sum(r['reads_generated_lean'] == 'none' for r in accounts),
        'LeanPapersTwentyFive': total_2025,
        'LeanPapersJanJulTwentySix': jan_jul_2026,
        'LeanPapersJulyTwentySix': by_month['2026-07'],
        'LeanPublicationRateRatio': f'{rate_ratio:.1f}',
    }

    OUT_TEX.parent.mkdir(parents=True, exist_ok=True)
    with OUT_TEX.open('w', encoding='utf8') as f:
        f.write('% Generated by scripts/build_practitioner_accounts.py\n')
        for key, value in macros.items():
            f.write(f'\\newcommand{{\\{key}}}{{{value}}}\n')

    OUT_MD.parent.mkdir(parents=True, exist_ok=True)
    with OUT_MD.open('w', encoding='utf8') as f:
        f.write('# Public first-person accounts of AI-assisted Lean work\n\n')
        f.write('This document is generated from `data/practitioner_accounts.csv`.  It keeps the public sources behind the workshop paper easy to inspect and corroborate.  The categorical fields are documented in `data/practitioner_accounts.schema.json`.\n\n')
        f.write('The accounts were found through web search and citation chasing.  Representativeness is unknown, so the rows should not be used to estimate prevalence.  `yes` records an event or practice explicitly described by the source; `qualified`, `unclear`, and `not_reported` preserve uncertainty instead of filling it in.\n\n')

        f.write('## Descriptive counts\n\n')
        f.write(f'- Public first-person accounts: **{len(accounts)}**\n')
        f.write(f'- Human--AI workflow studies kept alongside them: **{len(studies)}**\n')
        f.write(f'- Explicit formal statement/definition/correspondence mismatch: **{macros["AccountSemanticMismatchCount"]}** (+ **{macros["AccountSemanticMismatchQualifiedCount"]}** qualified)\n')
        f.write(f'- Source defect exposed during formalization: **{macros["AccountSourceDefectCount"]}**\n')
        f.write(f'- Counterexample explicitly used: **{macros["AccountCounterexampleCount"]}**\n')
        f.write(f'- Separate AI review role: **{macros["AccountSeparateAIReviewCount"]}**\n')
        f.write(f'- Persistent project state outside chat: **{macros["AccountPersistentStateCount"]}**\n')
        f.write(f'- Later human understanding of an already checked result: **{macros["AccountPosthocUnderstandingCount"]}**\n')
        f.write(f'- Generated Lean explicitly not read in the described workflow: **{macros["AccountNoLeanReadCount"]}**\n\n')

        f.write('## Lean publication activity used for context\n\n')
        f.write('`data/lean_publication_activity.csv` transcribes the complete-month counts shown by Papers With Lean on the statistics snapshot updated 2026-08-24.\n\n')
        f.write(f'- 2025: **{total_2025}** indexed papers\n')
        f.write(f'- January--July 2026: **{jan_jul_2026}** indexed papers\n')
        f.write(f'- Mean monthly rate ratio: **{rate_ratio:.1f}x**\n')
        f.write(f'- July 2026: **{by_month["2026-07"]}** indexed papers\n\n')

        f.write('## Account matrix\n\n')
        f.write('| ID | Author | Lean experience | Reads generated Lean | Separate AI review | Semantic mismatch | Source defect | Persistent state |\n')
        f.write('|---|---|---|---|---|---|---|---|\n')
        for r in accounts:
            f.write('| `{}` | {} | `{}` | `{}` | `{}` | `{}` | `{}` | `{}` |\n'.format(
                r['id'], r['author'].replace('|', '/'), r['reported_lean_experience'],
                r['reads_generated_lean'], r['separate_ai_review'], r['semantic_mismatch'],
                r['source_defect_found'], r['persistent_project_state']))
        f.write('\n')

        f.write('## Source records\n\n')
        for i, r in enumerate(rows, 1):
            f.write(f'### {i}. {r["author"]} - {r["title"]}\n\n')
            f.write(f'- **ID:** `{r["id"]}`\n')
            f.write(f'- **Date:** {r["date"]}\n')
            f.write(f'- **Source type:** `{r["source_type"]}`\n')
            f.write(f'- **Target:** {r["target"]}\n')
            f.write(f'- **Reported Lean experience:** `{r["reported_lean_experience"]}`\n')
            f.write(f'- **Reads generated Lean:** `{r["reads_generated_lean"]}`\n')
            f.write(f'- **Multiple AI tools:** `{r["multiple_ai_tools"]}`; **separate AI review:** `{r["separate_ai_review"]}`\n')
            f.write(f'- **Semantic mismatch:** `{r["semantic_mismatch"]}`; **source defect found:** `{r["source_defect_found"]}`; **counterexample used:** `{r["counterexample_used"]}`\n')
            f.write(f'- **Persistent project state:** `{r["persistent_project_state"]}`; **post-hoc understanding:** `{r["posthoc_understanding"]}`\n')
            f.write(f'- **Human role described:** {r["human_role"]}\n')
            f.write(f'- **Observation used by the paper:** {r["observation"]}\n')
            f.write(f'- **Source note:** {r["source_note"]}\n')
            f.write(f'- **Citation key:** `{r["citation_key"]}`\n')
            f.write(f'- **Source:** {r["source_url"]}\n\n')

    print(f'validated {len(rows)} source records')
    print(f'wrote {OUT_TEX}')
    print(f'wrote {OUT_MD}')


if __name__ == '__main__':
    main()
