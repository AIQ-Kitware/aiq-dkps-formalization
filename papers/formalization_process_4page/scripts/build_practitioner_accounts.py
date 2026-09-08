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
SCREENING_CSV = ROOT / 'data' / 'practitioner_account_screening.csv'
ACTIVITY_CSV = ROOT / 'data' / 'lean_publication_activity.csv'
SCHEMA_PATH = ROOT / 'data' / 'practitioner_accounts.schema.json'
SCREENING_SCHEMA_PATH = ROOT / 'data' / 'practitioner_account_screening.schema.json'
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



def validate_screening(rows, account_rows, bib_keys):
    schema = json.loads(SCREENING_SCHEMA_PATH.read_text(encoding='utf8'))
    expected = list(schema['columns'])
    actual = list(rows[0]) if rows else []
    if actual != expected:
        raise SystemExit(
            'practitioner_account_screening.csv columns differ from schema:\n'
            f'expected={expected}\nactual={actual}'
        )

    ids = [r['candidate_id'] for r in rows]
    if len(ids) != len(set(ids)):
        dup = sorted({x for x in ids if ids.count(x) > 1})
        raise SystemExit('Duplicate screening candidate ids: ' + ', '.join(dup))

    categorical = schema['categorical_values']
    required_text = [
        'candidate_id', 'screened_on', 'date', 'author', 'title', 'source_type',
        'source_url', 'discovery_route', 'decision', 'decision_reason',
    ]
    errors = []
    by_id = {r['candidate_id']: r for r in rows}
    account_by_id = {r['id']: r for r in account_rows}

    for i, r in enumerate(rows, 2):
        for key in required_text:
            if not r[key].strip():
                errors.append(f'screening row {i}: blank {key}')
        if r['source_type'] not in categorical['source_type']:
            errors.append(f'screening row {i}: bad source_type={r["source_type"]!r}')
        if r['decision'] not in categorical['decision']:
            errors.append(f'screening row {i}: bad decision={r["decision"]!r}')
        parsed = urlparse(r['source_url'])
        if parsed.scheme != 'https' or not parsed.netloc:
            errors.append(
                f'screening row {i}: source_url must be https: {r["source_url"]!r}'
            )
        if r['citation_key'] and r['citation_key'] not in bib_keys:
            errors.append(
                f'screening row {i}: missing bibliography key={r["citation_key"]!r}'
            )
        if r['decision'] in {'include_account', 'structured_study', 'related_work'}:
            if not r['citation_key'].strip():
                errors.append(
                    f'screening row {i}: {r["decision"]} requires citation_key'
                )
        if r['decision'] == 'duplicate':
            target = r['duplicate_of'].strip()
            if not target:
                errors.append(f'screening row {i}: duplicate requires duplicate_of')
            elif target == r['candidate_id']:
                errors.append(f'screening row {i}: duplicate_of points to itself')
            elif target not in by_id:
                errors.append(
                    f'screening row {i}: duplicate_of={target!r} is not a candidate_id'
                )
        elif r['duplicate_of'].strip():
            errors.append(
                f'screening row {i}: duplicate_of is only valid for duplicate decisions'
            )

    for account_id, account in account_by_id.items():
        screened = by_id.get(account_id)
        if screened is None:
            errors.append(f'account {account_id!r} is absent from screening log')
            continue
        expected_decision = (
            'structured_study'
            if account['source_type'] == 'human_study'
            else 'include_account'
        )
        if screened['decision'] != expected_decision:
            errors.append(
                f'account {account_id!r}: expected screening decision '
                f'{expected_decision!r}, got {screened["decision"]!r}'
            )
        if screened['source_url'] != account['source_url']:
            errors.append(f'account {account_id!r}: screening source_url differs')
        if screened['citation_key'] != account['citation_key']:
            errors.append(f'account {account_id!r}: screening citation_key differs')

    for r in rows:
        if r['decision'] == 'include_account':
            account = account_by_id.get(r['candidate_id'])
            if account is None:
                errors.append(
                    f'screened include_account {r["candidate_id"]!r} has no account row'
                )
            elif account['source_type'] == 'human_study':
                errors.append(
                    f'screened include_account {r["candidate_id"]!r} is a human_study row'
                )

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

    screening = load_csv(SCREENING_CSV)
    if not screening:
        raise SystemExit('No practitioner-account screening entries found')
    validate_screening(screening, rows, bib_keys)

    activity = load_csv(ACTIVITY_CSV)
    by_month = {r['month']: int(r['papers_indexed']) for r in activity}
    expected_months = (
        [f'2024-{m:02d}' for m in range(1, 13)]
        + [f'2025-{m:02d}' for m in range(1, 13)]
        + [f'2026-{m:02d}' for m in range(1, 10)]
    )
    if list(by_month) != expected_months:
        raise SystemExit(
            'lean_publication_activity.csv must contain Jan 2024--Sep 2026 months in order'
        )
    total_2024 = sum(v for k, v in by_month.items() if k.startswith('2024-'))
    total_2025 = sum(v for k, v in by_month.items() if k.startswith('2025-'))
    jan_jul_2026 = sum(v for k, v in by_month.items() if '2026-01' <= k <= '2026-07')
    jan_aug_2026 = sum(v for k, v in by_month.items() if '2026-01' <= k <= '2026-08')
    mean_2025 = total_2025 / 12
    mean_jan_aug_2026 = jan_aug_2026 / 8
    rate_ratio = mean_jan_aug_2026 / mean_2025

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
        'PractitionerScreenedCandidateCount': len(screening),
        'PractitionerScreenedIncludeCount': sum(r['decision'] == 'include_account' for r in screening),
        'PractitionerStructuredStudyCount': sum(r['decision'] == 'structured_study' for r in screening),
        'PractitionerRelatedWorkCount': sum(r['decision'] == 'related_work' for r in screening),
        'PractitionerDuplicateCount': sum(r['decision'] == 'duplicate' for r in screening),
        'PractitionerExcludeCount': sum(r['decision'] == 'exclude' for r in screening),
        'LeanPapersTwentyFour': total_2024,
        'LeanPapersTwentyFive': total_2025,
        'LeanPapersJanJulTwentySix': jan_jul_2026,
        'LeanPapersJulyTwentySix': by_month['2026-07'],
        'LeanPapersJanAugTwentySix': jan_aug_2026,
        'LeanPapersAugustTwentySix': by_month['2026-08'],
        'LeanPapersSeptemberPartialTwentySix': by_month['2026-09'],
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
        f.write('This document is generated from `data/practitioner_accounts.csv` and `data/practitioner_account_screening.csv`.  It keeps the public sources behind the workshop paper easy to inspect and corroborate.  The categorical fields are documented in the corresponding schema files.\n\n')
        f.write('The accounts were found through LLM-assisted web search.  Representativeness is unknown, so the rows should not be used to estimate prevalence.  `yes` records an event or practice explicitly described by the source; `qualified`, `unclear`, and `not_reported` preserve uncertainty instead of filling it in.\n\n')
        f.write('The screening log was introduced on 2026-09-08.  It records the preexisting included snapshot and the candidates reviewed during the current expansion; it does not reconstruct every source encountered in earlier searches and should not be read as an exhaustive search record.\n\n')

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

        f.write('## Screening log\n\n')
        f.write(f'- Candidates recorded: **{macros["PractitionerScreenedCandidateCount"]}**\n')
        f.write(f'- Included first-person accounts: **{macros["PractitionerScreenedIncludeCount"]}**\n')
        f.write(f'- Structured studies: **{macros["PractitionerStructuredStudyCount"]}**\n')
        f.write(f'- Related-work-only sources: **{macros["PractitionerRelatedWorkCount"]}**\n')
        f.write(f'- Duplicates: **{macros["PractitionerDuplicateCount"]}**\n')
        f.write(f'- Excluded: **{macros["PractitionerExcludeCount"]}**\n\n')
        f.write('| Candidate | Decision | Discovery route | Reason |\n')
        f.write('|---|---|---|---|\n')
        for r in screening:
            reason = r['decision_reason'].replace('|', '/')
            f.write(f'| `{r["candidate_id"]}` | `{r["decision"]}` | `{r["discovery_route"]}` | {reason} |\n')
        f.write('\n')

        f.write('## Lean publication activity used for context\n\n')
        f.write('`data/lean_publication_activity.csv` records the audited Papers With Lean series through the paper cutoff of 2026-09-06. The January 2024 extension groups the captured `site_papers.json` corpus by its `published` month after that definition reproduced the frozen January 2025--July 2026 statistics-chart overlap. September 2026 is partial.\n\n')
        f.write(f'- 2024: **{total_2024}** papers by `published` month\n')
        f.write(f'- 2025: **{total_2025}** papers by `published` month\n')
        f.write(f'- January--August 2026: **{jan_aug_2026}** papers by `published` month\n')
        f.write(f'- Mean monthly rate ratio, Jan--Aug 2026 versus 2025: **{rate_ratio:.1f}x**\n')
        f.write(f'- August 2026: **{by_month["2026-08"]}** papers\n')
        f.write(f'- September 2026 through the cutoff: **{by_month["2026-09"]}** papers (partial)\n\n')

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
    print(f'validated {len(screening)} screening entries')
    print(f'wrote {OUT_TEX}')
    print(f'wrote {OUT_MD}')


if __name__ == '__main__':
    main()
