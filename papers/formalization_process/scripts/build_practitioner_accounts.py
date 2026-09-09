#!/usr/bin/env python3
"""Validate and regenerate the public-account snapshot used by the paper."""
from __future__ import annotations

import csv
import json
import re
from collections import Counter
from pathlib import Path
from urllib.parse import urlparse

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ACCOUNTS_CSV = ROOT / 'data' / 'practitioner_accounts.csv'
SOURCES_CSV = ROOT / 'data' / 'practitioner_account_sources.csv'
SCREENING_CSV = ROOT / 'data' / 'practitioner_account_screening.csv'
ACTIVITY_CSV = ROOT / 'data' / 'lean_publication_activity.csv'
SCHEMA_PATH = ROOT / 'data' / 'practitioner_accounts.schema.json'
SOURCE_SCHEMA_PATH = ROOT / 'data' / 'practitioner_account_sources.schema.json'
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


def check_columns(rows, schema, filename):
    expected = list(schema['columns'])
    actual = list(rows[0]) if rows else []
    if actual != expected:
        raise SystemExit(
            f'{filename} columns differ from schema:\n'
            f'expected={expected}\nactual={actual}'
        )


def check_https(value, label, errors):
    parsed = urlparse(value)
    if parsed.scheme != 'https' or not parsed.netloc:
        errors.append(f'{label} must be https: {value!r}')


def validate_accounts(rows):
    schema = json.loads(SCHEMA_PATH.read_text(encoding='utf8'))
    check_columns(rows, schema, 'practitioner_accounts.csv')
    ids = [r['account_id'] for r in rows]
    if len(ids) != len(set(ids)):
        dup = sorted({x for x in ids if ids.count(x) > 1})
        raise SystemExit('Duplicate account ids: ' + ', '.join(dup))

    categorical = schema['categorical_values']
    boolean_fields = [
        'multiple_ai_tools', 'separate_ai_review', 'source_defect_found',
        'counterexample_used', 'persistent_project_state', 'posthoc_understanding',
    ]
    required_text = [
        'account_id', 'account_kind', 'practitioner_cluster', 'project_cluster',
        'date', 'author', 'title', 'target', 'human_role', 'observation',
        'account_note', 'primary_source_id',
    ]
    errors = []
    for i, r in enumerate(rows, 2):
        for key in required_text:
            if not r[key].strip():
                errors.append(f'account row {i}: blank {key}')
        if r['account_kind'] not in categorical['account_kind']:
            errors.append(f'account row {i}: bad account_kind={r["account_kind"]!r}')
        if r['reported_lean_experience'] not in categorical['reported_lean_experience']:
            errors.append(
                f'account row {i}: bad reported_lean_experience='
                f'{r["reported_lean_experience"]!r}'
            )
        if r['reads_generated_lean'] not in categorical['reads_generated_lean']:
            errors.append(
                f'account row {i}: bad reads_generated_lean={r["reads_generated_lean"]!r}'
            )
        for key in boolean_fields:
            if r[key] not in categorical['boolean_like']:
                errors.append(f'account row {i}: bad {key}={r[key]!r}')
        if r['semantic_mismatch'] not in categorical['semantic_mismatch']:
            errors.append(
                f'account row {i}: bad semantic_mismatch={r["semantic_mismatch"]!r}'
            )
    if errors:
        raise SystemExit('\n'.join(errors))


def validate_sources(rows, account_rows, bib_keys):
    schema = json.loads(SOURCE_SCHEMA_PATH.read_text(encoding='utf8'))
    check_columns(rows, schema, 'practitioner_account_sources.csv')
    ids = [r['source_id'] for r in rows]
    if len(ids) != len(set(ids)):
        dup = sorted({x for x in ids if ids.count(x) > 1})
        raise SystemExit('Duplicate source ids: ' + ', '.join(dup))

    categorical = schema['categorical_values']
    account_by_id = {r['account_id']: r for r in account_rows}
    required_text = [
        'source_id', 'account_id', 'source_role', 'date', 'author', 'title',
        'source_type', 'source_url', 'citation_key', 'first_person',
        'public_artifact', 'build_provenance_available',
        'supports_account_observation', 'evidence_scope', 'source_note',
    ]
    errors = []
    primaries = Counter()
    source_by_id = {}
    for i, r in enumerate(rows, 2):
        source_by_id[r['source_id']] = r
        for key in required_text:
            if not r[key].strip():
                errors.append(f'source row {i}: blank {key}')
        if r['account_id'] not in account_by_id:
            errors.append(
                f'source row {i}: unknown account_id={r["account_id"]!r}'
            )
        if r['source_role'] not in categorical['source_role']:
            errors.append(f'source row {i}: bad source_role={r["source_role"]!r}')
        if r['source_type'] not in categorical['source_type']:
            errors.append(f'source row {i}: bad source_type={r["source_type"]!r}')
        for key in ['first_person', 'public_artifact', 'build_provenance_available']:
            if r[key] not in categorical['boolean_like']:
                errors.append(f'source row {i}: bad {key}={r[key]!r}')
        if r['supports_account_observation'] not in categorical['support']:
            errors.append(
                f'source row {i}: bad supports_account_observation='
                f'{r["supports_account_observation"]!r}'
            )
        if r['citation_key'] not in bib_keys:
            errors.append(
                f'source row {i}: missing bibliography key={r["citation_key"]!r}'
            )
        check_https(r['source_url'], f'source row {i}: source_url', errors)
        if r['source_role'] == 'primary':
            primaries[r['account_id']] += 1

    for account in account_rows:
        aid = account['account_id']
        primary_id = account['primary_source_id']
        source = source_by_id.get(primary_id)
        if source is None:
            errors.append(f'account {aid!r}: primary_source_id {primary_id!r} missing')
            continue
        if source['account_id'] != aid:
            errors.append(f'account {aid!r}: primary source belongs to another account')
        if source['source_role'] != 'primary':
            errors.append(f'account {aid!r}: primary_source_id is not role primary')
        if primaries[aid] != 1:
            errors.append(f'account {aid!r}: expected one primary source, got {primaries[aid]}')
        if account['account_kind'] == 'practitioner_account' and source['first_person'] != 'yes':
            errors.append(
                f'account {aid!r}: practitioner-account primary source must be first_person=yes'
            )
        if account['account_kind'] == 'human_study' and source['source_type'] != 'human_study':
            errors.append(f'account {aid!r}: human-study primary source_type must be human_study')

    if errors:
        raise SystemExit('\n'.join(errors))


def validate_screening(rows, account_rows, source_rows, bib_keys):
    schema = json.loads(SCREENING_SCHEMA_PATH.read_text(encoding='utf8'))
    check_columns(rows, schema, 'practitioner_account_screening.csv')

    ids = [r['candidate_id'] for r in rows]
    if len(ids) != len(set(ids)):
        dup = sorted({x for x in ids if ids.count(x) > 1})
        raise SystemExit('Duplicate screening candidate ids: ' + ', '.join(dup))

    categorical = schema['categorical_values']
    account_by_id = {r['account_id']: r for r in account_rows}
    source_by_id = {r['source_id']: r for r in source_rows}
    by_id = {r['candidate_id']: r for r in rows}
    required_text = [
        'candidate_id', 'screened_on', 'date', 'author', 'title', 'source_type',
        'source_url', 'discovery_route', 'decision', 'decision_reason',
    ]
    citation_required = {
        'include_account', 'supplemental_source', 'structured_study', 'related_work'
    }
    linked_decisions = {'include_account', 'supplemental_source'}
    errors = []

    for i, r in enumerate(rows, 2):
        for key in required_text:
            if not r[key].strip():
                errors.append(f'screening row {i}: blank {key}')
        if r['source_type'] not in categorical['source_type']:
            errors.append(f'screening row {i}: bad source_type={r["source_type"]!r}')
        if r['decision'] not in categorical['decision']:
            errors.append(f'screening row {i}: bad decision={r["decision"]!r}')
        check_https(r['source_url'], f'screening row {i}: source_url', errors)
        if r['citation_key'] and r['citation_key'] not in bib_keys:
            errors.append(
                f'screening row {i}: missing bibliography key={r["citation_key"]!r}'
            )
        if r['decision'] in citation_required and not r['citation_key'].strip():
            errors.append(f'screening row {i}: {r["decision"]} requires citation_key')

        if r['decision'] in linked_decisions:
            aid = r['account_id'].strip()
            if not aid:
                errors.append(f'screening row {i}: {r["decision"]} requires account_id')
            elif aid not in account_by_id:
                errors.append(f'screening row {i}: unknown account_id={aid!r}')
        elif r['account_id'].strip() and r['account_id'] not in account_by_id:
            errors.append(f'screening row {i}: unknown account_id={r["account_id"]!r}')

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

        if r['decision'] in {'include_account', 'supplemental_source'} or r['account_id'].strip():
            source = source_by_id.get(r['candidate_id'])
            if source is None:
                errors.append(
                    f'screening row {i}: linked source {r["candidate_id"]!r} missing from source table'
                )
            else:
                if source['account_id'] != r['account_id']:
                    errors.append(f'screening row {i}: source/account link differs from source table')
                if source['source_url'] != r['source_url']:
                    errors.append(f'screening row {i}: source_url differs from source table')
                if source['citation_key'] != r['citation_key']:
                    errors.append(f'screening row {i}: citation_key differs from source table')
                if r['decision'] == 'supplemental_source' and source['source_role'] == 'primary':
                    errors.append(f'screening row {i}: supplemental_source has primary source_role')

    for account in account_rows:
        primary_id = account['primary_source_id']
        screened = by_id.get(primary_id)
        if screened is None:
            errors.append(f'account {account["account_id"]!r}: primary source absent from screening log')
            continue
        expected = 'structured_study' if account['account_kind'] == 'human_study' else 'include_account'
        if screened['decision'] != expected:
            errors.append(
                f'account {account["account_id"]!r}: expected screening decision '
                f'{expected!r}, got {screened["decision"]!r}'
            )

    for source in source_rows:
        if source['source_role'] == 'primary':
            continue
        screened = by_id.get(source['source_id'])
        if screened is None:
            errors.append(f'non-primary source {source["source_id"]!r}: absent from screening log')
        elif screened['decision'] != 'supplemental_source':
            errors.append(
                f'non-primary source {source["source_id"]!r}: expected supplemental_source screening decision'
            )

    if errors:
        raise SystemExit('\n'.join(errors))


def main():
    rows = load_csv(ACCOUNTS_CSV)
    if not rows:
        raise SystemExit('No practitioner accounts found')
    validate_accounts(rows)
    accounts = [r for r in rows if r['account_kind'] == 'practitioner_account']
    studies = [r for r in rows if r['account_kind'] == 'human_study']

    bib = BIB_PATH.read_text(encoding='utf8')
    bib_keys = set(re.findall(r'@[A-Za-z]+\s*\{\s*([^,]+),', bib))

    sources = load_csv(SOURCES_CSV)
    if not sources:
        raise SystemExit('No practitioner-account sources found')
    validate_sources(sources, rows, bib_keys)

    screening = load_csv(SCREENING_CSV)
    if not screening:
        raise SystemExit('No practitioner-account screening entries found')
    validate_screening(screening, rows, sources, bib_keys)

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

    overlap_clusters = {r['practitioner_cluster'] for r in accounts}
    project_clusters = {r['project_cluster'] for r in accounts}
    supplemental = [r for r in sources if r['source_role'] != 'primary']

    macros = {
        'PractitionerAccountCount': len(accounts),
        'PractitionerOverlapClusterCount': len(overlap_clusters),
        'PractitionerProjectClusterCount': len(project_clusters),
        'PractitionerSourceCount': len([r for r in sources if r['account_id'] in {a['account_id'] for a in accounts}]),
        'PractitionerSupplementalSourceCount': len([r for r in supplemental if r['account_id'] in {a['account_id'] for a in accounts}]),
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
        'PractitionerScreenedSupplementalCount': sum(r['decision'] == 'supplemental_source' for r in screening),
        'PractitionerStructuredStudyCount': sum(r['decision'] == 'structured_study' for r in screening),
        'PractitionerRelatedWorkCount': sum(r['decision'] == 'related_work' for r in screening),
        'PractitionerHoldCount': sum(r['decision'] == 'hold' for r in screening),
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

    sources_by_account = {}
    for source in sources:
        sources_by_account.setdefault(source['account_id'], []).append(source)

    OUT_MD.parent.mkdir(parents=True, exist_ok=True)
    with OUT_MD.open('w', encoding='utf8') as f:
        f.write('# Public first-person project accounts of AI-assisted Lean work\n\n')
        f.write('This document is generated from `data/practitioner_accounts.csv`, `data/practitioner_account_sources.csv`, and `data/practitioner_account_screening.csv`. The account table is one row per project/workflow episode; URLs are separate source records so follow-up evidence does not inflate the account denominator. The categorical fields are documented in the corresponding schema files.\n\n')
        f.write('The accounts were found through LLM-assisted web search. Representativeness is unknown, so the rows should not be used to estimate prevalence. `yes` records an event or practice explicitly described by the source; `qualified`, `unclear`, and `not_reported` preserve uncertainty instead of filling it in.\n\n')
        f.write('`practitioner_cluster` records overlap between project accounts when a practitioner appears more than once; it is an overlap component, not a count of unique people. `project_cluster` can group multiple workflow episodes from one project. Primary, supplemental, and corroborating sources are kept separately.\n\n')
        f.write('The screening log was introduced on 2026-09-08. It records the preexisting included snapshot and candidates reviewed during the current expansion; it does not reconstruct every source encountered in earlier searches and should not be read as an exhaustive search record.\n\n')

        f.write('## Descriptive counts\n\n')
        f.write(f'- Public first-person project/workflow accounts: **{len(accounts)}**\n')
        f.write(f'- Practitioner-overlap clusters: **{len(overlap_clusters)}**\n')
        f.write(f'- Public source records attached to practitioner accounts: **{macros["PractitionerSourceCount"]}**\n')
        f.write(f'- Supplemental/corroborating source records: **{macros["PractitionerSupplementalSourceCount"]}**\n')
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
        f.write(f'- Included project accounts: **{macros["PractitionerScreenedIncludeCount"]}**\n')
        f.write(f'- Supplemental/corroborating sources: **{macros["PractitionerScreenedSupplementalCount"]}**\n')
        f.write(f'- Structured studies: **{macros["PractitionerStructuredStudyCount"]}**\n')
        f.write(f'- Related-work-only sources: **{macros["PractitionerRelatedWorkCount"]}**\n')
        f.write(f'- Holds awaiting stronger first-person evidence: **{macros["PractitionerHoldCount"]}**\n')
        f.write(f'- True duplicates: **{macros["PractitionerDuplicateCount"]}**\n')
        f.write(f'- Excluded: **{macros["PractitionerExcludeCount"]}**\n\n')
        f.write('| Candidate | Decision | Account | Discovery route | Reason |\n')
        f.write('|---|---|---|---|---|\n')
        for r in screening:
            reason = r['decision_reason'].replace('|', '/')
            f.write(f'| `{r["candidate_id"]}` | `{r["decision"]}` | `{r["account_id"]}` | `{r["discovery_route"]}` | {reason} |\n')
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
        f.write('| Account | Practitioner cluster | Author | Lean experience | Reads generated Lean | Separate AI review | Semantic mismatch | Source defect | Persistent state |\n')
        f.write('|---|---|---|---|---|---|---|---|---|\n')
        for r in accounts:
            f.write('| `{}` | `{}` | {} | `{}` | `{}` | `{}` | `{}` | `{}` | `{}` |\n'.format(
                r['account_id'], r['practitioner_cluster'], r['author'].replace('|', '/'),
                r['reported_lean_experience'], r['reads_generated_lean'], r['separate_ai_review'],
                r['semantic_mismatch'], r['source_defect_found'], r['persistent_project_state']))
        f.write('\n')

        f.write('## Account and source records\n\n')
        for i, r in enumerate(rows, 1):
            f.write(f'### {i}. {r["author"]} - {r["title"]}\n\n')
            f.write(f'- **Account ID:** `{r["account_id"]}`\n')
            f.write(f'- **Account kind:** `{r["account_kind"]}`\n')
            f.write(f'- **Practitioner-overlap cluster:** `{r["practitioner_cluster"]}`\n')
            f.write(f'- **Project cluster:** `{r["project_cluster"]}`\n')
            f.write(f'- **Date:** {r["date"]}\n')
            f.write(f'- **Target:** {r["target"]}\n')
            f.write(f'- **Reported Lean experience:** `{r["reported_lean_experience"]}`\n')
            f.write(f'- **Reads generated Lean:** `{r["reads_generated_lean"]}`\n')
            f.write(f'- **Multiple AI tools:** `{r["multiple_ai_tools"]}`; **separate AI review:** `{r["separate_ai_review"]}`\n')
            f.write(f'- **Semantic mismatch:** `{r["semantic_mismatch"]}`; **source defect found:** `{r["source_defect_found"]}`; **counterexample used:** `{r["counterexample_used"]}`\n')
            f.write(f'- **Persistent project state:** `{r["persistent_project_state"]}`; **post-hoc understanding:** `{r["posthoc_understanding"]}`\n')
            f.write(f'- **Human role described:** {r["human_role"]}\n')
            f.write(f'- **Observation used by the paper:** {r["observation"]}\n')
            f.write(f'- **Account note:** {r["account_note"]}\n')
            f.write('- **Sources:**\n')
            for source in sources_by_account.get(r['account_id'], []):
                f.write(
                    f'  - `{source["source_id"]}` (`{source["source_role"]}`; '
                    f'`{source["source_type"]}`; first-person `{source["first_person"]}`; '
                    f'public artifact `{source["public_artifact"]}`; build/provenance '
                    f'`{source["build_provenance_available"]}`): {source["title"]}; '
                    f'citation `{source["citation_key"]}`; {source["source_url"]}\n'
                )
                f.write(f'    Evidence scope: {source["evidence_scope"]}. {source["source_note"]}\n')
            f.write('\n')

    print(f'validated {len(rows)} account records ({len(accounts)} practitioner accounts, {len(studies)} studies)')
    print(f'validated {len(sources)} source records')
    print(f'validated {len(screening)} screening entries')
    print(f'wrote {OUT_TEX}')
    print(f'wrote {OUT_MD}')


if __name__ == '__main__':
    main()
