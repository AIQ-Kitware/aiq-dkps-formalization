#!/usr/bin/env python3
"""Validate and export non-spoken lecture references.

The TTS extractor stays authoritative for voice input. Metadata lives in
metadata/*.json and never enters extracted narration. This module offers a
validated join for a future learning service; it is not part of TTS synthesis.

Usage:
    python3 reference_metadata.py --check
    python3 reference_metadata.py --json 053000
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
from urllib.parse import urlparse

from extract_narration import extract

HERE = Path(__file__).resolve().parent
METADATA = HERE / 'metadata'
LECTURE_NAME = re.compile(r'^([0-9]{6})-[a-z0-9-]+\.md$')
IDS = re.compile(r'^[a-z0-9]+(?:-[a-z0-9]+)*$')
CLAIM_KINDS = {'historical_attribution', 'source_attribution', 'source_scope', 'source_method'}
AUDIT_STATES = {'pending_primary_passage_comparison', 'primary_passage_confirmed', 'claim_needs_correction'}


def load_catalog(path: Path = METADATA / 'sources.json') -> dict:
    payload = json.loads(path.read_text(encoding='utf-8'))
    if payload.get('schema_version') != 1 or not isinstance(payload.get('sources'), dict):
        raise ValueError(f'{path}: unsupported reference catalog schema')
    sources = payload['sources']
    for key, item in sources.items():
        if not IDS.fullmatch(key):
            raise ValueError(f'{path}: invalid reference ID {key!r}')
        if not isinstance(item.get('title'), str) or not item['title'].strip():
            raise ValueError(f'{path}: missing title for {key}')
        if not isinstance(item.get('kind'), str) or not item['kind'].strip():
            raise ValueError(f'{path}: missing kind for {key}')
        parsed = urlparse(item.get('url', ''))
        if parsed.scheme != 'https' or not parsed.netloc:
            raise ValueError(f'{path}: source {key} requires HTTPS URL')
    return sources


def _match_anchor(narration: str, anchor: str, where: str) -> tuple[int, int]:
    if not isinstance(anchor, str) or len(anchor.strip()) < 35:
        raise ValueError(f'{where}: anchor must be an exact quoted excerpt (at least 35 characters)')
    # Reflow in the source must not invalidate an anchor. Match spaces, tabs and
    # newlines as equivalent, but never silently fuzzy-match changed words.
    expression = r'\s+'.join(re.escape(token) for token in anchor.split())
    matches = list(re.finditer(expression, narration))
    if len(matches) != 1:
        raise ValueError(f'{where}: historical anchor has {len(matches)} matches, expected exactly one: {anchor!r}')
    return matches[0].span()


def validate_lecture(path: Path, sources: dict, metadata_dir: Path = METADATA) -> dict:
    path = Path(path)
    name_match = LECTURE_NAME.fullmatch(path.name)
    if not name_match:
        raise ValueError(f'{path}: invalid transcript filename')
    lecture_id = name_match.group(1)
    sidecar_path = metadata_dir / (lecture_id + '.json')
    item = json.loads(sidecar_path.read_text(encoding='utf-8'))
    if item.get('schema_version') != 1:
        raise ValueError(f'{sidecar_path}: unsupported schema version')
    if item.get('lecture_id') != lecture_id or item.get('transcript') != path.name:
        raise ValueError(f'{sidecar_path}: transcript ID or filename drift')
    claims = item.get('historical_claims')
    readings = item.get('related_resources')
    if not isinstance(claims, list) or not isinstance(readings, list):
        raise ValueError(f'{sidecar_path}: historical_claims and related_resources must be arrays')
    narration = extract(path)
    used_claim_ids = set()
    joined_claims = []
    for claim in claims:
        claim_id = claim.get('id')
        if (not isinstance(claim_id, str) or
                not claim_id.startswith(lecture_id + '-h') or claim_id in used_claim_ids):
            raise ValueError(f'{sidecar_path}: duplicate or malformed claim ID {claim_id!r}')
        used_claim_ids.add(claim_id)
        if claim.get('kind') not in CLAIM_KINDS or claim.get('audit_status') not in AUDIT_STATES:
            raise ValueError(f'{sidecar_path}: invalid claim kind/audit_status: {claim_id}')
        source_ids = claim.get('source_ids')
        if not isinstance(source_ids, list) or not source_ids or any(sid not in sources for sid in source_ids):
            raise ValueError(f'{sidecar_path}: unknown or missing source for {claim_id}')
        if not isinstance(claim.get('source_locator'), str) or not claim['source_locator'].strip():
            raise ValueError(f'{sidecar_path}: missing source locator for {claim_id}')
        if claim['audit_status'] == 'primary_passage_confirmed':
            verification = claim.get('verification')
            if not isinstance(verification, dict) or not all(
                isinstance(verification.get(key), str) and verification[key].strip()
                for key in ('reviewer', 'checked_on', 'primary_locator')
            ):
                raise ValueError(f'{sidecar_path}: confirmed claim {claim_id} needs reviewer, checked_on and primary_locator')
        if claim['audit_status'] == 'claim_needs_correction':
            if not isinstance(claim.get('issue'), str) or not claim['issue'].strip():
                raise ValueError(f'{sidecar_path}: flagged claim {claim_id} needs an issue description')
        start, end = _match_anchor(narration, claim.get('anchor'), f'{sidecar_path}:{claim_id}')
        joined_claims.append({**claim, 'start': start, 'end': end})
    seen_resource_ids = set()
    for reading in readings:
        sid = reading.get('source_id')
        if sid not in sources or sid in seen_resource_ids:
            raise ValueError(f'{sidecar_path}: duplicate or unknown related resource {sid!r}')
        seen_resource_ids.add(sid)
        if not isinstance(reading.get('reason'), str) or not reading['reason'].strip():
            raise ValueError(f'{sidecar_path}: missing reading relevance note for {sid!r}')
    return {**item, 'historical_claims': joined_claims, 'narration': narration}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--check', action='store_true', help='validate the lecture sidecars and their narration anchors')
    group.add_argument('--json', metavar='LECTURE_ID', help='emit a validated future-server record as JSON')
    args = parser.parse_args()
    try:
        sources = load_catalog()
        paths = sorted(HERE.glob('[0-9]*-*.md'))
        if args.check:
            sidecars = sorted(METADATA.glob('[0-9]*.json'))
            if len(paths) < 150 or len(sidecars) != len(paths):
                raise ValueError(f'Expected at least 150 transcripts and matching sidecars; found {len(paths)} and {len(sidecars)}')
            parsed = [validate_lecture(path, sources) for path in paths]
            expected = {d['lecture_id']+'.json' for d in parsed}
            if {path.name for path in sidecars} != expected:
                raise ValueError('Orphan or missing per-lecture sidecar detected')
            print(f"Validated {len(parsed)} lecture sidecars, "
                  f"{sum(len(x['historical_claims']) for x in parsed)} claim anchors, "
                  f"{sum(len(x['related_resources']) for x in parsed)} related-resource links, "
                  f"{len(sources)} catalog sources.")
            return 0
        if not re.fullmatch(r'[0-9]{6}', args.json):
            raise ValueError(f'Invalid lecture ID: {args.json!r}')
        matched = [path for path in paths if path.name.startswith(args.json + '-')]
        if len(matched) != 1:
            raise ValueError(f'Expected one transcript for lecture {args.json}')
        result = validate_lecture(matched[0], sources)
        reference_ids = set()
        for claim in result['historical_claims']:
            reference_ids.update(claim['source_ids'])
        reference_ids.update(r['source_id'] for r in result['related_resources'])
        result['sources'] = {sid: sources[sid] for sid in sorted(reference_ids)}
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
