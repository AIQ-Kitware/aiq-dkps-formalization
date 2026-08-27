#!/usr/bin/env python3
"""Validate, probe, and render the Acharyya/Helm/Quench source censuses.

The JSON files are authoritative; the Markdown files are generated views.

Usage:
    python3 scripts/check_dkps_application_source_censuses.py
    python3 scripts/check_dkps_application_source_censuses.py --render
    python3 scripts/check_dkps_application_source_censuses.py --probe
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SLUGS = ('acharyya-2024', 'acharyya-2025', 'helm-2025', 'quench-2026')
JSONS = [ROOT / 'dev' / f'{s}-full-source-census.json' for s in SLUGS]
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |scoped )*"
    r"(?:alias|theorem|lemma|def|abbrev|structure|instance|class)\s+"
    # Lean identifiers admit subscript and superscript digits (eigenvalues₀_...); without
    # them the scan silently truncates such a name and the citation cannot be resolved.
    r"([A-Za-z_][A-Za-z0-9_'.₀-₉⁰-⁹]*)", re.M)
IMPORTS = [
    'Acharyya2024',
    'Acharyya2025.Bridge', 'Acharyya2025.ConfigPerturbation',
    'Acharyya2025.MathlibBridge', 'Acharyya2025.SpectralPipeline',
    'Acharyya2025.AlignedPipeline', 'Acharyya2025.GrowingResponse',
    'Acharyya2025.PaperRate', 'Acharyya2025.RateChain', 'Acharyya2025.Overlap',
    'Acharyya2025.ManifoldCondition', 'Acharyya2025.Theorem1Scale',
    'Helm2025', 'DkpsQuench2026',
    'ForTauCeti.Probability.AverageError',
    'ForTauCeti.Probability.VStatistic',
]
CANARY = 'DkpsApplicationCensusProbeCanaryMustNotResolve'


def fail(msg: str) -> None:
    raise SystemExit(f'ERROR: {msg}')


def load(path: Path) -> dict:
    try:
        return json.loads(path.read_text())
    except Exception as ex:
        fail(f'{path}: {ex}')


def check_schema(path: Path, data: dict) -> list[dict]:
    if data.get('census_kind') != 'dkps_application_source_semantic_alignment':
        fail(f'{path}: wrong census_kind')
    items = data.get('items')
    if not isinstance(items, list) or not items:
        fail(f'{path}: items must be nonempty')
    statuses = set(data.get('status_definitions', {}))
    verifications = set(data.get('verification_definitions', {}))
    alignments = set(data.get('semantic_alignment_definitions', {}))
    gaps = data.get('gaps', {})
    if not statuses or not verifications or not alignments:
        fail(f'{path}: missing definition tables')
    ids = set()
    referenced_gaps = set()
    for row in items:
        rid = row.get('id')
        if not rid or rid in ids:
            fail(f'{path}: missing/duplicate id {rid!r}')
        ids.add(rid)
        for field in ('importance','section','source_anchor','source_kind','title',
                      'source_claim','status','verification','notes','next_action'):
            if not isinstance(row.get(field), str) or not row[field].strip():
                fail(f'{path}: {rid} has empty {field}')
        if row['status'] not in statuses:
            fail(f'{path}: {rid} bad status {row["status"]}')
        if row['verification'] not in verifications:
            fail(f'{path}: {rid} bad verification {row["verification"]}')
        # The verification axis has to agree with what the row actually cites.  A row that
        # says 'absent' while citing declarations, or 'proved_in_build' while citing none,
        # reads as an internal contradiction to a hostile reviewer -- and is how a status
        # upgrade silently leaves the verification field behind.
        decls = row.get('lean_declarations') or []
        if row['verification'] == 'absent' and decls:
            fail(f'{path}: {rid} verification absent but cites {len(decls)} declaration(s)')
        if row['verification'] == 'proved_in_build' and not decls:
            fail(f'{path}: {rid} verification proved_in_build but cites no declaration')
        if row['status'].startswith('compiled') and row['verification'] == 'absent':
            fail(f'{path}: {rid} status {row["status"]} but verification absent')
        # Line-number citations into the prose rot silently when those files are edited.
        # Only the exact checks are gated here -- the file exists and the range lies inside
        # it.  Matching the anchor text against the range was tried and produced false
        # positives on LaTeX displays, and a check people learn to ignore is worse than none.
        loc = row.get('source_locator') or {}
        src, lines = loc.get('file'), loc.get('lines')
        if not src or not isinstance(lines, list) or len(lines) != 2:
            fail(f'{path}: {rid} missing or malformed source_locator')
        else:
            srcp = Path(src)
            if not srcp.exists():
                fail(f'{path}: {rid} source_locator file does not exist: {src}')
            else:
                total = len(srcp.read_text(errors='ignore').split('\n'))
                lo, hi = lines
                if not (1 <= lo <= hi <= total):
                    fail(f'{path}: {rid} source_locator lines {lo}-{hi} outside {src} '
                         f'(which has {total} lines)')
        sem = row.get('semantic_alignment', {})
        if sem.get('classification') not in alignments or not sem.get('detail'):
            fail(f'{path}: {rid} bad semantic_alignment')
        loc = row.get('source_locator', {})
        src = ROOT / loc.get('file','')
        lines = loc.get('lines')
        if not src.is_file():
            fail(f'{path}: {rid} source file missing: {src}')
        if not (isinstance(lines, list) and len(lines)==2 and
                all(isinstance(x,int) and x>0 for x in lines) and lines[0] <= lines[1]):
            fail(f'{path}: {rid} bad source line range')
        nlines = sum(1 for _ in src.open(errors='ignore'))
        if lines[1] > nlines:
            fail(f'{path}: {rid} source range ends at {lines[1]}, file has {nlines} lines')
        for key in row.get('gap_refs', []):
            if key not in gaps:
                fail(f'{path}: {rid} refers to absent gap {key}')
            referenced_gaps.add(key)
        for field in ('lean_declarations','planned_declarations','gap_refs'):
            if not isinstance(row.get(field), list):
                fail(f'{path}: {rid} {field} must be a list')
    orphan = set(gaps) - referenced_gaps
    if orphan:
        fail(f'{path}: orphan gaps: {sorted(orphan)}')
    return items


def declared_short_names() -> set[str]:
    out = set()
    for path in ROOT.rglob('*.lean'):
        rel = path.relative_to(ROOT)
        if 'external' in rel.parts or any(p.startswith('.') for p in rel.parts):
            continue
        out.update(name.rsplit('.', 1)[-1] for name in DECL_RE.findall(path.read_text(errors='ignore')))
    return out


def check_names(all_rows: list[dict]) -> list[str]:
    names = declared_short_names()
    refs = []
    for row in all_rows:
        for ref in row['lean_declarations']:
            short = ref.rsplit('.',1)[-1]
            if short not in names:
                fail(f'{row["id"]}: cited declaration not found by short name: {ref}')
            refs.append(ref)
        for ref in row['planned_declarations']:
            short = ref.rsplit('.',1)[-1]
            if short in names:
                fail(f'{row["id"]}: planned declaration now exists: {ref}')
    return list(dict.fromkeys(refs))


def probe(refs: list[str]) -> None:
    p = ROOT / 'dev' / '.dkps-application-census-probe.lean'
    lines = [*(f'import {m}\n' for m in IMPORTS), '\n']
    line_to_ref = {}
    for ref in refs:
        line_no = len(lines) + 1
        lines.append(f'#check @{ref}\n')
        line_to_ref[line_no] = ref
    canary_line = len(lines) + 1
    lines.append(f'#check @{CANARY}\n')
    p.write_text(''.join(lines))
    try:
        proc = subprocess.run(['lake','env','lean','-DmaxErrors=100000',str(p)],
                              cwd=ROOT, text=True, capture_output=True)
    except FileNotFoundError:
        fail('lake is unavailable; run without --probe or probe in the Lean environment')
    out = proc.stdout + proc.stderr
    errors = {}
    for m in re.finditer(re.escape(p.name)+r':(\d+):\d+: error', out):
        errors[int(m.group(1))] = True
    if canary_line not in errors:
        fail('probe canary unexpectedly resolved; diagnostic parser is unreliable')
    unresolved = [ref for line,ref in line_to_ref.items() if line in errors]
    if unresolved:
        fail('Lean probe failed for:\n  ' + '\n  '.join(unresolved))
    print(f'Lean probe resolved {len(refs)} cited declarations.')
    p.unlink(missing_ok=True)


def render(path: Path, data: dict) -> None:
    out = []
    paper = data['paper']
    title = {'acharyya-2024':'Acharyya et al. 2024',
             'acharyya-2025':'Acharyya et al. 2025',
             'helm-2025':'Helm et al. 2025',
             'quench-2026':'Helm--Johnson--Priebe 2026 (Quench)'}[path.name.split('-full-source-census')[0]]
    out += ['<!-- generated by scripts/check_dkps_application_source_censuses.py --render; edit the JSON, not this file -->','',f'# {title} full-paper source census','',paper['citation'],'',f'**Source version:** {paper["source_version"]}','',f'**Audit revision:** {data["audit_revision"]}','',data['scope'],'']
    if data.get('notes'):
        out += ['## Current audit note','',data['notes'],'']
    out += ['## Status summary','', '| status | items |','| --- | ---: |']
    counts=collections.Counter(r['status'] for r in data['items'])
    for k in data['status_definitions']:
        if counts[k]: out.append(f'| `{k}` | {counts[k]} |')
    out += ['','## Semantic-alignment summary','', '| classification | items |','| --- | ---: |']
    ac=collections.Counter(r['semantic_alignment']['classification'] for r in data['items'])
    for k in data['semantic_alignment_definitions']:
        if ac[k]: out.append(f'| `{k}` | {ac[k]} |')
    out += ['','## Items','', '| id | importance | source anchor | status | alignment | verification |','| --- | --- | --- | --- | --- | --- |']
    for r in data['items']:
        out.append(f'| `{r["id"]}` | `{r["importance"]}` | {r["source_anchor"]} | `{r["status"]}` | `{r["semantic_alignment"]["classification"]}` | `{r["verification"]}` |')
    out += ['','## Gaps and source repairs','']
    for key,g in data['gaps'].items():
        out += [f'### `{key}` — {g["title"]}','',f'**Kind:** `{g["kind"]}`','',g['detail'],'']
    out += ['## Detail','']
    for r in data['items']:
        loc=r['source_locator']; refs=r['lean_declarations']; planned=r['planned_declarations']
        out += [f'### `{r["id"]}` — {r["title"]}','',
                f'* **source anchor:** {r["source_anchor"]} ({r["source_kind"]}, section {r["section"]})',
                f'* **source locator:** `{loc["file"]}:{loc["lines"][0]}-{loc["lines"][1]}`',
                f'* **importance:** `{r["importance"]}`',
                f'* **status / verification:** `{r["status"]}` / `{r["verification"]}`',
                f'* **semantic alignment:** `{r["semantic_alignment"]["classification"]}` — {r["semantic_alignment"]["detail"]}',
                f'* **source claim:** {r["source_claim"]}']
        out.append('* **Lean declarations:** ' + (', '.join(f'`{x}`' for x in refs) if refs else '_none_'))
        if planned: out.append('* **planned declarations:** ' + ', '.join(f'`{x}`' for x in planned))
        if r['gap_refs']: out.append('* **gap refs:** ' + ', '.join(f'`{x}`' for x in r['gap_refs']))
        out += [f'* **notes:** {r["notes"]}',f'* **next action:** {r["next_action"]}','']
    md = path.with_suffix('.md')
    md.write_text('\n'.join(out).rstrip()+'\n')


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument('--render',action='store_true')
    ap.add_argument('--probe',action='store_true')
    args=ap.parse_args()
    all_rows=[]; loaded=[]
    for path in JSONS:
        data=load(path); rows=check_schema(path,data); all_rows += rows; loaded.append((path,data))
    refs=check_names(all_rows)
    if args.probe: probe(refs)
    if args.render:
        for path,data in loaded: render(path,data)
    print(f'OK: {len(JSONS)} censuses, {len(all_rows)} source rows, {len(refs)} cited Lean declarations.')

if __name__ == '__main__': main()
