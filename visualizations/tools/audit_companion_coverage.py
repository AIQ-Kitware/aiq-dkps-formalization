#!/usr/bin/env python3
"""Audit visual coverage of available DKPS lectures and expansion backlog.

The G1 lectures have their own Manim presentations; G2/G3 audio lectures
require a linked companion deck. Planned G4 nodes are reported, not treated as
missing currently available content.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from dkvis.presentation.course_graph import build_course_graph
from dkvis.presentation.companion_slides import CompanionSlideLibrary


def audit(graph=None, library=None):
    graph = graph or build_course_graph()
    library = library or CompanionSlideLibrary()
    entries = library.catalog()
    linked = {}
    for deck in entries:
        for node in deck['lecture_nodes']:
            linked.setdefault(node, []).append(deck)
    rows=[]
    # Graph paths may reuse nodes from other tracks; count distinct nodes.
    for node_id, item in graph['nodes'].items():
        if item['status'] != 'available':
            stage = 'planned'
        elif item['track'] == 'g1' and item['kind'] == 'presentation':
            stage = 'native-presentation'
        else:
            stages = {entry['editorial_stage'] for entry in linked.get(node_id, [])}
            stage = 'expanded' if 'expanded' in stages else 'baseline' if 'baseline' in stages else 'missing'
        # Some lecture headings include their numeric identifier. The ID is
        # already presented in its own column, so avoid repeating it.
        import re
        title = re.sub(r'^\d{6}\s*[—–-]\s*', '', item['title'])
        rows.append(dict(node=node_id,title=title,track=item['track'],
                         stage=stage,needs_expansion=stage=='baseline',
                         deck_ids=[e['id'] for e in linked.get(node_id, [])]))
    return rows


def report(rows):
    counts=Counter(r['stage'] for r in rows)
    available=sum(r['stage'] != 'planned' for r in rows)
    covered=available-counts['missing']
    md=[
        '# DKPS lecture slide coverage and expansion backlog', '',
        'This inventory is derived from the course graph and the source-controlled deck manifest.',
        'The `baseline` label means a source-derived reading outline is available **and needs expansion**.',
        'The `expanded` label means a separately developed companion deck exists; it is not a final visual-quality certification.',
        'G1 already consists of native Manim visual presentations. G4 is still planned.', '',
        f'**Available lecture coverage: {covered}/{available}.**', '',
        '| Stage | Lectures | Expansion needed |', '|---|---:|---|',
        f'| Native G1 presentations | {counts["native-presentation"]} | No companion required |',
        f'| Expanded G2/G3 companions | {counts["expanded"]} | Optional editorial refinement |',
        f'| G2 baseline companions | {counts["baseline"]} | **Yes** |',
        f'| Available lectures missing slides | {counts["missing"]} | Urgent |',
        f'| Planned G4 nodes | {counts["planned"]} | Not available yet |', '',
        '## Baseline companions requiring expansion', '',
        'Prioritize specific high-value proofs and examples rather than rewriting the entire course at once.',
        'Each item below already has a readable outline; expand it with exact typeset mathematics, worked cases, topic-specific diagrams, and slide-by-slide layout review.', '',
    ]
    for start in (30, 60, 90, 120):
        group=[r for r in rows if r['stage']=='baseline' and r['track']=='g2' and start<=int(r['node'][3:])//1000 < start+30]
        if not group: continue
        md += [f'### G2 {start:03d}000–{start+29:03d}000 ({len(group)} baseline decks)', '']
        md += [f'- [ ] `{r["node"]}` — {r["title"]} (`{r["deck_ids"][0] if r["deck_ids"] else "missing"}`)' for r in group]
        md += ['']
    if counts['missing']:
        md+=['## Available lectures with no visual coverage','']
        md += [f'- `{r["node"]}` — {r["title"]}' for r in rows if r['stage']=='missing']
        md += ['']
    md += [
        '## Promotion checklist', '',
        'When a baseline is expanded, update its deck source and set `editorial_stage` to `expanded` in `companion-slides/manifest.json`.',
        'Preserve the source lecture link and avoid changing the TTS narration or audio cache.',
        'Expansion requires: stand-alone mathematical definitions and hypotheses; important proof steps and a complete worked example;',
        'correct MathTex/LaTeX vector formulas; helpful topic-specific diagrams; and HTML/PowerPoint visual overflow checks.', '',
        '## Recheck', '',
        '```bash',
        'cd visualizations',
        'python tools/audit_companion_coverage.py --check',
        'python tools/audit_companion_coverage.py --write-report',
        '```', '',
        'The coverage status is available to the `/audio` browser from the deck API. This checklist is not a queue managed by another agent.', ''
    ]
    return '\n'.join(md)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='Return a nonzero code if any available lecture lacks slides')
    parser.add_argument('--write-report',action='store_true',help='Write the source-controlled markdown backlog')
    args=parser.parse_args()
    rows=audit()
    counts=Counter(x['stage'] for x in rows)
    print('Coverage:',dict(counts))
    if args.write_report:
        file=ROOT/'docs'/'companion-slide-coverage.md'
        file.write_text(report(rows),encoding='utf8')
        print('Wrote',file)
    if args.check and counts['missing']:
        raise SystemExit(f'{counts["missing"]} available lecture(s) lack companion slides')

if __name__ == '__main__':
    main()
