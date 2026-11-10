#!/usr/bin/env python3
"""Verify the G3 listening order, independent narration, and Proposition 4.3 bridge.

This is a source-level regression check for known G2-to-G3 adaptation defects.
It is deliberately stricter about inventory and named stale references than
about ordinary prose that might legitimately contain temporal language.
"""
from __future__ import annotations

import json
from pathlib import Path

from dkvis.presentation.audio_library import PAPER_DIRECTORY, narration_extractor
from dkvis.presentation.companion_slides import CompanionSlideLibrary
from dkvis.presentation.course_graph import build_course_graph

EXPECTED_FOUR_THEOREMS = ['020000', '021000', '022000', '023000']
EXPECTED_SECTION_FOUR = ['017000', '018000', '018500', '019000', '024000', '025000']
BANNED_FRAGMENTS = {
    '005000': ['the coming defect-matching problem'],
    '016000': ['we will show how that smallness', 'demands quantitative smallness'],
    '018000': ['our Hilbert–Schmidt lectures'],
    '019000': ['the explicit singular values give a strict numerical contradiction'],
    '020000': ['write e as u times its positive modulus'],
    '022000': ['later spectral-selection results will supply'],
}


def audit_g3_presentation_contract(*, directory=PAPER_DIRECTORY) -> dict:
    directory = Path(directory)
    plan = json.loads((directory / 'track.json').read_text(encoding='utf8'))
    rows = plan['lectures']
    order = [row['id'] for row in rows]
    errors = []
    if len(order) != len(set(order)) or len(order) != 27:
        errors.append('G3 must have 27 distinct lecture IDs')
    if order[17:21] != EXPECTED_FOUR_THEOREMS:
        errors.append('The four angle theorems must form a consecutive block')
    if order[-6:] != EXPECTED_SECTION_FOUR:
        errors.append('Section 4 must end in a contiguous six-lecture block')
    files = {path.name for path in directory.glob('[0-9]' * 6 + '-*.md')}
    if files != {row['file'] for row in rows}:
        errors.append('G3 track inventory disagrees with source files')
    stages = [row['section'] for row in rows]
    for section in set(stages):
        positions = [i for i, item in enumerate(stages) if item == section]
        if positions != list(range(positions[0], positions[-1] + 1)):
            errors.append(f'Non-contiguous G3 section: {section}')
    total_words = 0
    for row in rows:
        path = directory / row['file']
        if not path.is_file():
            continue
        text = path.read_text(encoding='utf8')
        if f'**Section:** {row["section"]}.' not in text:
            errors.append(f'{row["id"]} has a stale section label')
        spoken = narration_extractor(path)
        total_words += len(spoken.split())
        if len(spoken.split()) != row['spoken_words']:
            errors.append(f'{row["id"]} has stale spoken_words')
        for fragment in BANNED_FRAGMENTS.get(row['id'], []):
            if fragment in spoken.lower():
                errors.append(f'{row["id"]} retains: {fragment}')
    new_text = (directory / '018500-whole-space-squared-displacement-proposition-4-3.md').read_text(encoding='utf8')
    for necessary in ('pinching', 'Ky Fan', 'Q-norm', 'Proposition four point three', 'five and one to three and three'):
        if necessary not in new_text:
            errors.append(f'Proposition 4.3 is missing: {necessary}')
    if directory.resolve() == PAPER_DIRECTORY.resolve():
        graph = build_course_graph()
        if [n.removeprefix('g3:') for n in graph['tracks'][2]['path']] != order:
            errors.append('Course graph order differs from G3 track.json')
        deck_nodes={n for row in CompanionSlideLibrary().catalog() for n in row['lecture_nodes']}
        if not {f'g3:{i}' for i in order} <= deck_nodes:
            errors.append('G3 slide coverage is incomplete')
    return dict(lecture_count=len(rows), spoken_words=total_words, issues=errors)


def main():
    result = audit_g3_presentation_contract()
    print(f'G3: {result["lecture_count"]} recordings, '
          f'{result["spoken_words"]} spoken words, {len(result["issues"])} issue(s)')
    if result['issues']:
        for issue in result['issues']:
            print(' -', issue)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
