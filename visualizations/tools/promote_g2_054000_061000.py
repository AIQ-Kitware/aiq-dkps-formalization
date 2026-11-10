#!/usr/bin/env python3
"""Promote G2 054000-061000 companions without replacing shared manifest edits.

Invoke after extracting the companion JSON and figures:
    python3 visualizations/tools/promote_g2_054000_061000.py --write
    python3 visualizations/tools/promote_g2_054000_061000.py --check
"""
from __future__ import annotations

import argparse
import json
import os
import tempfile
from pathlib import Path

G2_BATCH4_DECK_DIRECTORY = Path(__file__).resolve().parents[1] / 'companion-slides'
G2_BATCH4_NODES = tuple(f'g2:{n:03d}000' for n in range(54, 62))


def inspect_g2_054000_061000_manifest():
    path = G2_BATCH4_DECK_DIRECTORY / 'manifest.json'
    data = json.loads(path.read_text(encoding='utf8'))
    if data.get('schema_version') != 1 or not isinstance(data.get('decks'), list):
        raise ValueError('Invalid companion deck manifest')
    pending = []
    for node in G2_BATCH4_NODES:
        rows = [item for item in data['decks'] if item.get('lecture_nodes') == [node]]
        if len(rows) != 1:
            raise ValueError(f'{node}: expected exactly one companion deck, found {len(rows)}')
        row = rows[0]
        if row.get('source') != row.get('id', '') + '.json':
            raise ValueError(f'{node}: mismatched manifest filename')
        source = G2_BATCH4_DECK_DIRECTORY / row['source']
        deck = json.loads(source.read_text(encoding='utf8'))
        if (deck.get('id') != row['id'] or deck.get('lecture_nodes') != [node]
                or deck.get('editorial_stage') != 'expanded'
                or len(deck.get('slides', [])) < 9):
            raise ValueError(f'{node}: expected expanded deck source')
        if row['editorial_stage'] == 'baseline':
            row['editorial_stage'] = 'expanded'
            pending.append(node)
        elif row['editorial_stage'] != 'expanded':
            raise ValueError(f'{node}: unsupported manifest stage')
    return path, data, pending


def promote_g2_054000_061000_manifest(*, write):
    path, data, pending = inspect_g2_054000_061000_manifest()
    if write and pending:
        fd, temporary = tempfile.mkstemp(prefix='.g2-batch4-manifest-',
                                          suffix='.tmp', dir=path.parent)
        try:
            with os.fdopen(fd, 'w', encoding='utf8') as stream:
                json.dump(data, stream, indent=2, ensure_ascii=False)
                stream.write('\n')
            os.replace(temporary, path)
        finally:
            Path(temporary).unlink(missing_ok=True)
    return pending


def cli_promote_g2_054000_061000():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    pending = promote_g2_054000_061000_manifest(write=args.write)
    if args.check and pending:
        parser.error('Not promoted: ' + ', '.join(pending))
    print(f'G2 054000–061000: {8-len(pending)}/8 promoted; {len(pending)} pending')


if __name__ == '__main__':
    cli_promote_g2_054000_061000()
