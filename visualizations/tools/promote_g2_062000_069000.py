#!/usr/bin/env python3
"""Promote eight expanded G2 Sylvester decks without clobbering shared edits.

    python3 visualizations/tools/promote_g2_062000_069000.py --write
    python3 visualizations/tools/promote_g2_062000_069000.py --check
"""
from __future__ import annotations
import argparse
import json
import os
import tempfile
from pathlib import Path

G2_SYLVESTER_DECK_DIRECTORY = Path(__file__).resolve().parents[1] / 'companion-slides'
G2_SYLVESTER_NODES = tuple(f'g2:{i:03d}000' for i in range(62, 70))


def inspect_g2_sylvester_promotion():
    manifest_path = G2_SYLVESTER_DECK_DIRECTORY / 'manifest.json'
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    if manifest.get('schema_version') != 1 or not isinstance(manifest.get('decks'), list):
        raise ValueError('Invalid companion slide manifest')
    pending = []
    for node in G2_SYLVESTER_NODES:
        matches = [row for row in manifest['decks'] if row.get('lecture_nodes') == [node]]
        if len(matches) != 1:
            raise ValueError(f'{node}: expected exactly one registered deck')
        entry = matches[0]
        if entry.get('source') != entry.get('id', '') + '.json':
            raise ValueError(f'{node}: invalid deck filename')
        path = G2_SYLVESTER_DECK_DIRECTORY / entry['source']
        deck = json.loads(path.read_text(encoding='utf-8'))
        if (deck.get('id') != entry['id'] or deck.get('lecture_nodes') != [node]
                or deck.get('editorial_stage') != 'expanded'
                or len(deck.get('slides', [])) != 10
                or sum(bool(row.get('mathtex')) for row in deck['slides']) < 7):
            raise ValueError(f'{node}: invalid expansion source')
        if entry.get('editorial_stage') == 'baseline':
            entry['editorial_stage'] = 'expanded'
            pending.append(node)
        elif entry.get('editorial_stage') != 'expanded':
            raise ValueError(f'{node}: unsupported editorial stage')
    return manifest_path, manifest, pending


def promote_g2_sylvester_decks(*, write: bool):
    path, manifest, pending = inspect_g2_sylvester_promotion()
    if write and pending:
        handle, tempname = tempfile.mkstemp(dir=path.parent, prefix='.sylvester-manifest-', suffix='.tmp')
        try:
            with os.fdopen(handle, 'w', encoding='utf-8') as stream:
                json.dump(manifest, stream, ensure_ascii=False, indent=2)
                stream.write('\n')
            os.replace(tempname, path)
        finally:
            Path(tempname).unlink(missing_ok=True)
    return pending


def cli_g2_sylvester_promotion():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    pending = promote_g2_sylvester_decks(write=args.write)
    if args.check and pending:
        parser.error('The following entries are still baseline: ' + ', '.join(pending))
    print(f'G2 Sylvester block: {8 - len(pending) if not args.write else 8}/8 expanded; '
          f'{0 if args.write else len(pending)} pending')


if __name__ == '__main__':
    cli_g2_sylvester_promotion()
