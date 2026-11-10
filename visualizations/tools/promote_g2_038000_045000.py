#!/usr/bin/env python3
"""Promote the authored G2 038000–045000 slide decks without replacing manifest rows.

Usage (from repository root):
    python3 visualizations/tools/promote_g2_038000_045000.py --write
    python3 visualizations/tools/promote_g2_038000_045000.py --check

This edits only the specified editorial_stage values; other agents' decks,
lecture associations, additional fields, and ordering remain unchanged.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import tempfile

COMPANION_DIR = Path(__file__).resolve().parents[1] / 'companion-slides'
PROMOTED_NODES = tuple(f'g2:{n:03}000' for n in range(38, 46))


def inspect_g2_038000_045000_promotion() -> tuple[Path, dict, list[str]]:
    path = COMPANION_DIR / 'manifest.json'
    manifest = json.loads(path.read_text(encoding='utf8'))
    if manifest.get('schema_version') != 1 or not isinstance(manifest.get('decks'), list):
        raise ValueError('Invalid companion deck manifest')
    changed = []
    for node in PROMOTED_NODES:
        matches = [row for row in manifest['decks'] if row.get('lecture_nodes') == [node]]
        if len(matches) != 1:
            raise ValueError(f'Expected one companion deck for {node}; found {len(matches)}')
        row = matches[0]
        deck_file = COMPANION_DIR / row['source']
        deck = json.loads(deck_file.read_text(encoding='utf8'))
        if (deck.get('id') != row['id'] or deck.get('lecture_nodes') != [node]
                or deck.get('editorial_stage') != 'expanded' or len(deck.get('slides', [])) < 9):
            raise ValueError(f'Authored deck is missing or inconsistent: {node}')
        if row.get('editorial_stage') != 'expanded':
            if row.get('editorial_stage') != 'baseline':
                raise ValueError(f'Unexpected existing stage for {node}')
            row['editorial_stage'] = 'expanded'
            changed.append(node)
    return path, manifest, changed


def promote_g2_038000_045000_manifest(write: bool) -> list[str]:
    path, manifest, changed = inspect_g2_038000_045000_promotion()
    if write and changed:
        # Atomic replacement avoids leaving a truncated manifest on interruption.
        fd, name = tempfile.mkstemp(prefix='.manifest-g2-', suffix='.tmp', dir=path.parent)
        try:
            with os.fdopen(fd, 'w', encoding='utf8') as stream:
                json.dump(manifest, stream, indent=2, ensure_ascii=False)
                stream.write('\n')
            os.replace(name, path)
        finally:
            Path(name).unlink(missing_ok=True)
    return changed


def cli_promote_g2_038000_045000() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true', help='Mark the eight authored decks expanded')
    mode.add_argument('--check', action='store_true', help='Verify promotion is already complete')
    args = parser.parse_args()
    changed = promote_g2_038000_045000_manifest(args.write)
    if args.check and changed:
        parser.error('Not promoted: ' + ', '.join(changed) + '; use --write')
    print(f'G2 038000–045000: {8-len(changed)}/8 already promoted; '
          + (f'{len(changed)} promoted' if args.write else 'all verified'))


if __name__ == '__main__':
    cli_promote_g2_038000_045000()
