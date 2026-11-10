#!/usr/bin/env python3
"""Register the four G2 math-extension companions without replacing the manifest.

The existing deck records, their order, and other agents' metadata are retained.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from tempfile import NamedTemporaryFile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'companion-slides'
ADDITIONS = {
    '091250': 'resolvents-and-yosida-regularization',
    '091500': 'strong-resolvent-convergence-and-spectral-limits',
    '092250': 'hille-yosida-and-contraction-semigroups',
    '099500': 'smoothed-singular-value-energies',
}


def merge_new_g2_companion_records(*, write=False) -> int:
    path = SOURCE / 'manifest.json'
    document = json.loads(path.read_text(encoding='utf8'))
    if document.get('schema_version') != 1 or not isinstance(document.get('decks'), list):
        raise ValueError('Unsupported companion manifest')
    existing_by_id = {row['id']: row for row in document['decks']}
    existing_by_node = {
        node: row for row in document['decks'] for node in row.get('lecture_nodes', [])
    }
    pending = []
    for number, label in ADDITIONS.items():
        deck_id = f'g2-{number}-{label}'
        node = f'g2:{number}'
        source = SOURCE / f'{deck_id}.json'
        if not source.is_file():
            raise FileNotFoundError(source)
        data = json.loads(source.read_text(encoding='utf8'))
        if data.get('id') != deck_id or data.get('lecture_nodes') != [node]:
            raise ValueError(f'Invalid new companion deck: {deck_id}')
        entry = dict(id=deck_id, source=f'{deck_id}.json',
                     lecture_nodes=[node], editorial_stage='baseline')
        previous = existing_by_node.get(node) or existing_by_id.get(deck_id)
        if previous is not None:
            if previous.get('id') != deck_id or previous.get('source') != entry['source'] or previous.get('lecture_nodes') != [node]:
                raise ValueError(f'Conflicting companion metadata for {node}: {previous}')
            continue  # Preserve existing metadata and editorial promotion.
        pending.append(entry)
    if write and pending:
        document['decks'].extend(pending)
        with NamedTemporaryFile('w', encoding='utf8', dir=SOURCE,
                                prefix='.manifest-merge-', delete=False) as stream:
            temp = Path(stream.name)
            json.dump(document, stream, ensure_ascii=False, indent=2)
            stream.write('\n')
        temp.replace(path)
    print(f'{len(pending)} new companion manifest records ' + ('installed' if write else 'pending'))
    return len(pending)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args(argv)
    pending = merge_new_g2_companion_records(write=args.write)
    if args.check and pending:
        raise SystemExit(f'{pending} companion decks require registration')


if __name__ == '__main__':
    main()
