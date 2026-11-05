"""Order lecture folders from YAML prerequisites.

    uv run python -m dkvis.lectures                  # preview, no writes
    uv run python -m dkvis.lectures --apply          # preserve existing numbers
    uv run python -m dkvis.lectures --rebalance --apply  # 001000, 002000, ...

Deck IDs and Python packages never depend on ordering numbers.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
from pathlib import Path
import re

import networkx as nx
import yaml

from dkvis.presentation.paths import ROOT

LECTURES = ROOT / 'lectures'


@lru_cache
def load_index(path=LECTURES/'index.yaml'):
    rows = yaml.safe_load(Path(path).read_text())['lectures']
    graph = nx.DiGraph()
    graph.add_nodes_from(rows)
    decks = set()
    for key, row in rows.items():
        if not re.fullmatch(r'[a-z][a-z0-9_]*', key):
            raise ValueError(f'Invalid lecture ID: {key}')
        if row['deck'] in decks:
            raise ValueError(f'Duplicate deck ID: {row["deck"]}')
        decks.add(row['deck'])
        for parent in row.get('requires', []):
            if parent not in rows:
                raise ValueError(f'{key}: unknown prerequisite {parent}')
            graph.add_edge(parent, key)
    preference = {key: i for i, key in enumerate(rows)}
    try:
        order = list(nx.lexicographical_topological_sort(graph, key=preference.get))
    except nx.NetworkXUnfeasible as error:
        raise ValueError(f'Prerequisite cycle: {nx.find_cycle(graph)}') from error
    return {key: rows[key] for key in order}


def find_folder(key, root=LECTURES):
    candidates = list(root.glob(f'[0-9][0-9][0-9][0-9][0-9][0-9]_{key}'))
    if (root/key).is_dir():
        candidates.append(root/key)
    if len(candidates) > 1:
        raise ValueError(f'Multiple folders for {key}: {candidates}')
    return candidates[0] if candidates else None


def lecture_path(key):
    if key not in load_index():
        raise KeyError(f'Unknown lecture: {key}')
    folder = find_folder(key)
    if folder is None:
        raise ValueError(f'No folder for {key}; run python -m dkvis.lectures --apply')
    return str((folder/'lecture.md').relative_to(ROOT))


def lecture_decks(series=None):
    return [row['deck'] for row in load_index().values()
            if series is None or row.get('series') == series]


def lecture_number(deck):
    """The organizer owns numbers; public artifacts inherit the current folder key."""
    for key, row in load_index().items():
        if row['deck'] == deck:
            folder = find_folder(key, LECTURES)
            if folder and re.match(r'^\d{6}_', folder.name):
                return folder.name[:6]
    return None


def lecture_output_name(deck):
    number = lecture_number(deck)
    return f'{number}_{deck}' if number else deck


def number_outputs(rows, renders):
    """Rename public exports in place; retain stable scene and speech caches."""
    if not renders.exists():
        return
    for row in rows.values():
        deck = row['deck']
        public = lecture_output_name(deck)
        for source in list(renders.iterdir()):
            # Names already carrying an earlier order key can also be rebalanced.
            bare = re.sub(r'^\d{6}_', '', source.name)
            if not (bare.startswith(deck+'.') or bare.startswith(deck+'-light.')):
                continue
            if source.suffix.lower() not in {'.mp4', '.html', '.pdf', '.pptx'} or not source.is_file():
                continue
            target = renders/(public+bare[len(deck):])
            if source == target:
                continue
            if target.exists():
                print(f'keep both: {source.name} (destination {target.name} already exists)')
                continue
            source.rename(target)
            sidecar=source.with_name(source.name+'.metadata.json')
            destination=target.with_name(target.name+'.metadata.json')
            if sidecar.is_file() and not destination.exists():
                sidecar.rename(destination)
            print(f'export {source.name} -> {target.name}')


def plan(rows, root=LECTURES, rebalance=False):
    keys = list(rows)
    sources = {key: find_folder(key, root) for key in keys}
    numbers = {}
    for i, key in enumerate(keys):
        folder = sources[key]
        if folder and re.match(r'^\d{6}_', folder.name):
            numbers[i] = int(folder.name[:6])
    if rebalance or not numbers:
        assigned = {i: (i+1)*1000 for i in range(len(keys))}
    else:
        assigned = dict(numbers)
        previous_index, previous_number = -1, 0
        for index, number in sorted(numbers.items()):
            slots = index-previous_index
            if number-previous_number < slots:
                raise ValueError('Existing order conflicts or a gap is exhausted; preview with --rebalance.')
            for offset in range(1, slots):
                assigned[previous_index+offset] = previous_number+(number-previous_number)*offset//slots
            previous_index, previous_number = index, number
        for i in range(previous_index+1, len(keys)):
            assigned[i] = previous_number+1000*(i-previous_index)
    if any(not 0 < n <= 999999 for n in assigned.values()):
        raise ValueError('Six-digit numbering range exhausted.')
    result = [(key, sources[key], root/f'{assigned[i]:06d}_{key}') for i, key in enumerate(keys)]
    for key, source, target in result:
        if target.exists() and target != source:
            raise ValueError(f'Refusing to overwrite {target}')
    return result


def write_catalog(rows, root):
    lines = ['# Lecture library', '',
             'Edit `index.yaml` to add lectures and their prerequisite IDs. YAML order breaks ties',
             'between otherwise independent lessons. Python uses NetworkX to sort the graph.', '',
             'Preview with `uv run python -m dkvis.lectures`; apply with `--apply`.',
             'Existing numbers stay fixed when possible; new lectures receive numbers in gaps.',
             'Use `--rebalance --apply` to regenerate 001000, 002000, 003000, ... when needed.', '',
             'An unnumbered folder named after its stable ID can hold a new `lecture.md` before',
             'organization. Alternatively, applying the plan creates its numbered folder.',
             'Decks resolve transcripts by stable ID, so renaming folders needs no import edits.',
             'Deck IDs, audio caches and Python package names stay stable. Public video, HTML and',
             'PDF exports inherit the six-digit lecture number; --apply also renames existing exports.', '',
             'This catalog is regenerated by the organizer; edit the YAML and lesson text.', '']
    for key, row in rows.items():
        folder = find_folder(key, root)
        number = folder.name.split('_', 1)[0]
        parents = ', '.join(f'[{p}](#{p})' for p in row.get('requires', [])) or 'Basic vectors and matrices'
        lines += [f'<a id="{key}"></a>', f'## {number} — {row["title"]}', '',
                  f'Prerequisites: {parents}.', '',
                  f'[Transcript]({folder.name}/lecture.md) · '
                  f'[Slides](../renders/{number}_{row["deck"]}.standalone.html) · '
                  f'[Handout](../renders/{number}_{row["deck"]}.handout.pdf)', '',
                  f'Build: `make slides DECK={row["deck"]}`. Folder: `{folder.name}/`.', '']
        overview = folder/'README.md'
        if not overview.exists():
            text = [f'# {row["title"]}', '',
                    f'[Transcript](lecture.md) · [Library and prerequisites](../README.md#{key})', '']
            if row.get('topic'):
                text += [f'[Topic guide, mathematical sources and code](../../dkvis/learning/{row["topic"]}/README.md)', '']
            text += [f'Build: `make slides DECK={row["deck"]}` from `visualizations/`.', '']
            overview.write_text('\n'.join(text))
    (root/'README.md').write_text('\n'.join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--apply', action='store_true')
    parser.add_argument('--rebalance', action='store_true')
    parser.add_argument('--root', type=Path, default=LECTURES, help='lecture directory containing index.yaml')
    args = parser.parse_args()
    try:
        rows = load_index(args.root/'index.yaml')
        changes = plan(rows, args.root, args.rebalance)
        for key, source, target in changes:
            state = 'keep' if source == target else ('move' if source else 'create')
            print(f'{state:6s} {source.name if source else key} -> {target.name}')
        if args.apply:
            for key, source, target in changes:
                if source is None:
                    target.mkdir(parents=True)
                elif source != target:
                    source.rename(target)
            if args.root.resolve() == LECTURES.resolve():
                number_outputs(rows, ROOT/'renders')
            write_catalog(rows, args.root)
        else:
            print('Preview only; pass --apply to organize folders and refresh the catalog.')
    except (ValueError, KeyError, yaml.YAMLError) as error:
        parser.error(str(error))


if __name__ == '__main__':
    main()
