"""Curated learning companions, shared by the library and portable exports."""
from __future__ import annotations

import argparse
from html import escape
from pathlib import Path
from urllib.parse import urlsplit

import yaml

from dkvis.decks import DECKS, get_deck
from dkvis.lectures import lecture_output_name
from dkvis.presentation.paths import ROOT


def learning_resources(deck):
    spec = get_deck(deck)
    if spec.learning_resources:
        source = ROOT / spec.learning_resources
    elif spec.narration:
        source = (ROOT / spec.narration).with_name('resources.yaml')
    else:
        return None
    if not source.is_file():
        if spec.learning_resources:
            raise FileNotFoundError(source)
        return None
    data = yaml.safe_load(source.read_text())
    if not isinstance(data, dict) or not isinstance(data.get('resources'), list):
        raise ValueError(f'{source}: expected a resources list')
    for row in data['resources']:
        for field in ('title', 'url', 'kind', 'why'):
            if not isinstance(row.get(field), str) or not row[field].strip():
                raise ValueError(f'{source}: missing resource {field}')
        url = urlsplit(row['url'])
        if url.scheme not in ('https', 'http') or not url.netloc:
            raise ValueError(f'{source}: learning links must use HTTP or HTTPS')
    return data


def companion_html(data):
    items = []
    for row in data['resources']:
        focus = f'<p class="focus">Focus: {escape(row["focus"])}</p>' if row.get('focus') else ''
        items.append(f'<li><h2><a href="{escape(row["url"], quote=True)}" '
                     f'target="_blank" rel="noopener noreferrer">{escape(row["title"])}</a></h2>'
                     f'<p class="kind">{escape(row["kind"])}</p><p>{escape(row["why"])}</p>{focus}</li>')
    title = escape(data['title'])
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Learn more — {title}</title><style>
body{{font:18px/1.6 system-ui,sans-serif;max-width:820px;margin:3rem auto;padding:0 1.5rem;color:#17202b;background:#fafbf9}}
h1{{font-size:1.8rem;line-height:1.3}}h2{{font-size:1.1rem;margin-bottom:.1rem}}a{{color:#15599b}}
li{{padding:.8rem 0}}p{{margin:.3rem 0}}.kind,footer{{font-size:.85rem;color:#526071}}.focus{{font-size:.95rem}}
@media print{{a{{color:inherit}}li{{break-inside:avoid}}}}
</style></head><body><h1>Learn more: {title}</h1><p>{escape(data.get('intro', ''))}</p>
<ol>{''.join(items)}</ol><footer>Links reviewed {escape(str(data.get('checked_on', 'not recorded')))}.</footer>
</body></html>'''


def companion_markdown(data):
    lines = [f'# Learn more: {data["title"]}', '', data.get('intro', ''), '']
    for i, row in enumerate(data['resources'], 1):
        lines.extend([f'{i}. [{row["title"]}]({row["url"]}) — {row["kind"]}',
                      f'   {row["why"]}'])
        if row.get('focus'):
            lines.append(f'   Focus: {row["focus"]}')
        lines.append('')
    lines.append(f'Links reviewed {data.get("checked_on", "not recorded")}.')
    return '\n'.join(lines) + '\n'


def export_resources(out, *, deck_name):
    data = learning_resources(deck_name)
    if data is None:
        return []
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    from dkvis.presentation.provenance import record
    paths = []
    for suffix, content in [('html', companion_html(data)), ('md', companion_markdown(data))]:
        path = out / f'{lecture_output_name(deck_name)}.learn-more.{suffix}'
        if not path.is_file() or path.read_text() != content:
            path.write_text(content)
            record(path, deck_name, 'learning-resources', checked_on=str(data.get('checked_on')),
                   curated_by=data.get('curated_by'))
        paths.append(path)
    return paths


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--deck', choices=sorted(DECKS), help='Omit to export all companions.')
    parser.add_argument('--out', type=Path, default=ROOT / 'renders')
    args = parser.parse_args(argv)
    decks = [args.deck] if args.deck else DECKS
    paths = [p for deck in decks for p in export_resources(args.out, deck_name=deck)]
    print(f'Exported {len(paths)} learning companion files to {args.out}')


if __name__ == '__main__':
    main()
