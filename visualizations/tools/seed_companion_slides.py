#!/usr/bin/env python3
"""Create first-pass G2 companion decks from existing spoken mathematical lectures.

This is a one-time bootstrap / optional maintenance tool, not an editorial
replacement. Never overwrites an authored slide deck. Baseline decks must be
individually expanded with proof diagrams, additional examples and vector math.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ROOT / 'draft-stages' / 'tts-lectures'
DEST = ROOT / 'companion-slides'
SENTENCE = re.compile(r'(?<=[.!?])\s+(?=[A-Z“"(])')
HEADINGS = re.compile(r'(?m)^## (.+?)\s*$')
DISPLAY_TEX = re.compile(r'\\\[(.*?)\\\]', re.S)


def readable(text: str) -> str:
    """Remove formatting, while leaving the mathematical content in the text."""
    text = re.sub(r'(?m)^>\s?', '', text)
    text = re.sub(r'\*\*(.*?)\*\*', r'\1', text)
    text = re.sub(r'(?<!\w)\*(.*?)\*(?!\w)', r'\1', text)
    text = re.sub(r'`([^`]+)`', r'\1', text)
    text = re.sub(r'\[([^\]]+)\]\([^)]*\)', r'\1', text)
    return re.sub(r'\s+', ' ', text).strip()


def sentences(text: str) -> list[str]:
    return [s.strip() for s in SENTENCE.split(readable(text)) if s.strip()]


def passage(text: str, max_chars: int = 580) -> tuple[str, list[str]]:
    """Read from the start to a complete sentence boundary, not mid-sentence."""
    chunks = sentences(text)
    if not chunks:
        return '', []
    lead = chunks[0]
    kept = []
    for item in chunks[1:]:
        if len(' '.join([lead, *kept, item])) > max_chars and kept:
            break
        kept.append(item)
        if len(' '.join([lead, *kept])) >= max_chars:
            break
    return lead, [' '.join(kept)] if kept else []


def spoken_sections(path: Path) -> list[tuple[str, str]]:
    source = path.read_text(encoding='utf-8')
    begin, end = '<!-- BEGIN SPOKEN LECTURE -->', '<!-- END SPOKEN LECTURE -->'
    if begin not in source or end not in source:
        raise ValueError(f'No complete spoken markers: {path}')
    spoken = source.split(begin, 1)[1].split(end, 1)[0].strip()
    # Some lectures introduce their own spoken title as a level-one heading.
    spoken = re.sub(r'(?m)^# [^\n]*\n', '', spoken).strip()
    bits = HEADINGS.split(spoken)
    result = [('The problem and its setting', bits[0].strip())]
    result.extend((bits[i], bits[i + 1].strip()) for i in range(1, len(bits), 2))
    return [(title, text) for title, text in result if readable(text)]


def appendix_formula(path: Path) -> str | None:
    text = path.read_text(encoding='utf-8')
    appendix = text.split('<!-- END SPOKEN LECTURE -->', 1)[1]
    # Exclude code blocks and Lean excerpts to avoid interpreting their strings as math.
    appendix = re.split(r'(?m)^```|^### Actual Lean|^\*\*Lean bridge', appendix, maxsplit=1)[0]
    for match in DISPLAY_TEX.finditer(appendix):
        tex = match.group(1).strip()
        if (20 <= len(tex) <= 130 and '\\tag' not in tex
                and '\\label' not in tex and '\\begin{' not in tex
                and not '\\end{' in tex):
            return tex
    return None


def name_for(path: Path) -> str:
    raw = 'g2-' + path.stem
    return raw if len(raw) <= 63 else raw[:63].rstrip('-')


def baseline_deck(path: Path) -> dict:
    title = path.read_text(encoding='utf8').splitlines()[0].lstrip('#').strip()
    title = re.sub(r'^\d{6}\s*[—–-]\s*', '', title)
    ident = path.stem[:6]
    deck_id = name_for(path)
    sections = spoken_sections(path)
    pages = []
    for idx, (heading, content) in enumerate(sections):
        lead, body = passage(content, 630 if idx == 0 else 700)
        if not lead:
            continue
        # Editorial expansion can later separate and complete the proofs; in
        # the baseline, section titles + source excerpts form a readable map.
        if len(lead) > 310:
            body.insert(0, lead)
            lead = f'{heading} is the next step of the argument.'
        pages.append(dict(id=f'{idx:02d}-overview', title=heading,
                          eyebrow=f'G2 · {ident} · first-pass outline', lead=lead,
                          body=body, layout='opening' if idx == 0 else 'reading'))
    tex = appendix_formula(path)
    if tex:
        # Keep the symbolic statement together with a short passage of spoken
        # context; the seed never claims to provide a complete proof.
        context, context_body = passage(sections[-1][1], 350)
        # One exact formula from the display-only mathematics appendix. No
        # invented theorem or arbitrary algebraic rearrangement is introduced.
        pages.append(dict(id='reference-equation', title='The mathematical relationship',
                          eyebrow=f'G2 · {ident} · mathematical reference',
                          lead=context or 'The mathematical relationship can be expressed in symbols.',
                          body=context_body or ['This identity encodes the relationships under discussion.'],
                          mathtex=tex, layout='equation'))
    final = readable(sections[-1][1])
    last = sentences(final)[-1]
    if last and len(last) < 420:
        pages.append(dict(id='closing-perspective',title='What to retain',
                          eyebrow=f'G2 · {ident} · conclusion',
                          lead=last, body=[],layout='reading'))
    if not 3 <= len(pages) <= 100:
        raise ValueError(f'Unexpected slide count {len(pages)} for {path.name}')
    return dict(schema_version=1, id=deck_id, title=title,
                subtitle=f'G2 lecture {ident} · baseline companion · needs expansion',
                editorial_stage='baseline', lecture_nodes=[f'g2:{ident}'],
                source_lecture=f'draft-stages/tts-lectures/{path.name}',
                adaptation=('First-pass source-derived outline. Section excerpts and any vector equation '
                            'come from the spoken lecture and its display-only mathematics appendix. '
                            'Expand with worked mathematics, proofs and topic-specific diagrams.'),
                slides=pages)


def seed(sources: Path = SOURCES, dest: Path = DEST, *, write=False):
    manifest = json.loads((dest / 'manifest.json').read_text(encoding='utf8'))
    entries = manifest['decks']
    existing = {node for row in entries for node in row['lecture_nodes']}
    added=[]
    for path in sorted(sources.glob('[0-9]' * 6 + '-*.md')):
        node = f'g2:{path.name[:6]}'
        if node in existing:
            continue
        data = baseline_deck(path)
        file = dest / f'{data["id"]}.json'
        if file.exists():
            raise ValueError(f'Would overwrite unregistered deck {file}')
        added.append((file, data))
        entries.append(dict(id=data['id'], source=file.name,
                            lecture_nodes=[node],editorial_stage='baseline'))
    for row in entries:
        # Existing authored companions were reviewed/expanded in earlier batches.
        row.setdefault('editorial_stage','expanded')
    if write:
        for file, data in added:
            file.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n',encoding='utf8')
        (dest / 'manifest.json').write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n',encoding='utf8')
    return [data for _, data in added]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='Write only missing decks and update the manifest')
    args = parser.parse_args()
    added = seed(write=args.write)
    print(f'{len(added)} missing G2 decks ' + ('written' if args.write else 'would be written'))
    for data in added[:5]:print(' ',data['id'],len(data['slides']),'slides')


if __name__ == '__main__':
    main()
