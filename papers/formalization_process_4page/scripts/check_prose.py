#!/usr/bin/env python3
from pathlib import Path

paths = [
    Path('paper.tex'),
    Path('related_work_condensed.tex'),
    Path('related_work_semantic_alignment.tex'),
]
text = ' ' + '\n'.join(p.read_text().lower() for p in paths if p.exists()) + ' '
banned = [
    ' matters ',
    ' silently ',
    ' quietly ',
    ' unusually ',
    'source-faithful',
    'project-local',
]
found = [x.strip() for x in banned if x in text]
if found:
    raise SystemExit('banned prose tokens: ' + ', '.join(found))
print('basic prose check: PASS')
