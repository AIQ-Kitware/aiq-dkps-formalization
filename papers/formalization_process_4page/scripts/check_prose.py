#!/usr/bin/env python3
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
paths = [root / 'paper.tex']
patterns = {
    'banned word matters': r'\bmatters\b',
    'banned word silently': r'\bsilently\b',
    'banned word quietly': r'\bquietly\b',
    'banned word unusually': r'\bunusually\b',
    'repo phrase source-faithful': r'source-faithful',
    'repo phrase project-local': r'project-local',
    'stock contrast not-X-but-Y': r'\bnot\b[^.\n]{0,100}\bbut\b',
}
failed = False
for path in paths:
    text = path.read_text(encoding='utf8')
    for name, pat in patterns.items():
        for m in re.finditer(pat, text, flags=re.I):
            line = text.count('\n', 0, m.start()) + 1
            print(f'{path.name}:{line}: {name}: {m.group(0)!r}')
            failed = True
if failed:
    raise SystemExit(1)
print('prose checks passed')
