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
    'banned worth phrasing': r'\bworth\b',
    'repo phrase source-faithful': r'source-faithful',
    'repo phrase project-local': r'project-local',
    'internal census jargon': r'\bcensus\b',
    'internal inventory jargon': r'\binventory\b',
    'internal reopening jargon': r'\breopen(?:ed|ing|s)?\b',
    'terminal-status jargon': r'terminal status',
    'stock contrast not-X-but-Y': r'\bnot\b[^.\n]{0,100}\bbut\b',
    'stock kernel phrase': r'the kernel has done its job',
    'belittles doohickey example': r'intentionally silly|deliberately silly',
    'paired theorem overclaim phrasing': r'the lean theorem above was valid|the overclaim was',
    'unsupported proof bottleneck claim': r'proof production stopped being the main bottleneck',
    'slogan section title too narrow': r'a checked theorem that was still too narrow',
    'rhetorical theorem heading': r'what is the theorem about\?',
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
