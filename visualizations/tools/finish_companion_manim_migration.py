#!/usr/bin/env python3
"""Finish Manim migration without removing local diagram files from disk.

Git tracks exports from the old pipeline, despite the existing ignore rule.
This script stops tracking those exports and removes the obsolete Python module
if it is unchanged since the reviewed snapshot. Other changes are preserved.

Run from any directory:
  python visualizations/tools/finish_companion_manim_migration.py --write
  python visualizations/tools/finish_companion_manim_migration.py --check
"""
from __future__ import annotations

import argparse
import hashlib
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEGACY_MODULE = 'visualizations/dkvis/presentation/companion_figures.py'
# Prevent deletion of other agents' revisions to the old Python module.
EXPECTED_MODULE_SHA256 = 'c8dfecca2d6b0aeac39f36fad539ed2db718a8913813e36c2ea312c2d200ab91'
SVG_PREFIX = 'visualizations/companion-slides/figures/'


def git_output(*args):
    process = subprocess.run(['git', '-c', f'safe.directory={ROOT}', *args], cwd=ROOT, check=True,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return process.stdout


def tracked_svg_files():
    raw = git_output('ls-files', '-z', '--', SVG_PREFIX + '*.svg')
    return [name.decode('utf8') for name in raw.split(b'\0') if name]


def legacy_module_is_tracked():
    return bool(git_output('ls-files', '--', LEGACY_MODULE).strip())


def finish_companion_manim_migration(*, write=False):
    exports = tracked_svg_files()
    obsolete = legacy_module_is_tracked()
    print(f'Tracked generated SVGs: {len(exports)}')
    print(f'Legacy figure module: {"tracked" if obsolete else "already untracked"}')
    if not write:
        if exports or obsolete:
            raise SystemExit('Migration cleanup incomplete. Re-run with --write.')
        return
    if exports:
        # --cached removes only the index entries: the local generated files remain.
        subprocess.run(['git', '-c', f'safe.directory={ROOT}', 'rm', '--cached', '--', *exports], cwd=ROOT, check=True)
    if obsolete:
        old_path = ROOT / LEGACY_MODULE
        digest = hashlib.sha256(old_path.read_bytes()).hexdigest() if old_path.is_file() else None
        if digest == EXPECTED_MODULE_SHA256:
            subprocess.run(['git', '-c', f'safe.directory={ROOT}', 'rm', '--', LEGACY_MODULE], cwd=ROOT, check=True)
        else:
            print('Preserved modified legacy figure module; review it before untracking.')
    print('Migration cleanup complete (SVG files preserved locally).')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--check', action='store_true')
    group.add_argument('--write', action='store_true')
    args = parser.parse_args(argv)
    finish_companion_manim_migration(write=args.write)


if __name__ == '__main__':
    main()
