#!/usr/bin/env python3
"""Promote G2 046000–053000 companion decks without clobbering the manifest.

Run after extracting the deck sources:
    python3 visualizations/tools/promote_g2_046000_053000.py --write
    python3 visualizations/tools/promote_g2_046000_053000.py --check
"""
from __future__ import annotations
import argparse
import json
import os
import tempfile
from pathlib import Path

BATCH3_DECK_DIR = Path(__file__).resolve().parents[1] / 'companion-slides'
BATCH3_NODES = tuple(f'g2:{n:03d}000' for n in range(46,54))


def inspect_g2_046000_053000_manifest():
    path=BATCH3_DECK_DIR/'manifest.json'
    data=json.loads(path.read_text(encoding='utf8'))
    if data.get('schema_version') != 1 or not isinstance(data.get('decks'),list):
        raise ValueError('Invalid companion deck manifest')
    pending=[]
    for node in BATCH3_NODES:
        matches=[row for row in data['decks'] if row.get('lecture_nodes')==[node]]
        if len(matches)!=1:raise ValueError(f'Expected one companion deck at {node}; found {len(matches)}')
        entry=matches[0]
        deck=json.loads((BATCH3_DECK_DIR/entry['source']).read_text(encoding='utf8'))
        if (deck.get('id')!=entry.get('id') or deck.get('lecture_nodes')!=[node]
                or deck.get('editorial_stage')!='expanded' or len(deck.get('slides',[]))<9):
            raise ValueError(f'Expected expanded source for {node}')
        if entry.get('editorial_stage')=='baseline':
            entry['editorial_stage']='expanded';pending.append(node)
        elif entry.get('editorial_stage')!='expanded':
            raise ValueError(f'Unexpected editorial stage at {node}')
    return path,data,pending


def promote_g2_046000_053000_manifest(*,write):
    path,data,pending=inspect_g2_046000_053000_manifest()
    if write and pending:
        fd,tmp=tempfile.mkstemp(prefix='.manifest-g2batch3-',suffix='.tmp',dir=path.parent)
        try:
            with os.fdopen(fd,'w',encoding='utf8') as stream:
                json.dump(data,stream,indent=2,ensure_ascii=False);stream.write('\n')
            os.replace(tmp,path)
        finally:Path(tmp).unlink(missing_ok=True)
    return pending


def cli_promote_g2_046000_053000():
    parser=argparse.ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args=parser.parse_args()
    pending=promote_g2_046000_053000_manifest(write=args.write)
    if args.check and pending:parser.error('Not promoted: '+', '.join(pending))
    print(f'G2 046000–053000: {8-len(pending)}/8 already promoted; {len(pending)} pending or promoted')


if __name__=='__main__':cli_promote_g2_046000_053000()
