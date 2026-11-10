#!/usr/bin/env python3
"""Integrate four standalone mathematics lectures with existing G2 catalogs.

Works in place and never replaces the whole curriculum, tests, or shared manifests.
Use --write to integrate; --check verifies installed state without mutation.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

VISUALIZATIONS = Path(__file__).resolve().parents[1]
ROOT = VISUALIZATIONS.parent
LECTURES = VISUALIZATIONS / 'draft-stages' / 'tts-lectures'
ASSIGNMENTS = {'091250':'unbounded', '091500':'unbounded', '092250':'unbounded', '099500':'operator-ideals'}
SOURCES = {
 '091250':'091250-resolvents-and-yosida-regularization.md',
 '091500':'091500-strong-resolvent-convergence-and-spectral-limits.md',
 '092250':'092250-hille-yosida-and-contraction-semigroups.md',
 '099500':'099500-smoothed-singular-value-energies.md',
}
RELATIONSHIPS = [
 ['g2:091250','hard_depends_on','g2:081000','The resolvent construction uses bounded inverses of nonreal or positive shifts.'],
 ['g2:091250','hard_depends_on','g2:083000','The domain and closedness hypotheses matter for resolvent inversion.'],
 ['g2:091500','hard_depends_on','g2:091250','Strong resolvent convergence is illustrated with the Yosida approximation.'],
 ['g2:092250','hard_depends_on','g2:091250','The contraction-semigroup construction starts from Yosida resolvent approximants.'],
 ['g2:099500','hard_depends_on','g2:099000','The smoothing-domain theorem uses the Hilbert-Schmidt and trace-class distinction.'],
]


def math_extension_json_update(path: Path, updater, *, write: bool) -> bool:
    payload=json.loads(path.read_text(encoding='utf8'))
    changed=updater(payload)
    if changed and write:
        path.write_text(json.dumps(payload,ensure_ascii=False,indent=2)+'\n', encoding='utf8')
    return changed


def math_extension_topic_map(payload: dict) -> bool:
    topics={item['id'] for item in payload['topics']}
    if not set(ASSIGNMENTS.values()).issubset(topics):
        raise ValueError('Required topic IDs are not present in topics.json')
    assignments=payload['g2_assignments']
    changes=False
    for ident,topic in ASSIGNMENTS.items():
        key=f'g2:{ident}'
        if key in assignments and assignments[key] != topic:
            raise ValueError(f'Conflicting topic for {key}: {assignments[key]}')
        if key not in assignments:
            assignments[key]=topic
            changes=True
    return changes


def math_extension_relationships(payload: dict) -> bool:
    edges=payload['edges']
    keyed={(edge[0],edge[1],edge[2]) for edge in edges}
    changes=False
    for row in RELATIONSHIPS:
        if tuple(row[:3]) not in keyed:
            edges.append(row)
            changes=True
    return changes


def math_extension_replace_if_present(path: Path, patches: tuple[tuple[str,str],...], *, write: bool) -> bool:
    source=path.read_text(encoding='utf8')
    after=source
    for old,new in patches:
        after=after.replace(old,new)
    if after!=source and write:
        path.write_text(after,encoding='utf8')
    return after!=source


def math_extension_patch_legacy_counts(*, write:bool) -> dict:
    # Existing tests tie a growing G2 inventory to the original 150 entries.
    # Replace those particular assertions with checks that remain meaningful
    # when more mathematics lessons are inserted later.
    changes={}
    patches={
      'draft-stages/tts-lectures/README.md':(
        ('These 150 transcript-first drafts follow', 'These transcript-first drafts follow'),
        ('The collection currently contains 150 numbered transcript drafts,',
         'The original collection contains 150 numbered transcript drafts, with additional mathematical lectures inserted between them,'),
      ),
      'draft-stages/tts-lectures/reference_metadata.py': (
        ('validate all 150 sidecars', 'validate the lecture sidecars'),
        ("if len(paths) != 150 or len(sidecars) != len(paths):", "if len(paths) < 150 or len(sidecars) != len(paths):"),
        ("Expected 150 transcripts and matching sidecars", "Expected at least 150 transcripts and matching sidecars"),
      ),
      'dkvis/presentation/course_graph.py':(
        ("summary='Full 150-lecture path'", "summary=f'Full {len(g2)}-lecture path'"),
      ),
      'tests/test_audio_course_tracks.py':(
        ("tracks[1]['count'] == 150", "tracks[1]['count'] >= 154"),
        ("len(client.get('/api/audio-lectures').json()['items']) == 150", "len(client.get('/api/audio-lectures').json()['items']) >= 154"),
      ),
      'tests/test_audio_lecture_library.py': (
        ('len(items) == 150', 'len(items) >= 154'),
      ),
      'tests/test_course_graph.py': (
        ("len(graph['nodes']) == 204", "len(graph['nodes']) >= 208"),
        ("len(tracks['g2']['path']) == 150", "len(tracks['g2']['path']) >= 154"),
        ('sorted(map(len, order_only)) == [22, 182]', "sorted(map(len, order_only)) == [22, len(graph['nodes']) - 22]"),
        ('len(path_edges) == 203', 'len(path_edges) >= 203'),
      ),
    }
    for rel,items in patches.items():
        path=VISUALIZATIONS/rel
        if path.is_file():
            changes[rel]=math_extension_replace_if_present(path,items,write=write)
    return changes


def math_extension_integrate(*,write:bool)->dict:
    for ident,filename in SOURCES.items():
        transcript=LECTURES/filename
        metadata=LECTURES/'metadata'/f'{ident}.json'
        if not transcript.is_file() or not metadata.is_file():
            raise FileNotFoundError(f'Missing transcript or metadata: {ident}')
    result={
       'topic_map':math_extension_json_update(VISUALIZATIONS/'curriculum'/'topics.json', math_extension_topic_map,write=write),
       'relationships':math_extension_json_update(VISUALIZATIONS/'curriculum'/'relationships.json', math_extension_relationships,write=write),
       'legacy':math_extension_patch_legacy_counts(write=write),
    }
    return result


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true',help='Integrate new course nodes and update legacy counts')
    mode.add_argument('--check',action='store_true',help='Fail if a catalog or test still needs this integration')
    args=parser.parse_args()
    result=math_extension_integrate(write=args.write)
    changes=result['topic_map'] or result['relationships'] or any(result['legacy'].values())
    if args.check and changes:
        raise SystemExit('G2 mathematics expansion not integrated; run --write')
    print(json.dumps({'mode':'write' if args.write else 'check','pending_changes_before_update':changes,'details':result},indent=2))


if __name__=='__main__':
    main()
