"""Shared lecture graph: identities, named paths and typed conceptual edges.

A path is a sequence of existing nodes, not a copy of their transcripts.
Original-parent edges record provenance; they are never prerequisites.
"""
from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from urllib.parse import quote

from dkvis.presentation.paths import ROOT
from dkvis.presentation.audio_library import SOURCE_DIRECTORY, PAPER_DIRECTORY

GRAPH_DIRECTORY = ROOT / 'curriculum'
RELATION_TYPES = frozenset({
    'hard_depends_on', 'soft_depends_on', 'expands_on', 'original_parent',
    'alternative_presentation', 'related_to',
})


def _read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def _title_from_file(path):
    first = path.read_text(encoding='utf-8').splitlines()[0]
    return first[2:].strip() if first.startswith('# ') else path.stem.replace('-', ' ').title()


def _check_acyclic(edges, relation):
    dependencies = defaultdict(list)
    for edge in edges:
        if edge['type'] == relation:
            dependencies[edge['from']].append(edge['to'])
    colors = {}

    def visit(node):
        if colors.get(node) == 1:
            raise ValueError(f'{relation} cycle involves {node}')
        if colors.get(node) == 2:
            return
        colors[node] = 1
        for needed in dependencies[node]:
            visit(needed)
        colors[node] = 2

    for node in list(dependencies):
        visit(node)


def build_course_graph(*, g1_directory=None, g2_directory=None, g3_directory=None,
                       graph_directory=None):
    """Build and validate graph with stable namespaced node identifiers."""
    g1_directory = Path(g1_directory or ROOT / 'lectures')
    g2_directory = Path(g2_directory or SOURCE_DIRECTORY)
    g3_directory = Path(g3_directory or PAPER_DIRECTORY)
    graph_directory = Path(graph_directory or GRAPH_DIRECTORY)
    g3_plan = _read_json(g3_directory / 'track.json')
    g4_plan = _read_json(graph_directory / 'g4-yws.json')
    relations = _read_json(graph_directory / 'relationships.json')
    # Curated topic relationships are stored separately so the initial audit stays readable.
    topic_relations_path = graph_directory / 'topic-relationships.json'
    topic_relations = _read_json(topic_relations_path) if topic_relations_path.is_file() else {'edges': []}
    topic_path = graph_directory / 'topics.json'
    topic_data = _read_json(topic_path) if topic_path.is_file() else None
    if topic_relations.get('schema_version', 1) != 1:
        raise ValueError('Unsupported topic relationship schema')
    if topic_data is not None and topic_data.get('schema_version') != 1:
        raise ValueError('Unsupported course topic schema')
    if relations.get('schema_version') != 1:
        raise ValueError('Unsupported course graph schema')

    nodes = {}
    edges = []
    tracks = []

    def insert(node):
        node_id = node['id']
        if node_id in nodes:
            raise ValueError(f'Duplicate course node: {node_id}')
        nodes[node_id] = node

    from dkvis.lectures import load_index
    g1_index = load_index()
    g1 = []
    g1_keys = {}
    for folder in sorted(p for p in g1_directory.iterdir() if p.is_dir() and (p/'lecture.md').is_file()):
        node_id = 'g1:' + folder.name
        key = folder.name.split('_', 1)[-1]
        deck = g1_index.get(key, {}).get('deck')
        insert(dict(id=node_id, title=_title_from_file(folder/'lecture.md'),
                    track='g1', status='available', kind='presentation',
                    url='/?deck=' + quote(deck) if deck else '/',
                    source='visualizations/lectures/' + folder.name + '/lecture.md'))
        g1.append(node_id)
        g1_keys[key] = node_id
    # Reuse the organizer's authored prerequisite list for the Manim presentations.
    # They are suggested preparatory lectures, not hard dependencies on listening order.
    for key, node_id in g1_keys.items():
        for parent in g1_index.get(key, {}).get('requires', []):
            if parent in g1_keys:
                edges.append(dict(from_=node_id, to=g1_keys[parent], type='soft_depends_on',
                                  why='The Manim syllabus recommends this background presentation.'))
    tracks.append(dict(id='g1', title='G1 - Manim presentations', status='available',
                       summary='Visual lecture presentations', path=g1))

    g2 = []
    for path in sorted(g2_directory.glob('[0-9][0-9][0-9][0-9][0-9][0-9]-*.md')):
        ident = path.name[:6]
        node_id = 'g2:' + ident
        insert(dict(id=node_id, title=_title_from_file(path), track='g2',
                    status='available', kind='audio',
                    url=f'/audio?track=g2&lecture={ident}',
                    source=f'visualizations/draft-stages/tts-lectures/{path.name}'))
        g2.append(node_id)
    tracks.append(dict(id='g2', title='G2 - Comprehensive audio', status='available',
                       summary='Full 150-lecture path', path=g2))

    g3 = []
    for row in g3_plan['lectures']:
        ident = row['id']
        path = g3_directory / row['file']
        if not path.is_file():
            raise ValueError(f'Missing G3 transcript: {path}')
        node_id = 'g3:' + ident
        insert(dict(id=node_id, title=row['title'], track='g3',
                    status='available', kind='audio',
                    url=f'/audio?track=g3&lecture={ident}',
                    source=f'visualizations/draft-stages/tts-paper/{row["file"]}'))
        g3.append(node_id)
        parent = row.get('source_g2')
        if parent:
            edges.append(dict(from_=node_id, to='g2:' + parent, type='original_parent'))
    tracks.append(dict(id='g3', title=g3_plan['title'], status='available',
                       summary=g3_plan.get('summary', ''), path=g3))

    for row in g4_plan['nodes']:
        insert(dict(id=row['id'], title=row['title'], track='g4',
                    status=row['status'], kind='audio', url=None,
                    source=row['source']))
    tracks.append(dict(id='g4', title=g4_plan['title'], status='planned',
                       summary=g4_plan['summary'], path=g4_plan['path']))

    for triple in [*relations['edges'], *topic_relations['edges']]:
        if not isinstance(triple, list) or len(triple) not in (3, 4):
            raise ValueError(f'Expected [source, relation, target, optional reason]: {triple}')
        source, relation, target = triple[:3]
        reason = triple[3] if len(triple) == 4 else None
        if reason is not None and (not isinstance(reason, str) or not reason.strip()):
            raise ValueError(f'Invalid relationship explanation: {triple}')
        edges.append(dict(from_=source, to=target, type=relation, why=reason))

    topics = []
    if topic_data is not None:
        topics = topic_data['topics']
        topic_ids = {topic['id'] for topic in topics}
        if len(topic_ids) != len(topics):
            raise ValueError('Duplicate course topic')
        assigned = topic_data['g2_assignments']
        if set(assigned) != {node_id for node_id in nodes if node_id.startswith('g2:')}:
            raise ValueError('Topic assignments must cover every G2 lecture')
        g1_assigned = topic_data['g1_assignments']
        if set(g1_assigned) != {node_id for node_id in nodes if node_id.startswith('g1:')}:
            raise ValueError('Topic assignments must cover every G1 presentation')
        for node_id, node in nodes.items():
            if node['track'] == 'g2':
                topic = assigned[node_id]
            elif node['track'] == 'g1':
                topic = g1_assigned[node_id]
            elif node['track'] == 'g3':
                topic = topic_data.get('g3_overrides', {}).get(node_id)
                if topic is None:
                    parent = next((e['to'] for e in edges
                                   if e['from_'] == node_id and e['type'] == 'original_parent'), None)
                    topic = assigned[parent] if parent else 'orientation'
            else:
                topic = topic_data['g4_topic']
            if topic not in topic_ids:
                raise ValueError(f'Unknown topic for {node_id}: {topic}')
            node['topic'] = topic

    seen = set()
    parents = set()
    normalized = []
    for edge in edges:
        source, relation, target = edge['from_'], edge['type'], edge['to']
        if relation not in RELATION_TYPES:
            raise ValueError(f'Unknown relation {relation}')
        if source not in nodes or target not in nodes or source == target:
            raise ValueError(f'Invalid course edge: {source} {relation} {target}')
        triple = (source, relation, target)
        if triple in seen:
            raise ValueError(f'Duplicate edge {triple}')
        seen.add(triple)
        if relation == 'original_parent':
            if source in parents:
                raise ValueError(f'Multiple original parents for {source}')
            parents.add(source)
        normalized.append({'from': source, 'type': relation, 'to': target, **({'why': edge['why']} if edge.get('why') else {})})
    for track in tracks:
        if len(track['path']) != len(set(track['path'])):
            raise ValueError(f'Duplicate path member in {track["id"]}')
        for node in track['path']:
            if node not in nodes:
                raise ValueError(f'Unknown path member {node} in {track["id"]}')
    _check_acyclic(normalized, 'hard_depends_on')
    _check_acyclic(normalized, 'original_parent')
    for track in tracks:
        track['available_count'] = sum(nodes[node]['status'] == 'available' for node in track['path'])
        track['planned_count'] = sum(nodes[node]['status'] != 'available' for node in track['path'])
    return {'schema_version': 1, 'nodes': nodes, 'edges': normalized, 'tracks': tracks, 'topics': topics,
            'relations': {
                'hard_depends_on': 'Required mathematical background for the proof; the lecture still defines what it uses.',
                'soft_depends_on': 'Helpful preparation, not required listening.',
                'expands_on': 'More detail on a topic already treated elsewhere.',
                'original_parent': 'Source adaptation or derivation; records provenance, not a prerequisite.',
                'alternative_presentation': 'Another way of teaching overlapping mathematics.',
                'related_to': 'Related mathematics without a claimed dependency.'
            }}


def connections(graph, node_id):
    """Return directed relations involving a node, plus inverse navigation."""
    if node_id not in graph['nodes']:
        return []
    result = []
    for edge in graph['edges']:
        if node_id not in (edge['from'], edge['to']):
            continue
        other = edge['to'] if edge['from'] == node_id else edge['from']
        result.append(dict(type=edge['type'], direction='outgoing' if edge['from'] == node_id else 'incoming',
                           node_id=other, title=graph['nodes'][other]['title'],
                           status=graph['nodes'][other]['status'], url=graph['nodes'][other]['url'],
                           **({'why': edge['why']} if edge.get('why') else {})))
    return result

if __name__ == '__main__':
    graph = build_course_graph()
    print(f"Course graph: {len(graph['nodes'])} nodes, {len(graph['edges'])} typed edges")
    for path in graph['tracks']:
        print(f"  {path['id']}: {len(path['path'])} positions, "
              f"{path['available_count']} available, {path['planned_count']} planned")
