"""Course paths reuse source lectures; conceptual edges remain validated."""
import json
from pathlib import Path

import pytest
from starlette.testclient import TestClient

from dkvis.presentation.course_graph import build_course_graph, connected_components, connections
from dkvis.presentation.serve import create_app


def test_course_graph_inventory_and_yws_reuse():
    graph = build_course_graph()
    assert len(graph['nodes']) >= 209
    assert set(graph['relations']) == {
        'hard_depends_on', 'soft_depends_on', 'expands_on',
        'original_parent', 'alternative_presentation', 'related_to',
        'listening_next', 'proof_depends_on'}
    tracks = {track['id']: track for track in graph['tracks']}
    assert len(tracks['g1']['path']) == 22
    assert len(tracks['g2']['path']) >= 154
    assert len(tracks['g3']['path']) == 27
    assert tracks['g4']['available_count'] == 7
    assert tracks['g4']['planned_count'] == 6
    assert tracks['g4']['path'].count('g3:003000') == 1
    assert graph['nodes']['g4:residual-proof']['url'] is None
    assert graph['nodes']['g2:147000']['url'].startswith('/audio?track=g2')
    assert graph['nodes']['g3:003000']['url'].startswith('/audio?track=g3')
    original = [e for e in graph['edges'] if e['type'] == 'original_parent']
    assert len(original) == 26
    assert {'from': 'g3:020000', 'to': 'g2:110000', 'type': 'original_parent'} in original
    assert all(graph['nodes'][e['from']]['track'] == 'g3' for e in original)
    assert any(e['type'] == 'hard_depends_on' and e['to'] == 'g3:003000'
               for e in graph['edges'])
    incoming = connections(graph, 'g2:110000')
    assert any(row['node_id'] == 'g3:020000' and row['direction'] == 'incoming'
               for row in incoming)


def test_graph_rejects_invalid_edges_and_cycles(tmp_path):
    from dkvis.presentation.course_graph import GRAPH_DIRECTORY
    for filename in ('g4-yws.json', 'relationships.json'):
        (tmp_path / filename).write_bytes((GRAPH_DIRECTORY / filename).read_bytes())
    rpath = tmp_path / 'relationships.json'
    data = json.loads(rpath.read_text())
    data['edges'].append(['g4:unknown', 'soft_depends_on', 'g3:001000'])
    rpath.write_text(json.dumps(data))
    with pytest.raises(ValueError, match='Invalid course edge'):
        build_course_graph(graph_directory=tmp_path)
    data['edges'].pop()
    data['edges'].extend([
        ['g3:001000', 'hard_depends_on', 'g3:002000'],
        ['g3:002000', 'hard_depends_on', 'g3:001000'],
    ])
    rpath.write_text(json.dumps(data))
    with pytest.raises(ValueError, match='cycle'):
        build_course_graph(graph_directory=tmp_path)


def test_graph_api_and_reader_links(tmp_path):
    render = tmp_path / 'renders'
    render.mkdir()
    with TestClient(create_app(render)) as client:
        response = client.get('/api/course-graph')
        assert response.status_code == 200
        assert response.json()['tracks'][-1]['id'] == 'g4'
        assert client.get('/learning-paths?track=g4').status_code == 200
        assert 'DKPS · Course graph' in client.get('/learning-paths').text
        tracks = client.get('/api/audio-tracks').json()['tracks']
        assert [track['id'] for track in tracks] == ['g1', 'g2', 'g3', 'g4']
        assert tracks[-1]['kind'] == 'graph'
        detail = client.get('/api/audio-lectures/147000?track=g2').json()
        assert any(row['node_id'] == 'g1:003875_yws'
                   for row in detail['course_connections'])
        audio_html = client.get('/audio').text
        assert 'Course graph connections' in audio_html
        assert '/learning-paths?track=g4' in audio_html


def test_curated_topic_graph_covers_every_lecture():
    graph = build_course_graph()
    assert len(graph['topics']) == 13
    assert len(graph['nodes']) >= 209
    assert len(graph['edges']) >= 650
    assert all(node.get('topic') for node in graph['nodes'].values())
    topics = {topic['id'] for topic in graph['topics']}
    assert set(node['topic'] for node in graph['nodes'].values()) == topics
    sources = {edge['from'] for edge in graph['edges']}
    for number in range(1, 150):
        assert f'g2:{number*1000:06d}' in sources
    assert graph['nodes']['g2:147000']['topic'] == 'statistics'
    assert graph['nodes']['g3:020000']['topic'] == 'davis-kahan'
    assert graph['nodes']['g4:residual-proof']['topic'] == 'statistics'


def test_curated_links_have_explanations_and_cross_track_connections():
    graph = build_course_graph()
    reasons = [e for e in graph['edges'] if e.get('why')]
    assert len(reasons) >= 250
    assert any(e['from'] == 'g2:110000' and e['to'] == 'g2:108000'
               and e['type'] == 'hard_depends_on' for e in reasons)
    assert any(e['from'] == 'g3:020000' and e['to'] == 'g2:110000'
               and e['type'] == 'alternative_presentation' for e in reasons)
    assert any(e['from'] == 'g4:application' and e['to'] == 'g2:148000'
               and e['type'] == 'expands_on' for e in reasons)
    assert all(e['why'].strip() and len(e['why']) > 20 for e in reasons)
    assert any('why' in c for c in connections(graph, 'g2:110000'))


def test_new_graph_ui_controls_and_api(tmp_path):
    render = tmp_path / 'renders'
    render.mkdir()
    with TestClient(create_app(render)) as client:
        response = client.get('/api/course-graph')
        assert response.status_code == 200
        data = response.json()
        assert 'topics' in data and len(data['topics']) == 13
        assert any(edge.get('why') for edge in data['edges'])
        text = client.get('/learning-paths?track=g4&node=g4:overview').text
        for marker in ('id="graph"', 'id="relations"', 'id="topic"',
                       'id="extent"', 'id="zoom-in"', 'id="fit"',
                       'id="connections"', 'id="edges-all"', 'id="edges-none"',
                       'id="edges-core"', 'id="node-labels"', 'id="maximize"', '/api/course-graph'):
            assert marker in text
        assert '<option value="all" selected>' in text
        assert 'listening_next' in text and 'proof_depends_on' in text


def test_g1_syllabus_links_to_exact_deck_and_uses_authored_background():
    graph = build_course_graph()
    assert graph['nodes']['g1:003875_yws']['url'] == '/?deck=yws-population-gap'
    assert graph['nodes']['g1:001000_projections']['url'] == '/?deck=prereq-projections'
    assert any(e['from'] == 'g1:003875_yws' and e['to'] == 'g1:003750_sine_theta'
               and e['type'] == 'soft_depends_on' and e.get('why')
               for e in graph['edges'])


def test_all_nodes_connected_by_navigation_and_real_cross_track_relationships():
    graph = build_course_graph()
    assert len(connected_components(graph)) == 1
    # Course order alone connects each path, not the different tracks.
    order_only = connected_components(graph, relation_types={'listening_next'})
    assert len(order_only) == 2
    g1_count = len(next(track['path'] for track in graph['tracks'] if track['id'] == 'g1'))
    assert sorted(map(len, order_only)) == sorted([g1_count, len(graph['nodes']) - g1_count])
    # Actual alternative presentations tie G1 to the audio tracks.
    overview_types = {'listening_next', 'proof_depends_on', 'alternative_presentation'}
    assert len(connected_components(graph, relation_types=overview_types)) == 1
    assert len(connected_components(graph, relation_types=set())) == len(graph['nodes'])
    assert len(connected_components(graph, node_ids={'g2:000000','g2:001000'})) == 1


def test_listening_order_is_explicit_and_not_a_mathematical_dependency():
    graph = build_course_graph()
    path_edges = {(e['from'], e['to']): e for e in graph['edges'] if e['type'] == 'listening_next'}
    expected_pairs = {
        (first, second)
        for track in graph['tracks']
        for first, second in zip(track['path'], track['path'][1:])
    }
    assert set(path_edges) == expected_pairs  # Shared pairs are counted once.
    for track in graph['tracks']:
        for first, second in zip(track['path'], track['path'][1:]):
            row = path_edges[first, second]
            assert track['id'].upper() in row['why']
    assert ('g1:000505_history_overview', 'g1:000670_history_people_foundations') in path_edges
    assert ('g3:000000', 'g3:001000') in path_edges
    assert ('g4:overview', 'g3:001000') in path_edges
    assert 'Next' in graph['relations']['listening_next']


def test_proof_links_are_curated_with_explicit_reasons():
    graph = build_course_graph()
    proof_edges = [e for e in graph['edges'] if e['type'] == 'proof_depends_on']
    assert len(proof_edges) == 42
    assert all(e['why'] and len(e['why']) > 25 for e in proof_edges)
    assert any(e['from'] == 'g2:110000' and e['to'] == 'g2:071000'
               for e in proof_edges)
    assert any(e['from'] == 'g2:134000' and e['to'] == 'g2:133000'
               for e in proof_edges)
    assert any(e['from'] == 'g4:residual-proof' and e['to'] == 'g3:003000'
               for e in proof_edges)


def test_proof_graph_rejects_cycles(tmp_path):
    from dkvis.presentation.course_graph import GRAPH_DIRECTORY
    for filename in ('g4-yws.json', 'relationships.json', 'proof-relationships.json'):
        (tmp_path / filename).write_bytes((GRAPH_DIRECTORY / filename).read_bytes())
    data = json.loads((tmp_path / 'proof-relationships.json').read_text())
    data['edges'] += [
        ['g2:110000', 'proof_depends_on', 'g2:112000', 'A test-only cycle edge'],
        ['g2:112000', 'proof_depends_on', 'g2:110000', 'The reverse test-only cycle edge'],
    ]
    (tmp_path / 'proof-relationships.json').write_text(json.dumps(data))
    with pytest.raises(ValueError, match='proof_depends_on cycle'):
        build_course_graph(graph_directory=tmp_path)
