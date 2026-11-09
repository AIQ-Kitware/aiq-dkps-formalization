"""Course paths reuse source lectures; conceptual edges remain validated."""
import json
from pathlib import Path

import pytest
from starlette.testclient import TestClient

from dkvis.presentation.course_graph import build_course_graph, connections
from dkvis.presentation.serve import create_app


def test_course_graph_inventory_and_yws_reuse():
    graph = build_course_graph()
    assert len(graph['nodes']) == 204
    assert set(graph['relations']) == {
        'hard_depends_on', 'soft_depends_on', 'expands_on',
        'original_parent', 'alternative_presentation', 'related_to'}
    tracks = {track['id']: track for track in graph['tracks']}
    assert len(tracks['g1']['path']) == 22
    assert len(tracks['g2']['path']) == 150
    assert len(tracks['g3']['path']) == 26
    assert tracks['g4']['available_count'] == 7
    assert tracks['g4']['planned_count'] == 6
    assert tracks['g4']['path'].count('g3:003000') == 1
    assert graph['nodes']['g4:residual-proof']['url'] is None
    assert graph['nodes']['g2:147000']['url'].startswith('/audio?track=g2')
    assert graph['nodes']['g3:003000']['url'].startswith('/audio?track=g3')
    original = [e for e in graph['edges'] if e['type'] == 'original_parent']
    assert len(original) == 25
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
        assert 'DKPS learning paths' in client.get('/learning-paths').text
        tracks = client.get('/api/audio-tracks').json()['tracks']
        assert [track['id'] for track in tracks] == ['g1', 'g2', 'g3', 'g4']
        assert tracks[-1]['kind'] == 'graph'
        detail = client.get('/api/audio-lectures/147000?track=g2').json()
        assert any(row['node_id'] == 'g1:003875_yws'
                   for row in detail['course_connections'])
        audio_html = client.get('/audio').text
        assert 'Course graph connections' in audio_html
        assert '/learning-paths?track=g4' in audio_html
