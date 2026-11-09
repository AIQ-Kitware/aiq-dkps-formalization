# Interactive DKPS course graph

The **Learning graph** at `/learning-paths` visualizes the shared curriculum across G1 (Manim), G2 (150 comprehensive recordings), G3 (26 paper-focused recordings), and G4 (the planned YWS track). The graph records mathematical relationships independently of course-path order.

## Browsing

- **Select a node** to display its lecture title, status, assigned topic, and incoming/outgoing connections. Click **Open lecture** for available audio or a presentation.
- **Graph extent** defaults to a two-connection neighborhood. Use one hop for a focused view or **Entire selected path / topic** for an overview.
- **Learning path** displays the specified track and lets you browse lectures reused in another path. Choose **All four tracks** for the combined graph. In the complete topic map, select a topic cluster directly to focus it.
- **Topic cluster** selects a mathematical subject, such as Sylvester equations, principal angles, or the YWS population-gap results.
- **Relationship filters** show or hide hard and soft dependencies, expansions, alternative presentations, original-parent provenance, and general related-topic links. Provenance and broad related-topic links start hidden to keep proof dependencies readable.
- **Search** finds nodes by title, ID, and topic. Mouse wheel or trackpad zooms, dragging empty space pans, and **Fit** restores the full visible selection. Nodes can be selected via mouse, touch, or keyboard Enter.
- Deep links such as `/learning-paths?track=g3&node=g3:020000` select a particular lecture. The audio reader's existing course-graph links continue to work.

Graph arrows point **from a lecture toward the supporting or related lecture**. Incoming hard-dependency arrows indicate a result that uses the selected topic. `original_parent` records source adaptation, not mathematical dependence.

## Data model

- `curriculum/topics.json`: explicit primary topic for every G1 and G2 lecture, G3 topic inheritance from its G2 source except for the introduction, and the G4 population-gap topic. These groupings are navigational labels, not claims of theorem dependence.
- `curriculum/relationships.json`: the initial manually curated cross-track and G3/YWS links.
- `lectures/index.yaml`: the existing G1 organizer's `requires` links are imported as soft presentation prerequisites; the graph links directly to each G1 deck.
- `curriculum/topic-relationships.json`: additional individually authored conceptual relationships for G2, including a short mathematical rationale for each. Each row is `[source_id, relation_type, target_id, reason]`.
- `draft-stages/tts-paper/track.json`: G3 adaptations and their `original_parent` relationships.
- `curriculum/g4-yws.json`: G4's planned nodes and reusable lecture path.

The API remains `GET /api/course-graph`. Nodes have a `topic`; graph responses include topic metadata and, when present, an edge's `why` explanation. Existing three-column relationship entries remain valid. Node IDs are namespaced (`g1:`, `g2:`, `g3:`, `g4:`), so cross-track references remain stable even when paths reuse recordings.

`build_course_graph` checks referential integrity, duplicate relationships, original-parent uniqueness, acyclic hard prerequisites and source parents, and complete G1/G2 topic assignments. New edges should express an identifiable mathematical relationship, not merely adjacency in a syllabus. In particular, G2 lecture numbers alone should never imply a hard dependency.

## Validation

```bash
cd /home/joncrall/code/aiq-dkps-formalization/visualizations
python -m dkvis.presentation.course_graph
python -m pytest -q tests/test_course_graph.py tests/test_audio_course_tracks.py tests/test_audio_lecture_library.py
make serve
```

Visit `http://127.0.0.1:8001/learning-paths`, or use the host's LAN IP. The graph UI is self-contained; it needs no CDN or third-party JavaScript.
