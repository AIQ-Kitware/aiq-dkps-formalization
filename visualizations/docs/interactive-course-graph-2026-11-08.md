# Interactive DKPS course graph

The **Learning graph** at `/learning-paths` shows 204 lecture nodes across G1 (Manim), G2 (150 comprehensive audio recordings), G3 (26 focused paper recordings), and the planned G4 YWS course. Every node is visible on the initial map.

## Browse and filter

- The default view shows the **entire graph**, arranged by thirteen mathematical topic clusters. Nodes remain visible when relationship types are hidden. Topic and learning-path filters narrow the node set deliberately.
- Use the individual relationship checkboxes to enable or disable each edge type. The **All edges**, **Core edges**, and **No edges** controls provide useful presets. Core edges include listening order, proof dependencies, and alternative-presentation links connecting G1 to the audio tracks.
- The counter above the map reports the number of visible nodes, visible edges, and weakly connected components under the chosen edge filters. For the default filters, all 204 nodes form one connected component; with listening order alone, G1 and the audio tracks are separate components.
- Click a node for its lecture details and outgoing/incoming connections. Search by lecture title, ID, or topic; selecting a search result centers the corresponding node without hiding other nodes. Use **Expand** for a larger graph, and **Fit** to restore the current map bounds.
- Zoom with the mouse wheel, drag empty space to pan, turn on **Show all lecture labels** when examining a cluster, or change **Graph extent** to a one- or two-hop neighborhood.
- Available nodes link to their audio or Manim presentation; planned G4 recordings remain clearly labeled.

## Relationship semantics

| Type | Arrow direction | Meaning |
| --- | --- | --- |
| `listening_next` | Earlier to later | Consecutive positions in a named G1–G4 course path; no prerequisite claim |
| `proof_depends_on` | Proof to supporting result | An explicit lemma, identity, construction, or estimate used in the proof |
| `hard_depends_on` | Result to prerequisite | Required mathematical background |
| `soft_depends_on` | Lecture to background | Helpful preparation |
| `expands_on` | Detailed to introductory | More complete mathematical treatment |
| `alternative_presentation` | One treatment to another | Overlapping mathematical exposition |
| `original_parent` | Adaptation to source | Source provenance, not a proof dependency |
| `related_to` | Topic to topic | Related mathematical ideas |

**Listening order is never inferred to be a hard mathematical dependency.** The 203 unique sequence edges come from adjacent positions in the four named paths, with shared G3/G4 pairs deduplicated. The 42 specifically curated `proof_depends_on` edges are stored separately with the mathematical reason for each link.

## Source files and behavior

- `curriculum/relationships.json`: initial G3/G4 and cross-track relationships.
- `curriculum/topic-relationships.json`: 277 curated G2 conceptual relationships.
- `curriculum/proof-relationships.json`: proof-use links with explanations.
- `curriculum/topics.json`: topic cluster assignments.
- `draft-stages/tts-paper/track.json` and `curriculum/g4-yws.json`: course paths and original parent mappings.
- `lectures/index.yaml`: the G1 organizer's recommended background relationships.
- `dkvis/presentation/course_graph.py`: derives all `listening_next` edges from paths and validates the graph.
- `dkvis/presentation/course_graph.html`: standalone SVG-based interactive explorer (no CDN or external graph library).

The server exposes the graph as `GET /api/course-graph`. `build_course_graph()` rejects invalid node references, duplicate relationships, cyclic hard/proof dependencies, and cyclic original-parent relationships. `connected_components()` measures graph connectivity with selectable relation types and node subsets.

## Checks

```bash
cd /home/joncrall/code/aiq-dkps-formalization/visualizations
python -m dkvis.presentation.course_graph
python -m pytest -q tests/test_course_graph.py tests/test_audio_course_tracks.py tests/test_audio_lecture_library.py
make serve
```

Open `http://127.0.0.1:8001/learning-paths` or the equivalent LAN address.
