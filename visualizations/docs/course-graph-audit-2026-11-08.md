# Shared course graph and YWS path audit

## Architecture

The repository now has a common graph of **lecture nodes** and **typed edges**. G1, G2, G3 and G4 are ordered **paths** through those nodes. Membership in a path does not create a prerequisite edge; one recording can be selected in multiple paths without copying its transcript or generating another audio cache.

Stable node IDs are namespaced: `g1:003875_yws`, `g2:147000`, `g3:004000`, and `g4:residual-proof`. The namespace here identifies the node's *authoring home*, not which paths may contain it. A path may include a node authored in any namespace. The graph inventories 22 G1 presentations, 150 G2 recordings, 26 G3 recordings, and six **planned** YWS recordings, or 204 distinct nodes. The first curated edge set has 90 links, including 25 original-parent mappings taken directly from the existing G3 syllabus.

Graph sources:

- `visualizations/curriculum/relationships.json` contains explicitly reviewed conceptual links.
- `visualizations/curriculum/g4-yws.json` contains the proposed G4 path and planned YWS-specific nodes.
- G1 presentation folders, G2 Markdown filenames, and G3 `track.json` provide the other node and path inventories.
- `dkvis.presentation.course_graph` validates node references, unique IDs, path membership, original-parent uniqueness, and cycles in the hard-prerequisite and original-parent subgraphs.

## Relationship semantics

| Relation | Meaning | Usage |
| --- | --- | --- |
| `hard_depends_on` | Mathematical material directly needed to develop or reconstruct an argument | Use sparingly; do not infer from recording order. The lecture still introduces its essential assumptions locally. |
| `soft_depends_on` | Recommended prior knowledge that improves comprehension | The listener can skip this link without breaking the proof. |
| `expands_on` | The source node offers a deeper or narrower treatment of material in the target | Does not imply the source was adapted from the target. |
| `original_parent` | The original authored source of an adaptation | Provenance, **not** a mathematical prerequisite. At most one immediate parent; parent chains are supported. |
| `alternative_presentation` | Different media or pedagogical approach to overlapping content | Navigation is symmetric, even though each edge is stored once. |
| `related_to` | Useful connection without a known direction or prerequisite | Retained as an optional relation; do not add speculative edges. |

Edges are stored as `[source, relation, target]`. A link such as `g3:020000 --original_parent--> g2:110000` records the provenance of the shortened sine-theta recording. Another link such as `g4:residual-proof --hard_depends_on--> g3:003000` identifies a necessary residual calculation for the proposed proof treatment.

## Proposed G4: Yu-Wang-Samworth

YWS works with finite-dimensional real symmetric matrices, ordered eigenvector blocks, population-only eigengaps, principal angles, residual bounds, frame alignment, and a rectangular extension. A full course on unbounded operators, operator ideals, and direct-rotation optimization is not required to state and prove the population-gap theorem.

The G4 path uses **seven available recordings** from G2/G3 and **six new, planned recordings**, arranged in 13 positions:

1. New YWS motivation and population-gap overview *(planned)*.
2. G3 finite spectral picture, spectral separation, trial-space residuals, and principal-angle geometry *(four available recordings)*.
3. New mixed-versus-population-gap example, population-residual proof of Theorem 2, and sharpness analysis *(three planned recordings)*.
4. G2 population-gap statistics, Procrustes alignment, and rectangular subspace estimates *(three available recordings)*.
5. New rank-boundary/rectangular source correction and statistical application synthesis *(two planned recordings)*.

Existing relevant mathematical source anchors include `YuWangSamworth2015/Symmetric/Theorem2.lean`, `YuWangSamworth2015/Rectangular/SourceTheorem3.lean`, the `MiddleBlockSharpness` development, and the Manim presentation at `visualizations/lectures/003875_yws/`.

G4 appears at `/learning-paths?track=g4`. Shared recordings open in the existing `/audio` reader, which continues to generate and cache their audio under their original G2/G3 identity. Planned entries are visible but have no playback link. G4 is therefore a **separate path**, not a copy of G3 or a branch that requires completing G3.

## Editorial implications

Retain standalone introductions within each recording. Graph prerequisites represent mathematical conceptual relationships, not instructions to listen to other recordings first. Reusing a recording in G4 is preferable to pasting its prose into a new file; new G4 recordings should focus on YWS-specific arguments.

The current graph provides full node coverage but only a **curated initial set of edges**. Additional relationships, especially among the 150 G2 foundation lectures, should be added after reviewing their actual hypotheses and proof flow. A missing edge does not assert mathematical independence.

## API and verification

- `/learning-paths` browses the paths, node status, and incoming/outgoing edges.
- `/api/course-graph` supplies the normalized graph for future learning-system clients.
- `/api/audio-lectures/{id}?track=g2|g3` includes `course_connections` alongside the existing transcript and reference links.
- `/audio?track=g2|g3&lecture=000000` opens a particular shared recording.

Run `python -m dkvis.presentation.course_graph` from `visualizations/` to verify and summarize the graph. Run `python -m pytest -q tests/test_course_graph.py tests/test_audio_course_tracks.py` for API and edge validation.

## Follow-on work

1. Draft and independently review the six G4-only recordings, starting with the population-residual proof and corrected rectangular theorem.
2. Expand G2 conceptual edges in proof-order batches, retaining the distinction between hard and soft dependencies.
3. Add domain-specific grouping and topic-based graph filters after observing how people use the initial path navigator.
