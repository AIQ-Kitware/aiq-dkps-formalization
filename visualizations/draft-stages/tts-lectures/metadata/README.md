# Non-spoken lecture citations and related reading

This directory holds one JSON sidecar per numbered transcript (`000000.json` through
`149000.json`) and a shared bibliographic catalog (`sources.json`). The TTS pipeline
uses `extract_narration.py` to extract only the marked spoken region of each
lecture. Sidecars supply source-audit and learning-server metadata.

## Two independent kinds of reference

- `historical_claims`: exact excerpts of narration that make a historical
  assertion, attribute a development to a person/paper, describe the original
  paper's hypotheses, quote its numbered results, or report what that paper
  asks or claims. Each entry has a source, a source locator, an audit state,
  and an anchor pointing to the spoken words. The `audit_status` field records
  whether the primary passage has been reviewed.
- `related_resources`: optional reading or video suggestions that explain
  similar material, frequently using different examples or hypotheses.
  Their `reason` describes what each resource adds.

Routine definitions, lemmas, and mathematical propositions generally need no
external bibliographic markup here; their proof and scope are governed by the
Lean implementation and the mathematical companion appendices. Historical
attribution and claims *about* the original published text remain candidates
for external primary-source checking.

## Public learning resources

Select resources whose teaching content is freely readable or watchable without
payment or creating an account. Prefer a specific openly accessible lecture,
worked example, article, or complete text over a publisher catalog entry.
In `sources.json`, new public learning entries record `access: free_no_login`
and a `format` such as `html`, `video_and_transcript`, or `pdf`.

Keep primary historical bibliography independently of teaching-resource
selection. Use `related_resources.reason` to identify the actual mathematics
explained by each link, and avoid assigning an entire course to an episode when
a more specific lesson is available.

## Sidecar format

For `053000-the-best-map-when-we-keep-only-a-few-directions.md`, the companion
`metadata/053000.json` has this structure (excerpt):

```json
{
  "schema_version": 1,
  "lecture_id": "053000",
  "transcript": "053000-low-rank-approximation-and-eckart-young.md",
  "historical_claims": [
    {
      "id": "053000-h01",
      "anchor": "Eckart–Young identifies an optimal rank-k approximation for both measurements.",
      "kind": "historical_attribution",
      "source_ids": ["eckart-young-1936"],
      "source_locator": "Original rank approximation",
      "audit_status": "pending_primary_passage_comparison"
    }
  ],
  "related_resources": [
    {"source_id": "mit-strang-svd", "reason": "Finite-dimensional singular-direction intuition; ..."}
  ]
}
```

The complete file, rather than this shortened illustration, is authoritative.
A reference ID resolves through `sources.json`, where its bibliographic title,
URL, type, and where it was discovered are recorded.

Anchors are **verbatim excerpts of the spoken content**, not citation tags
embedded in it. To avoid fragile absolute paragraph numbers or manual offsets,
the validator locates each anchor uniquely after extraction and tolerates only
whitespace reflow. A substantive textual change to a historical claim requires
updating the sidecar; a missing or multiply matched anchor fails validation.
Stable claim IDs can then be used in editorial review and a learning-system UI.

## Audit status

- `pending_primary_passage_comparison`: primary-passage review is queued.
- `primary_passage_confirmed`: a reviewer compared the claim with the original
  source text (including the theorem's assumptions), and recorded evidence of
  the comparison in the source audit notes.
- `claim_needs_correction`: a review identified a mismatch, disputed
  attribution, or unsupported statement; record the issue before editing.

A `primary_passage_confirmed` claim must also supply a `verification` object
with `reviewer`, `checked_on`, and `primary_locator` fields; a
`claim_needs_correction` record must include a nonempty `issue`. The
validator rejects premature confirmation without that supporting record.

Historical claim review records the wording and hypotheses of published
statements. Mathematical counterexamples and proofs are recorded in the
lecture's mathematical companion and Lean correspondence.

## Check and export

At the repository root:

```bash
python3 visualizations/draft-stages/tts-lectures/reference_metadata.py --check
python3 -m unittest discover \
  -s visualizations/draft-stages/tts-lectures \
  -p test_reference_metadata.py
```

An opt-in machine-readable record for the **future** learning server:

```bash
python3 visualizations/draft-stages/tts-lectures/reference_metadata.py \
  --json 053000 > /tmp/053000-learning.json
```

The JSON includes the unchanged extracted narration, citation anchors with
character offsets, optional reading links, and relevant bibliography records.
**Do not send that JSON to TTS.** For TTS use only:

```bash
python3 visualizations/draft-stages/tts-lectures/extract_narration.py \
  visualizations/draft-stages/tts-lectures/053000-low-rank-approximation-and-eckart-young.md \
  > /tmp/053000-speech.txt
```

Slide, timing, visualization, and server design remain future phases.
