# Internal roadmap bookkeeping

Working notes for this repository. **Nothing here is part of the roadmap family**, and no
roadmap document links to it.

- [`pr-draft.md`](pr-draft.md) — scratch space for the upstream submission: a skeleton PR
  body, and the open discussion points to settle or to raise with Tau Ceti reviewers.
- [`candidate-topic-design.md`](candidate-topic-design.md) — the partition of every
  `ForTauCeti` module into fine-grained topic keys, ordered so that each is submittable
  against the topics before it. Validated by
  `scripts/check_tauceti_roadmap_topics.py`.
- [`topic-map.md`](topic-map.md) — which roadmap directory owns which topic keys. The
  checker reads this file; the topic keys deliberately appear nowhere in the roadmaps
  themselves.

Two commands:

```sh
python3 scripts/check_tauceti_roadmap_topics.py --roadmaps  # the roadmap-level DAG
python3 scripts/check_tauceti_roadmap_topics.py --check     # total, disjoint, acyclic
```

`scripts/check_roadmap_delivered.py` reports, per roadmap, how many suggested signature
names already have a declaration somewhere in the libraries. It is a planning aid: a name
match says nothing about whether the two statements agree, and its output must not be
copied into a roadmap.
