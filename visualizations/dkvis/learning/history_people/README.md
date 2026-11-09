# People behind the mathematics

Two standalone biographical companions to the mathematical history overview:

| Lecture | Deck | People |
| --- | --- | --- |
| 000670 | `history-people-foundations` | Sylvester, Jordan, Rayleigh, Ritz, Weyl |
| 000835 | `history-people-operators` | Sz.-Nagy, Halmos, Kato, Davis, Kahan |

Each has an introduction, one two-beat portrait/publication scene per person,
connections and summary slides, full image-credit cards, and four study questions.
They focus on careers and mathematical context rather than proofs. Neither
requires the earlier overview, and neither claims to cover every contributor.

```bash
# From visualizations/:
uv run python -m dkvis.presentation.external_assets fetch
make slides DECK=history-people-foundations
make slides DECK=history-people-operators
make video DECK=history-people-foundations TTS_PROFILE=crall-math-dk-v2-breeze-tts2
make video DECK=history-people-operators TTS_PROFILE=crall-math-dk-v2-breeze-tts2
```

Both participate in `make lectures-video`. Restart an already-running library
server to load their registrations. Generated HTML/PDF/video files and image
bytes stay ignored. The title credits the lecture's source-model provenance;
portrait creators and licenses are credited separately on each image use.

- [Foundations transcript](../../../lectures/000670_history_people_foundations/lecture.md)
  and [sources](../../../lectures/000670_history_people_foundations/sources.md).
- [Operators transcript](../../../lectures/000835_history_people_operators/lecture.md)
  and [sources](../../../lectures/000835_history_people_operators/sources.md).
- [Image-store and transfer guide](../../../docs/EXTERNAL_ASSETS.md).
- [Cast coverage and next episodes](../../../docs/planning/history-cast-and-images.md).

`people.yaml` supplies concise card text and biography links; the numbered
`lecture.md` files own spoken narration. `scenes.py` binds each beat exactly
through the shared lesson components. No biography is used as proof of a
mathematical assertion, and no later portrait is presented as a picture taken
at the earlier publication date.
