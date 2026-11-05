# Model authorship correction — 5 November 2026

Jon identified the authoring model for this session as **GPT-6.1-Sol**, and
confirmed: “In fact, I know all of the new numbered lectures and transcripts
were made via this model.” Earlier records used
`GPT-6 (Codex; exact model variant and weights/config undetermined)`.

The numbered lectures' `provenance.yaml` files now use **GPT-6.1-Sol** for their
initial authorship and revisions, with the original source commits/dates and
the explicit confirmation retained. This includes the lecture slides,
transcripts, and quizzes. Unknown weights or runtime settings are not inferred.
Generated covers and future exports use the corrected source attribution.
Existing video-generation snapshots still describe what was recorded at export.

The following commits from this session carry the earlier generic model name.
This document corrects their **model co-author identification** to
**GPT-6.1-Sol**. Human authorship, commit hashes, and measured resource-accounting
records remain as recorded. Accounting commits are listed for authorship only;
this correction is not a recalculation of resource usage.

| Commit | Work |
| --- | --- |
| `f9d93847b` | Group lecture resources with transcripts captions and provenance |
| `03a3f6891` | Publish resource accounting for lecture library improvements |
| `792e82240` | Add attributed robot covers and incremental lecture video updates |
| `79087ae34` | Publish resource accounting for incremental lecture updates |
| `0b2261815` | Document cover refresh when lecture attribution changes |
| `720de2544` | Publish final lecture update resource accounting |
| `aabc931ce` | Make lectures standalone and improve native media navigation |
| `46ed65938` | Publish lecture cleanup resource accounting |
| `cbe21cd57` | Save viewer feedback with lecture generation and playback context |
| `4b4924f6e` | Publish lecture feedback resource accounting |
| `0dd6bf3ae` | Restrict the lecture library to registered presentation decks |
| `accfd1c8c` | Publish lecture catalog resource accounting |
| `6019c7ee9` | Expose a caption toggle and playback speeds up to 4x |
| `d46ed5956` | Centralize user lecture style rules and organize visualization documentation |
| `74eadb30d` | Publish lecture style and player controls resource accounting |
