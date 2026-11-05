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

## Unattributed commits — identification record, 5 November 2026

Two commits that touched the visualization sources carry no `Co-authored-by`
trailer. This section records what the repository's own measured and session
records establish for each. Per the repository convention, a model is recorded
only where a record identifies the authoring model by its own runtime
identification; nothing is inferred from neighboring commits. Both commits are
pushed to `origin/main`, so their messages are not rewritten; this document is
the standing attribution record.

| Commit | Date | Work | Identification |
| --- | --- | --- | --- |
| `f2073e0fd` | 2026-10-09 11:58 EDT | `tweak slides`: narrative edits to `dkvis/slides_process.py` (Friday overview) and `dkvis/slides_sine_theta.py` (title slide) | **Not determinable** from any record available on `aivm-2404`; no model recorded |
| `595e6a9fb` | 2026-11-04 19:27 EST | `wip`: mixed batch (49 files) — tally publish output, upstream contribution census, journal manuscript, visualization TTS/matching changes | **Human-authored (joncrall); no LLM model** |

Evidence for `f2073e0fd` (not determinable):

- The resource-tally ledger has no rows for 2026-10-04 through 2026-10-14
  (rotated ledger `ledger.20261024T050144.jsonl`), so no usage was measured for
  the commit's hour.
- No dkps session in this machine's claude-code, codex, or pi stores was
  active in that window: the dkps claude-code session
  (`c76ad737-bd43-4215-bc40-494806d40e7a`, model `claude-opus-5-5`) ended
  2026-10-03 04:49 UTC, and the codex rollouts active here on Oct 8–9
  (`rollout-2026-10-07T23-18-09-…`) worked a different project (zero references
  to any visualization file).
- The sessions that made the neighboring trailing commits (`GPT-5.6 Sol`,
  `GPT-6`) are not present in this machine's stores, so their transcripts cannot
  be checked either. The commit may be a codex session on another machine or a
  direct human edit; the available record does not say, and no model is
  recorded.

Evidence for `595e6a9fb` (human-authored):

- The only LLM session recorded in this repository in the minutes around the
  commit is the codex session
  `rollout-2026-10-28T11-17-57-01a18316-e406-78a3-b6d7-2b85d853a660` (model
  `gpt-6.1-sol` in all 111 of its recorded responses; span
  2026-10-28T15:17:58Z → 2026-11-05T19:44:11Z; transcript retained on
  `aivm-2404`). Its last recorded commit here before the wip was
  `0e06458f0` at 19:21:46 EST, five and a half minutes earlier.
- The commit carries no tally row of its own (none in the ledger or in
  `.llm_resource_tally/local/`), unlike every other commit made by that
  session, which each produced a measured row.
- The session's transcript records the user instruction at 19:27:51 EST —
  28 seconds after the commit — “Make sure all of your work is committed. don't
  commit anything that is generated.”, and the session's reply 28 seconds later:
  “Most tracked changes are already in your `wip` merge, but the new lesson and
  rendering modules are still untracked.” It then committed only the remaining
  untracked work (`f2061b35a`, `5fdda50fe`, `a357ffb10`). The session's own
  runtime record thus identifies the wip commit as the user's, not the agent's.

If a later source (for example, the owner's recollection of the Oct 9 session,
analogous to the GPT-6.1-Sol confirmation above) identifies the model behind
`f2073e0fd`, add it here with that source; do not infer it from the adjacent
`GPT-5.6 Sol` / `GPT-6` trailers.
