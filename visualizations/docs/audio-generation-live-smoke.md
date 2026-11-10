# Live audio generation smoke test

The offline unit tests do not establish that the rebuilt Docker container and
running DKPS reader cooperate correctly on the actual GPU. This test is run on
the machine hosting both services.

## Prerequisites

- `local-ai` Breeze is rebuilt and reachable at `http://127.0.0.1:8821`.
- The DKPS reader is running at `http://127.0.0.1:8001/audio`.
- The checked-in public Breeze profile and its advertised voice are used by
  default (`crall-math-dk-v2-breeze-tts2` and `crall-math-dk-v2`). Set
  `DKVIS_TTS_PROFILE` and/or `TTS_BENCH_VOICE` only to override them. The script
  does not print voice identifiers. An explicitly selected profile with no
  advertised default voice requires `TTS_BENCH_VOICE`.
- Use two lectures with missing cached audio. Defaults: `000000` and `001000`.
- Do not exercise a lecture already being generated elsewhere: the script
  refuses to cancel a lecture that has pre-existing jobs.

First inspect the running services **without starting any synthesis**:

```bash
cd /home/joncrall/code/aiq-dkps-formalization
python3 visualizations/tools/smoke_audio_generation.py
```

Then opt in to actual speech requests:

```bash
python3 visualizations/tools/smoke_audio_generation.py \
  --exercise --pages 3 --cancel-delay 5
```

The exercise:

1. Requests up to three missing pages of lecture A as background cache work.
2. Samples the lecture's generation queue, ETA, and paragraph progress.
3. Requests an uncached page from lecture B at interactive playback priority.
4. Cancels pending and active work for lecture A.
5. Polls until lecture B's page is ready or the deadline is reached.
6. Reports whether the old lecture has outstanding tasks. The script never
   deletes finished cached audio.

Use `--lecture-a ID --lecture-b ID` to select other lectures, `--track g3`
for the paper track, or `--timeout 360` on a heavily loaded GPU. The default
`--timeout` is 240 seconds. Only the `--exercise` form sends synthesis and
cancellation requests.

The exercise calls the same DKPS endpoints used by the browser, and checks that
the Breeze server advertises `/v1/audio/jobs`. It does not launch a browser or
check screen layout.

## Browser verification

Open `/audio`, select the local Breeze profile and voice, then:

1. Choose a partially cached lecture. Confirm the page chips and ready/total
   counts match the script's read-only inventory.
2. Click **Cache whole lecture**. Confirm the elapsed time, ETA and paragraph
   progress update while the page is being synthesized.
3. Choose a different uncached lecture and click **Play page**. Its request
   should have playback priority. On the earlier lecture's queue entry, choose
   **Cancel lecture**, or return to the earlier lecture and click **Stop generation**.
4. Confirm the new lecture becomes playable, unfinished old jobs disappear,
   and completed pages remain cached.
5. Reload `/audio`. Cached status should persist. ETA estimates should be
   informed by newly completed pages.

**Background preparation:** `Cache whole lecture` now starts a server-owned
campaign that submits a bounded number of pages to the priority queue and
continues when you switch lectures or close the tab. The API reports its
status through `GET /api/audio-generation/inventory`. Stop the campaign with
**Stop generation** or **Cancel lecture**. Campaigns are in-memory; restart a
campaign after restarting the DKPS server. Existing completed pages are reused.
The smoke script also tests multiple pending jobs independently.

## Interpreting failures

- **Missing job API:** the running Docker image is older than the server
  overlay. Rebuild/restart the Breeze service.
- **Reader connection refused:** start `make serve` from `visualizations/`.
- **Profile/voice rejected:** verify the locally configured Breeze profile and
  `TTS_BENCH_VOICE`. No voice identifier is required in checked-in files.
- **Old jobs remain in canceling state:** active inference can finish its
  current passage before the server observes cancellation.
- **New lecture never reaches ready:** inspect DKPS and Docker logs locally;
  the smoke-test console deliberately withholds raw server errors, which may
  contain private configuration values.
