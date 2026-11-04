# Independent local theorem exploration experiments

This directory evaluates **Loogle**, **LeanExplore**, and optionally
**LeanSearch v2** against the AIQ DKPS formalization project. These are
three independent upstream tools, not a new DKPS analysis stack.

**No `leanq`, semantic-alignment-server, internal source census, new Lean
module, modification to `lakefile.toml`, or hosted inference endpoint.**
The experiment is opt-in. Every generated artifact, third-party checkout,
Python environment, search index, model, and run result lives under this
folder's ignored `.build/` directory unless overridden explicitly.

## What each tool can actually search

| Tool | Search interface | Your Lean 4.36.0-rc1 and local DKPS? | GPU |
| --- | --- | --- | --- |
| Loogle | Upstream CLI and native localhost web UI | **Yes**, directly indexes compiled modules and transitive imports from your pinned Lake environment | No |
| LeanExplore | Local Python `Service` and stdio MCP server | **No** by default: its downloaded, precomputed package index is independent of this checkout and may represent other Mathlib revisions | Optional; uses 0.6B embed/rerank models |
| LeanSearch v2 | Upstream local FastAPI search and `/docs` | **No** by default: published cuVS index represents **Mathlib v4.28.0-rc1**; no DKPS/TauCeti | One-GPU retriever-only experiment, not full reranking |

The first priority is whether native tools reveal interesting mathematics,
not whether they can be made to resemble the existing proof viewer. This
overlay does **not** rebuild LeanExplore or LeanSearch's corpora against
Lean 4.36. Rebuilding them is a separate project involving their upstream
extraction pipelines; LeanSearch's informalization pipeline also uses an
LLM endpoint by default, which is outside this local-only experiment.

## 1. Loogle (start here)

From the **DKPS repo root**:

```bash
./dev/theorem-exploration/install-loogle.sh

# The main project must have compiled .olean files; if not:
lake exe cache get
lake build DavisKahan.All

# Search DKPS declarations and their imported TauCeti/Mathlib dependencies:
./dev/theorem-exploration/run-loogle.sh --module DavisKahan.All 'sinTheta'

# Native, completely local browser interface:
./dev/theorem-exploration/run-loogle.sh --web --module DavisKahan.All
# http://127.0.0.1:8088
```

Loogle supports a single import root per invocation. To explore other
independent packages, switch modules (e.g. `YuWangSamworth2015`,
`DkpsQuench2026`, `ForTauCeti`, or `Mathlib`). For simultaneous web
views, assign different ports:

```bash
./dev/theorem-exploration/run-loogle.sh --web --port 8089 --module YuWangSamworth2015
./dev/theorem-exploration/run-loogle.sh --json --module DkpsQuench2026 'spectral'
```

`--prepare` explicitly runs `lake exe cache get` and `lake build MODULE`.
Do **not** use that mode when testing strict offline operation; run it
once during initial provisioning. The Loogle binary is built with the
project's *exact* `lean-toolchain`, rather than editing your main Lake
manifest. If the pinned toolchain changes, reinstall Loogle.

The Loogle index is cached in `.build/loogle/index/`, not in `.lake` or
a dependency checkout. It uses upstream Loogle's invalidation logic.

## 2. LeanExplore (independent precomputed semantic index)

```bash
# Uses Python 3.12 or any compatible venv-capable Python.
PYTHON_BIN=python3.12 ./dev/theorem-exploration/install-leanexplore.sh --fetch-assets

./dev/theorem-exploration/run-leanexplore.sh \
  --package Mathlib 'spectral subspace perturbation bound'
./dev/theorem-exploration/run-leanexplore.sh \
  --json --limit 20 --rerank-top 0 'unitarily invariant norm'

# Optional native local MCP (stdio protocol; not an HTTP visualization):
./dev/theorem-exploration/run-leanexplore.sh --mcp
```

`run-leanexplore.sh` uses upstream `lean_explore.search.Service` **directly**,
not `lean-explore search` (the latter talks to a hosted API). It sets
Hugging Face's offline environment flags, so an absent downloaded model
fails rather than silently fetching one during a query. The installer
explicitly fetches the upstream database and the Qwen3 0.6B embedding
and reranking models, using `LEAN_EXPLORE_CACHE_DIR` and `HF_HOME`
under `.build/`. Its upstream `active_version` file is isolated under
`.build/leanexplore/home/` via a dedicated HOME. Reranking can be disabled
with `--rerank-top 0`.

There is no native LeanExplore browser UI in this workflow; the native
local UI is its MCP tool interface, usable by an MCP client. Its prebuilt
index is not a trustworthy declaration-presence test for your pinned
Mathlib/TauCeti/DKPS modules.

## 3. LeanSearch v2 on one RTX 3090 (optional)

The upstream standard deployment expects **two or more GPUs** to run
both 8B embedder and 8B reranker. Its `RetrievalPipeline` has a one-GPU
path: the 8B embedder and cuVS index load on GPU 0, with **zero**
reranker replicas, so searches must send `rerank=false`. Upstream still
loads the reranker **tokenizer** even with no reranker replica. The
installer downloads that tokenizer but not its multi-GB model weights.

```bash
# Ubuntu 24.04: Python 3.12 is preferable for CUDA/cuVS wheels.
PYTHON_BIN=python3.12 ./dev/theorem-exploration/install-leansearch.sh

# Explicitly opt into a large corpus + 8B model download:
PYTHON_BIN=python3.12 ./dev/theorem-exploration/install-leansearch.sh --fetch-assets

# Terminal 1, starts only on 127.0.0.1:
./dev/theorem-exploration/run-leansearch.sh --serve
# http://127.0.0.1:8000/docs (upstream FastAPI docs)

# Terminal 2, always sends rerank=false:
./dev/theorem-exploration/run-leansearch.sh --profile \
  'Davis Kahan spectral subspace perturbation bound'
```

The published cuVS index is **5.74 GB on disk** (including a ~5.17 GB
CAGRA index), and Qwen3-Embedding-8B takes roughly 16 GB in FP16 **before**
activation and CUDA overhead. A 24 GB RTX 3090 is therefore *borderline*:
starting the server may fail with CUDA OOM. The code paths are grounded in
upstream source, but **not GPU-tested here**. This does not implement
quantization, sharding, or fallback to CPU. If the standard cuVS package
cannot be installed for the host CUDA/Python combination, stop and
record that as an experiment outcome rather than changing your Lean pin.

The upstream FastAPI server supports `rerank=true` requests; this
launcher **does not patch its API**. Only use this overlay's query
wrapper (which forces `false`) or explicitly send `rerank: false`
from another client. Do not invoke LeanSearch reasoning mode or its
remote LLM profiles; those are outside the offline experiment.

All queries target the **local** `http://127.0.0.1:8000` service; models
and datasets are fetched only during installation, and the running
server sets Hugging Face offline flags.

## 4. Record comparable probes, without merging results

The curated inputs in `queries.json` pair a *native structural Loogle
query* with a *natural-language semantic query* for each topic. They
are not identical strings because the tools solve different retrieval
problems. The reporter saves each tool's **unaltered JSON**, exit
status, stderr, and elapsed wall time; it does not invent common scores,
proof relationships, or correctness claims.

```bash
python3 dev/theorem-exploration/evaluate.py --backend loogle
python3 dev/theorem-exploration/evaluate.py --backend leanexplore --case sin-theta
python3 dev/theorem-exploration/evaluate.py --backend leansearch --case direct-rotation
# Only after all three are installed and started:
python3 dev/theorem-exploration/evaluate.py
```

Reports are written under `.build/results/`. Inspect names, mathematical
relevance, source signatures, toolchain freshness, and latency yourself.
A missing installation or non-running LeanSearch server appears as a
recorded error rather than a fabricated empty search result.

## Offline and version boundaries

- Initial Git/PyPI/Hugging Face downloads require internet access.
  Runtime entrypoints do not invoke hosted search services or APIs.
- Loogle needs the **same Lean toolchain as the compiled `.olean`s**.
  It uses `lake env` from the actual DKPS checkout; no separate pinned
  Mathlib dataset is involved.
- LeanExplore and LeanSearch use downloaded historical corpora. Their
  local execution does **not** mean they index your local Lean revision.
- If a strict OS-enforced network sandbox is required, put the query
  processes in your existing network-isolated VM/container; this overlay
  configures local-only backends and offline model modes but is not a
  network firewall.
- The Loogle web server and LeanSearch server bind to `127.0.0.1` by
  default; they are not intended for untrusted network exposure.
- The scripts leave all existing proof modules and normal `lake build`
  targets untouched. No persistent agent/hook or service is installed.

## References

- Loogle: https://github.com/nomeata/loogle (README: local Lake project and web server)
- LeanExplore: https://github.com/lean-explore/lean-explore (docs/local-backend.md)
- LeanSearch v2: https://github.com/frenzymath/LeanSearch-v2 (README, pipeline and FastAPI source)
- LeanSearch dataset: https://huggingface.co/datasets/FrenzyMath/lsv2-mathlib-v4.28.0-rc1-cuvs
