# Bridges into the later proofs

These four lectures fill teaching gaps exposed by the matching and perturbation
walkthroughs. They are implemented lessons, not placeholders. The dependency
edges in `lectures/index.yaml` describe helpful preparation, not a claim that a
Lean declaration imports another lecture's companion file.

| Stable lecture ID | What it explains | Where it helps |
| --- | --- | --- |
| `invariant_blocks` | Invariant versus reducing spaces; input/output meaning of blocks; self-adjoint complement argument; projection commutation | Rayleigh–Ritz blocks, PVM selections, stationarity and simultaneous-block arguments |
| `principal_angles` | Basis freedom; overlap SVD; principal pairs; sine as perpendicular error | YWS geometry, direct rotation, matching vertices and repeated angles |
| `trace_gradients` | Entrywise pairing; trace cyclicity; derivative representation; restricted tests; the skew sign | Feasible variations, trace-pairing derivatives, gradient-compression tests |
| `uniform_minima` | One error band for every candidate; the two minimum comparisons; moving-dip and moving-minimizer examples | Passing the smooth matching minimum to the trace-norm endpoint |

Each includes authored narration, topic-specific visual explanations, four
five-second study questions, a separate computation bonus, symbolic facts and
compiled Lean applications, source/convention notes, and external learning
links. Existing order numbers are preserved; the organizer allocates gaps.

Further useful bridges include a real quarter-turn as complex multiplication,
simultaneous invariant spaces for several maps, two-dimensional projection
blocks, and spectral functional calculus for differentiating matrix costs.
Those are not claimed to be implemented by these four lectures. The current
invariant-block lesson introduces the common-preservation requirement; it does
not prove the matching proof's full simultaneous reduction.
