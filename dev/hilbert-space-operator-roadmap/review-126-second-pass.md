# Review response — TauCetiRoadmap#126, kim-em, 2026-08-21

Review `4989151648`. Five items. **This note records the repository-side work, which is
complete. The roadmap edits themselves are deliberately not made yet.**

The reviewer's closing note says the eight operator-theory roadmaps are unchanged since
`ceab3470`; verified — `git diff ceab3470 HEAD -- TauCetiRoadmap/OperatorTheory` is empty, and
all five cited line anchors resolve to the right bullets.

---

## Item 1 — resolvent convention. **Fixed in this repository.**

The reviewer asked that Part D consume and generalize
`TauCeti.LinearPMap`'s landed resolvent core rather than introduce its own under the opposite
sign convention. It was worse than reported: our
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Resolvent.lean` declared
`TauCeti.LinearPMap.resolventSet` and `.spectrum` — the *same fully-qualified names* as the
landed module — with `A - z` where the landed one has `lambda • I - A`. No collision fired only
because nothing imported both; `TauCeti.Analysis.Semigroups.Resolvent.Identity` is the single
upstream importer of the resolvent core, and one import away from a duplicate-declaration error.

**The decisive fact is not the duplication — it is that Mathlib agrees with Tau Ceti and we did
not.** `Mathlib/Algebra/Algebra/Spectrum/Basic.lean:64,80` defines
`resolventSet R a = {r | IsUnit (↑ₐ r - a)}` and `resolvent a r = (↑ₐ r - a)⁻¹ʳ` — the
`lambda • I - A` orientation. Our `A - z` was out of step with the library underneath us.

What was done:

| commit | |
|---|---|
| `ed6f0732` | `ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean` — conservative scalar generalization of all **30** landed declarations |
| `c74f01ac` | `RoadmapBridge/TauCetiResolventConservativity.lean` — compiler-checked proof that the generalization recovers every landed real statement |
| `df4c478c` | toolchain bump so the work is against current upstream, not a stale pin |
| `7d23499e` | the migration: local `A - z` core deleted, `ForTauCeti` and `DavisKahan` moved onto the landed convention |
| `daf02d6e` | extraction manifest revalidated by hand |

Three findings worth carrying into the roadmap reply:

1. **`RCLike` is not needed.** All 30 declarations, including the Neumann series and both
   bounded bridges, go through on `NontriviallyNormedField` alone, because `E →L[𝕜] E` is
   already a `NormedAlgebra` over such a field. The roadmap can ask for less than it does.
2. **The bounded bridges are the convention test.** `mem_resolventSet_toPMap_top_iff` and
   `resolvent_toPMap_top` compiled with *no* proof change beyond `ℝ → 𝕜`. Under `A - z` they
   would have needed sign bridging at every use.
3. **Consuming upstream deleted code rather than adding it.** The migration is +770/−782 across
   21 files. `DavisKahan/SpectralTheory/SelfAdjointBorelCalculus.lean` had reimplemented the
   bounded bridge by hand in the opposite sign; routing it through the upstream bridge replaced
   22 lines of proof with 5.

Two statement shape changes, both forced and both faithful over `ℝ`:
`mem_resolventSet_of_norm_mul_lt_one` and its private helper take `‖mu - lambda‖` where upstream
takes `|mu - lambda|`, since the absolute value has no meaning on a general normed field. The
conservativity bridge restates the upstream `|·|` form and derives it, so this is checked rather
than asserted.

### What the roadmap edit still has to say

- SA-D01–D12 restated against `TauCeti.LinearPMap`, one convention throughout, `(λI − A)⁻¹`,
  identity `R(λ) − R(μ) = (μ − λ) R(λ) R(μ)`.
- Cayley and Yosida restated: `1 + 2i R(-i)`, `-n² R(in) - in`, `-n² R(-in) + in`.
- `Suggested.lean` should import the individual Tau Ceti resolvent module and prototype against
  those declarations, dropping its own `resolventSet`/`spectrum`/`resolvent`.
- Retract the claims that Part D depends only on Mathlib and that this layer is absent upstream.
- SA-D02, SA-D10, SA-D12, SA-D13 remain genuine additional targets — upstream has no spectrum
  notion, no resolvent spectral mapping, no closedness, no measurability.
- Consider dropping the `RCLike` requirement per finding 1.
- **Add the maximality result.** Upstream gained `eq_of_le_of_mem_resolventSet` after our pin —
  "if `A ≤ B` and some `λ` is in both resolvent sets then `A = B`" — the step that upgrades
  "`A` is a restriction of the generator" to "`A` *is* the generator". Delivered.

---

## Items 2–5 — roadmap prose only; our implementations are already correct

Verified against the tree. None of the four is in a `Suggested.lean`; all four are README bullets
that drifted from the compiled mathematics.

**Item 2 — MSS-C02–C05 need `0 < r`.** Correct, and our code already has it:
`ForTauCeti/Probability/Moments/SampleMean.lean:88,154,234,255` all take `(hr : 0 < r)`, as do the
downstream copies in `Acharyya2024/SecondMoment.lean:88` and
`DkpsQuench2026/Paper/EvaluationConcentration.lean`. Fix the README bullets.

**Item 3 — SSP-D03 uses the wrong operator.** Correct, and our code uses the right one:
`YuWangSamworth2015/YuWangSamworth2015/Core/Residual.lean:82` defines
`residualColumn j = λⱼ(T) • wⱼ − T wⱼ` — the *population* residual, `T` not `S`. The three
consequences the reviewer describes are all proved there: the cross-term identity at `:89`, the
perturbation decomposition at `:110` (SSP-D11), the population-gap lower bound at `:122`
(SSP-D08), the Frobenius upper bound at `:153` (SSP-D09). The reviewer's 2×2 counterexample
refutes a statement we never proved.

**Item 4 — PA-B28 overstates the 1-D case.** Correct.
`ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:620`,
`principalCosines_rankOne : principalCosines (span 𝕜 {u}) (span 𝕜 {v}) = Finsupp.single 0 ‖⟪u,v⟫‖`.
For orthogonal unit vectors this is `Finsupp.single 0 0 = 0` — true. The reviewer's suggested
wording ("the only potentially nonzero principal cosine") is what the `Finsupp` API already means.

**Item 5 — MSS-C23 needs its positivity hypotheses.** Correct. The general theorems
(`MatrixConcentration.lean:166`, `SampleSecondMoment.lean:118`) take `(hη : 0 < η)`. The
`η = c/(2d)` specialization is **not a theorem anywhere** — it is a docstring remark in our code
too, and the roadmap's "in particular" clause was copied from it. If it is ever stated, it needs
`0 < c` and `0 < d`.

---

## Repository state at the stopping point

`lake build`: 9681/9681, exit 0. Gates at their pre-existing baselines — export check OK,
`check_dependency_layers.py` 14 `GENERIC_IMPORTS_SOURCE` findings, `check_declaration_name_drift.py`
2 findings on `Challenge/YuWangSamworth/Leaderboard.lean`. Neither pre-existing failure is related
to this work.

Known pre-existing conditions, deliberately not folded into the migration:

- 156 Mathlib deprecation *warnings* in the libraries that do not set `warningAsError`
  (DavisKahan 103, DkpsQuench2026 42, Acharyya2025 11). Same six renames as `df4c478c`.
- 57 further occurrences of the words this repository bans from comments, across 29 files
  (27 `axioms`, 17 `axiom`, 12 `sorry`, 1 `axiomatised`). Many are legitimate English usage in
  mathematical prose; the rule bans them anyway so that grep-based detection stays clean. Needs
  its own pass with its own judgement calls.
- `dev/tauceti/extraction-manifest.json` has pre-existing stale rows unrelated to the resolvent
  work. They were left alone; see `daf02d6e`.
