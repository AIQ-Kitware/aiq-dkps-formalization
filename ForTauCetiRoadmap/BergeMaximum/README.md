# Roadmap: Berge's maximum theorem over a fixed compact set

**Topic T22 of the candidate design.** Two modules, no prerequisites. Mathlib has
the hemicontinuity *definitions* and the extreme-value theorem, and no Berge
theorem; this supplies the upper-hemicontinuity half in three usable forms.

## The theorem, and the engine under it

For jointly continuous `g : P → X → ℝ` and a fixed nonempty compact `K ⊆ X`, the
argmin correspondence `M p = {x ∈ K | IsMinOn (g p) K x}` is upper
hemicontinuous, and the value function is continuous:

```lean
theorem upperHemicontinuousAt_isMinOn
    (hK : IsCompact K) (hg : Continuous (Function.uncurry g))
    (p₀ : P) [(𝓝 p₀).IsCountablyGenerated] :
    UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀

theorem continuous_iInf_of_isCompact
    (hK : IsCompact K) (hKne : K.Nonempty) (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ⨅ x : ↥K, g p ↑x)
```

Both come from one lemma, which is the actual content of the topic:

```lean
theorem exists_subseq_tendsto_isMinOn_of_approxMinOn
    (hK : IsCompact K) (hF : Continuous F) (hz : ∀ k, z k ∈ K)
    (hε : ∀ x ∈ K, Tendsto (ε x) atTop (𝓝 0))
    (happrox : ∀ x ∈ K, ∀ k, F (z k) ≤ F x + ε x k) :
    ∃ φ, StrictMono φ ∧ ∃ ψ ∈ K, IsMinOn F K ψ ∧ Tendsto (z ∘ φ) atTop (𝓝 ψ)
```

*A sequence of approximate minimizers in a compact set has a subsequence
converging to a genuine minimizer.* That is the recovery half of the fundamental
theorem of Γ-convergence, and Berge is what you get by feeding it
`ε x k = |g (p k) x − g p₀ x|`.

## Pinned conventions

### Fixed constraint set, said out loud

This is the **fixed-constraint** case: `K` does not vary with the parameter. The
classical Berge theorem allows a parameter-varying constraint correspondence, and
that case is *not* formalized here. The module docstring says so in its first
paragraph, and a roadmap that omitted it would be claiming a stronger theorem than
the library has.

### Three forms, because three consumers want different things

`tendsto_subseq_isMinOn_of_isMinOn` (the closed-graph, sequential form),
`upperHemicontinuousAt_isMinOn` (through Mathlib's own `UpperHemicontinuousAt`,
which needs `X` Hausdorff so the compact `K` is closed), and
`exists_modulus_isMinOn` / `exists_modulus_isMinOn_family` (a uniform `ε`–`δ`
modulus on a metric `P`). The family form measures closeness by a finite family of
continuous invariants rather than the ambient metric — the case where minimizers
are determined only up to a symmetry group, which is why it exists.

### Sequential proofs, deliberately

The uniform-convergence-on-compacts step is proved in the sequential form
actually needed (`tendsto_eval_sub_of_isCompact`), via the subsequence criterion
and sequential compactness, rather than through the compact-open topology. The
hypotheses are correspondingly `FirstCountableTopology` and, where Mathlib's
predicate is used, `T2Space`.

## Existing foundations

Mathlib supplies `IsCompact.exists_isMinOn`, `IsCompact.tendsto_subseq`,
`UpperHemicontinuousAt` in `Mathlib/Topology/Semicontinuity/Hemicontinuity.lean`,
and `IsMinOn`.

A sorry-free staged implementation exists under `ForTauCeti/Topology/`
(`scripts/check_tauceti_roadmap_topics.py --topic T22`). It still requires Tau
Ceti review and migration.

## What remains to land

- **The parameter-varying constraint case.** This is the classical theorem's
  actual generality, and it is the first thing a reviewer who knows Berge will
  ask for. It is not started; the fixed-constraint case is not a step toward it
  so much as the special case that the argmin engine gives for free.
- **The lower-hemicontinuity half**, and hence the maximum theorem proper.
- **Theorem-level acceptance examples**, in Tau Ceti's shape.

The first two are additions, not corrections: nothing stated here weakens.

## Ordering and PR slices

One PR. `ApproxMinimizer` is the engine and `Berge` is its four corollaries; they
are 144 and 346 lines and the second is unreadable without the first.

## Provenance and coordination

Both modules were authored in place in this repository (Davis–Kahan/DKPS
formalization, Kitware, Inc.) and lived in `ForMathlib` until 2026-07-29, when
lane FM-RETIRE retired that library into `ForTauCeti`, renaming the namespace
`ForMathlib → TauCeti`. Three of these theorems are pinned as *data* in
`comparator/pending-berge.json` and named in
`Challenge/MathlibPending/Berge/Leaderboard.lean`; they were repointed with the
rename, and `Challenge` is outside `defaultTargets`, so a rename here needs
`scripts/check_declaration_name_drift.py` and `lake build Challenge` rather than a
green default build.

T22 is rung **U** of `dev/tauceti/submission-ladder.md`, the last rung. Nothing in
the library depends on it.

Written 2026-07-30 by `jon (yardrat)` under lane ROADMAP-WRITE, claimed together
with T21 because the two share that FM-RETIRE provenance.
