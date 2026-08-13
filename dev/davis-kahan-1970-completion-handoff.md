# Davis--Kahan 1970 completion handoff — mathematical and architectural edition

> **Historical checkpoint, retained as source-audit evidence.** Current status and policy live in `AGENTS.md`, the maintained Davis--Kahan census/frontier, and the distributable source specification. Re-measure current HEAD before acting on any status claim below.
>
> **Superseded on the completion question, updated after the hostile Appendix-scope audit.** All 29 counted results of the maintained denominator are terminal on all three axes. The first `S2-tan-theta` closure still kept the Ritz compression bounded; the Appendix-complete closure is now `TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_exact` plus its real sibling, which allow `A_0` itself to be unbounded. The work-list sections below are historical. The architectural sections — complexification as a proof technique, `LinearPMap` as the canonical unbounded carrier, paper facades exposing paper hypotheses — remain current guidance.

State inspected 2026-08-09 from checkpoint HEAD `69d1655a` (`main`, clean working tree).

This document is for an agent taking over the remaining Davis--Kahan 1970 campaign without prior context. It is intentionally more than a work list: it records the mathematical architecture, the proof routes already discovered, the routes already falsified, and the reusable infrastructure that now exists so that the next agent does not have to rediscover the campaign's hardest lessons.

Read `docs/planning/historical/coordinator-subagent-workflow-2026-08-09.md` for the mechanical coordinator loop and `AGENTS.md` for repository policy. Before substantial work under `ForTauCeti/Analysis/InnerProductSpace/`, also read `dev/lean-proof-engineering-lessons.md`.

The source census is `dev/davis-kahan-1970-full-source-census.json`. It is the durable record of source coverage, but do not treat any single status field, blocker name, or prose note as infallible. Re-measure the current declarations and current HEAD before acting. In particular, this checkpoint already contains work newer than the previous completion handoff, and one row (`DK-8.1-thm`) is still marked `compiled_exact` while also carrying a genuine real-scalar scope blocker.

---

## 0. What we are optimizing for

The acceptance target is a faithful formalization of the mathematical content of Davis--Kahan 1970. The architectural target is an operator-theory library that remains coherent after the paper is finished.

These are not competing goals. The usual good outcome is:

1. identify the paper obligation precisely;
2. search Tau Ceti, `ForTauCeti`, and the existing Davis--Kahan development for the mathematical concept;
3. if the missing statement is genuinely reusable operator theory, prove it once at the lowest natural layer;
4. consume it from a thin source-facing theorem whose hypotheses and conclusion match the paper;
5. register the paper endpoint in the census/frontier only after the declaration exists and compiles.

The operator-theory roadmap is therefore a **design compass**, not a second bureaucratic checklist. `ForTauCeti` is a permanent mathematical product of this repository; `AGENTS.md` explicitly asks that it be held to the "platonic ideal" roadmap standard. When a Davis--Kahan proof naturally exposes a missing general theorem, fixing that abstraction seam is part of good Davis--Kahan work. Conversely, do not turn one source obligation into an unrelated research project merely because a neighboring roadmap signature exists.

Concrete operating principles:

* **General mathematics goes at the lowest reusable layer.** If a proof says nothing about Davis--Kahan, Section numbers, or paper-specific records, it probably belongs in `ForTauCeti/`.
* **Paper facades should expose paper hypotheses.** Internal records are useful implementation devices, but a source endpoint is not complete if its caller is required to supply a branch selection, spectral orientation, smallness condition, or conclusion-like witness that the paper itself proves.
* **`LinearPMap` is the canonical carrier for unbounded operators.** The local `ClosedOperator` compatibility layer is transitional. New foundational work should normally strengthen `LinearPMap`, not deepen the duplicate carrier.
* **Complexification is a proof technique, not the default architecture.** First determine whether the proof is already scalar-generic. If an essential ingredient is genuinely complex-only, transport the smallest necessary portion and descend the actual mathematical object, not an arbitrary existential witness.
* **Mission boundaries are planning boundaries, not architectural walls.** It is correct to repair a missing reusable theorem immediately below the current source theorem. It is not necessary to implement an unrelated adjacent roadmap item.
* **Do not modify `external/TauCeti/` or the roadmap checkout from this repository.** They are references. Reusable mathematics needed here lives in `ForTauCeti/`.
* **Do not frame code as "work to push upstream".** Make it good mathematics locally. Other projects decide what they consume.
* **Prefer one canonical spelling.** A compatibility alias may be useful during migration, but the end state should not contain two independent representations of the same operator-theory concept.

A useful litmus test is: if the paper disappeared tomorrow, would this lemma still be a natural theorem about Hilbert-space operators? If yes, strongly consider `ForTauCeti`. If the statement exists only to match a numbered source claim, keep the endpoint in `DavisKahan/Sources/DavisKahan1970/`.

---

## 1. Current checkpoint and what changed since the previous handoff

Current checkpoint:

* HEAD `69d1655a`, clean tree.
* 49 census rows.
* Status counts currently serialized in the census:

  * 26 `compiled_exact`;
  * 18 `compiled_specialization`;
  * 1 `refuted_as_transcribed`;
  * 1 `resolved_by_modern_development`;
  * 3 `not_a_completion_obligation`.
* 23 rows currently contain a `scope_gap` field.
* The stale global blocker `real-scalar-infinite-dimensional-scope` is still attached to 8 rows, but its name no longer describes most of them.
* Static census check on this checkpoint reports `46/49` proved in the default build and 3 paper-open questions as not applicable; Lean declaration resolution was not rerun in this inspection environment.
* Static frontier check reports `83/83` named declarations textually present and `18/18` required nonterminal census rows mapped. Treat that as a consistency check, not a completeness proof: `DK-8.1-thm` is the concrete example of a row whose status is `compiled_exact` while a real-scalar obligation remains.
* Dependency-layer checker remains at the existing baseline of 7 backwards-dependency violations, all in the beam/form-method area. Library-structure checks 1, 2, 4, and 5 are green; check 3 retains 16 pre-existing Experimental-structure violations.

Two recent advances materially change the remaining proof graph.

### 1.1 M38 landed: Section 1 equations (1.12) and (1.13)

Commit `3902b73b` formalized the Section 1 Ky Fan/Rayleigh--Ritz suprema. The critical conceptual correction is that the printed `sup` is **not a maximum in infinite dimension**. For the diagonal operator with entries approaching one from below, e.g. `diag(1 - 1/n)`, every approximation number is one, so the Ky Fan `ν`-gauge is `ν`, but no finite-dimensional compression attains it. The correct formal shape is `IsLUB`.

Current public source declarations include:

* `equation1_12`;
* `equation1_13_compressions`;
* `equation1_13_reSum`;
* the compression monotonicity lemmas used for their `≤` halves.

The approximate-attaining engine is now available and is exactly the form needed by the Appendix to Section 6. Do not reintroduce an `∃ Ω, ... = ...` maximizer statement.

The codomain-room narrowing that `(1.12)` used to carry has been removed: `equation1_12` now assumes only `hE`, an orthonormal `ν`-tuple in the *domain*, which is exactly the nonemptiness of the family the printed supremum ranges over. `(1.13)`'s two room hypotheses stay, because the printed `(1.13)` quantifies over projectors on both sides. See mission A below for what was actually done.

### 1.2 M36 foundation landed: real spectral ranges and real bounded gap branches

The real-scalar Section 8 problem is no longer starting from scratch. The following operator-theory infrastructure has landed:

* real spectral ranges for self-adjoint `LinearPMap`s, including domain preservation, commutation, complement ranges, and reducing-subspace structure;
* complex spectral-range complement/reduction facts at the same canonical layer;
* exact complexification of a descended real `LinearPMap` spectral range;
* exact subspace geometry transport under complexification;
* exact form and invariant-subspace transport under complexification;
* a **bounded real spectral branch across a genuine gap** obtained by descending the actual complex bounded spectral projection.

The newest module is

`DavisKahan/SpectralTheory/Complexification/BoundedGapProjection.lean`.

Its important declarations are:

* `conjugateOperator_boundedSelfAdjointSpectralProjection_Iic_complexify`;
* `realBoundedSpectralProjectionIicOfGap`;
* `complexify_realBoundedSpectralProjectionIicOfGap`;
* `realBoundedSpectralProjectionIicOfGap_idem`;
* `realBoundedSpectralSubspaceIicOfGap`;
* `complexifySubmodule_realBoundedSpectralSubspaceIicOfGap`.

The key mathematics is the gap. The bounded Borel spectral projection is complex-only, but when

`realSpectrum B ⊆ Iic α ∪ Ici (α + δ)`, `δ > 0`,

the indicator of `Iic α` agrees on the spectrum with a continuous **real-valued** gap symbol. Continuous functional calculus is compatible with canonical conjugation of the complexification, so the actual complex spectral projection is conjugation-fixed and descends to a real projection. Its real range complexifies exactly to the complex source branch. This is the missing nonmechanical ingredient for real Theorem 8.1.

Do not replace this with "complexify, obtain some reducing subspace, take real parts". An arbitrary complex reducing subspace need not descend. We now descend the **canonical spectral projection itself**.

---

## 2. Mathematical dictionary and recurring objects

A next agent should be comfortable with these correspondences before proving anything.

### 2.1 Two subspaces and their angles

For closed subspaces `U,V` with orthogonal projections `P,Q`:

* `directedGap U V` is one directed sine quantity, morally `‖P_{V⊥}|_U‖`;
* `subspaceGap U V = ‖P-Q‖` is the symmetric gap, the sine of the maximal ambient angle;
* the paper has two directed angle operators, usually `Θ₀` and `Θ₁`, associated with the two crossed blocks;
* the ambient Hermitian angle is represented in the complex tree by `paperAngleOperatorC U V` and in the real tree by its real counterpart;
* cosine/sine blocks in the Halmos decomposition carry the principal-angle data.

The crossed defect spaces are the top-angle (`π/2`) pieces:

* `U ∩ V⊥`;
* `U⊥ ∩ V`.

Standing assumption (3.5) equalizes their dimensions. This is the missing ingredient behind several places where the finite-dimensional development currently uses equality of ambient finranks to turn a directed bound into a symmetric bound.

### 2.2 Approximation numbers, Ky Fan gauges, and UI norms

The project deliberately uses approximation numbers as the dimension-free singular-value language:

`a_n(T) = T.approximationNumber n`.

The paper's `ν`-norm is represented by

`kyFanApproximationGauge ν T = Σ_{n<ν} a_n(T)`.

This is defined for every bounded operator, including noncompact operators. When a rectangular singular-value list exists it agrees with the corresponding Ky Fan prefix.

For arbitrary unitarily invariant norms, the most robust proof architecture is usually:

1. prove every Ky Fan prefix inequality;
2. invoke the Fan-dominance theorem for `PaperUnitaryInvariantNorm` or the relevant ideal family.

Do not attempt to transport a `KyFanDominantIdealFamily` object across scalar fields. The family is instantiated per field and there is no `gauge_complexify`. Transport approximation numbers/Ky Fan inequalities and rebuild the norm conclusion over the target field.

### 2.3 Real spectrum

When real and complex operators interact, use

`TauCeti.DavisKahan.Experimental.Foundation.realSpectrum`.

Do not rewrite `spectrum ℝ` through complexification. The repository has a real-algebra module diamond (`Algebra.complexToReal` versus the real structure on `RealComplexification`) that makes those expressions propositionally related but not definitionally identical.

`realSpectrum_complexify` is the correct bridge for bounded real operators.

### 2.4 Unbounded operators

The canonical unbounded carrier is Mathlib `LinearPMap`. Existing `DKClosedOperator` / `ClosedOperator` wrappers are compatibility layers. If a new theorem is fundamentally about domains, graph closure, spectral projections, or self-adjoint partial maps, prefer the `LinearPMap` layer and adapt outward.

In particular, recent spectral cutoff and spectral reduction work is already `LinearPMap`-native. Reuse it.

### 2.5 Complexification transport that is already available

For real subspaces/operators, the current complexification layer includes exact facts of the following shape:

* `starProjection_complexifySubmodule`;
* `complexifySubmodule_orthogonal`;
* `subspaceGap_complexifySubmodule`;
* `directedGap_complexifySubmodule`;
* `isQuarterAcute_complexifySubmodule_iff`;
* `complexify_reduces_iff`;
* `re_inner_complexify`;
* `re_inner_le_of_mem_complexifySubmodule`;
* `le_re_inner_of_mem_complexifySubmodule`;
* `mapsTo_complexifySubmodule` and orthogonal variants;
* `range_complexify`;
* `complexifySubmodule_realSpecRange` for the unbounded spectral range;
* `complexifySubmodule_realBoundedSpectralSubspaceIicOfGap` for the actual bounded branch across a gap.

Use these exact bridges before inventing new transport records.

---

## 3. Completed foundations that remaining proofs should reuse

### 3.1 M30: branch-free bounded `tan 2Θ` with sharp factor two

The bounded infinite-dimensional double-angle tangent problem is solved. The important public chain is:

* `tanTwoTheta_directedCorner_residual_all_kyFan_branchFree`;
* `tanTwoTheta_directedCorner_residual_all_kyFan_branchFree_upper`;
* `tanTwoTheta_wholeSpace_all_kyFan_branchFree`;
* `tanTwoTheta_wholeSpace_paperUINorm_branchFree`.

The proof is a model for the unbounded Ky Fan problem. Its essential ingredients are:

* the **actual rectangular tangent corner** `T`;

* signed cosine blocks, not positive cosine branches;

* Gram identities

  `C₀† C₀ (1 + T†T) = 1`,

  `C₁† C₁ (1 + TT†) = 1`;

* Section 7 reflection equation

  `(C₁ T) A₀ - A₁ (C₁ T) = B C₀ + C₁ B`;

* approximate leading singular families;

* polar isometries absorbing the sign of `cos 2θ`;

* `sum_abs_le_kyFanApproximationGauge_of_orthonormal` applied to absolute real inner products;

* epsilon-to-zero passage.

The factor `2` comes once from the two residual pairings. Lower-to-upper corner transport is by adjoint/Ky Fan invariance and adds **no second factor two**. Preserve that invariant in any unbounded analogue.

### 3.2 Section 6 single-angle unbounded tangent passage

The single-angle tangent theorem is already available at unbounded ambient scope, arbitrary trial dimension, and UI-norm scope. Do not rebuild its cutoff/Fan machinery for unrelated scalar work.

The infinite-trial proof uses min--max localization and almost-invariant spectral-band enlargement rather than literally reproducing equations (6.7)--(6.11). The theorem conclusion is therefore available even though those displayed identities themselves are not all source-numbered declarations.

### 3.3 Unbounded double-angle pole exclusion and operator-norm tangent

`ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/` now contains:

* `ReflectionBlocks.lean` — reflection block identities from `Z²=1`;
* `UnboundedReflection.lean` — domain preservation and domain-correct equation (7.6);
* `UnboundedPole.lean` — branch-free pole exclusion;
* `SpectralCutoff.lean` — actual self-adjoint spectral cutoff family.

For a self-adjoint `LinearPMap A`, reducing low spectral subspace `U`, gap `δ=b-a>0`, bounded fully off-diagonal perturbation `B`, and commuting reflection, the pole theorem gives on `U`

`‖Sx‖ ≤ [2‖B‖ / sqrt(δ²+4‖B‖²)] ‖x‖`,

`[δ / sqrt(δ²+4‖B‖²)] ‖x‖ ≤ ‖Cx‖`.

Thus `|cos 2Θ₀|` is uniformly bounded below before any tangent quotient is formed.

`tanTwoTheta_unbounded_residual_opNorm` packages the `ν=1` consequence

`δ |tan 2θ| ≤ 2 ‖B‖`

with the sharp constant and without choosing an acute/obtuse branch.

The open problem is the Ky Fan `ν≥2` / arbitrary UI-norm analogue, described in detail in mission F.

### 3.4 Real single- and double-angle sine/tangent infrastructure

Do not trust old comments saying whole trees are complex-only. Several real axes were closed by M32--M35. In particular:

* ambient and directed real `tan Θ` endpoints exist;
* real unbounded single-angle tangent endpoints exist;
* ambient and directed real `sin 2Θ` UI-norm endpoints exist;
* real angle/operator complexification machinery exists.

The remaining rows often retain old historical notes describing obstacles that have since been routed around. Read the most recent paragraph of each census row and inspect the signatures.

---

## 4. The high-leverage dependency graph

Do not think of the remaining work as 18 unrelated `compiled_specialization` rows. Several mathematical assets close multiple rows.

### Shared unlock S: standing assumption (3.5) and equality of directed gaps

Prove a reusable theorem expressing the effect of

`dim(U ∩ V⊥) = dim(U⊥ ∩ V)`.

At minimum, this should imply

`subspaceGap U V = directedGap U V`

(or equality of the two directed gaps, from which the symmetric formula follows).

This feeds:

* `DK-8.2-thm`: replace finite-dimensional/equal-finrank conversion by the paper's actual standing assumption;
* `S2-tan-theta`: derive ambient transversality/acuteness from the already-derived directed estimate under (1.5)+(3.5);
* the Section 3 narrative around why (1.5) does **not** imply (3.5), whose bilateral-shift example belongs to `DK-3.2-prop`.

A stronger theorem identifying the crossed sine blocks' singular data under a `CrossedDefectsEquivalent` hypothesis may be worthwhile if it is clean, because the paper explicitly reasons through `S₀` and `S₁`. But for the norm-only uses, do not insist on a full singular-sequence classification if a direct defect/generic decomposition proof is shorter and reusable.

### Shared unlock T: unbounded branch-free Ky Fan `tan 2Θ`

Prove the unbounded residual theorem at every Ky Fan prefix, then Fan dominance.

This closes or materially advances:

* `S2-unbounded-scope`;
* the substantive double-angle part of `DK-6-appendix`;
* the missing 2-norm sentence of `(9.7)` on `DK-9.5-9.7`.

Do this once in the correct general source module. The beam file should merely instantiate it.

### Shared unlock R: real Theorem 8.1 branch

The bounded-gap descent infrastructure in `e030479d` makes this a focused source theorem now. Once real Theorem 8.1 exists, the scalar part of Theorem 8.2 can be transported much more cleanly.

### Shared unlock I: functional-calculus intertwiners

Section 3 still has several obligations where the paper says, in effect,

`A X = X B  =>  f(A) X = X f(B)`.

Before proving a local spectral theorem, inspect

`ForTauCeti/Analysis/InnerProductSpace/SeparatedIntertwiner.lean`, especially `cfcHom_intertwines`.

A well-shaped rectangular/self-adjoint intertwining lemma may unlock both the Proposition 3.1 characterization and the Theorem 3.1 realization cleanup.

---

## 5. Detailed remaining missions and proof strategies

### A. `S1-ui-norms`: remove the codomain-room hypothesis from equation (1.12) -- DONE

**Status:** closed. `equation1_12` now reads

`equation1_12 (K : E →L[ℂ] F) {ν : ℕ} (hE : ∃ x : Fin ν → E, Orthonormal ℂ x)`

with the same `IsLUB` conclusion, the same indexing set, and the same right-hand side. There is no `hF` and no replacement hypothesis: no `[FiniteDimensional]`, no compactness, no rank bound. `equation1_13_compressions` and `equation1_13_reSum` are untouched and keep both room hypotheses, which for printed `(1.13)` are the printed claim rather than an addition to it.

**The route that worked was not the one recorded here before.** The previous entry proposed running the attaining argument at `ν' = min ν (finrank W')`, citing `rectangularKyFanSum_eq_minFinrank_of_minFinrank_le`. That lemma is in the *finite-dimensional* singular-value layer: it is about `rectangularKyFanSum` of an `A : E →ₗ[𝕜] F` with `[FiniteDimensional 𝕜 E]` and `[FiniteDimensional 𝕜 F]` as section instances (`ForTauCeti/Analysis/InnerProductSpace/SchattenNorm.lean`). `(1.12)` is about `kyFanApproximationGauge` of a bounded `K : E →L[ℂ] F` on possibly infinite-dimensional spaces, so that lemma does not apply, and the route also needed an orthonormal-extension step that was never proved.

**What was done instead: pad the codomain.** `hF` is an artifact of the attaining engine `exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner_complex`, which returns an orthonormal `ν`-tuple in *each* space and therefore cannot run when `dim F < ν`. But the conclusion of `(1.12)` never mentions the codomain. So replace `F` by the `L²` sum `WithLp 2 (F × EuclideanSpace ℂ (Fin ν))`, which has room for `ν` orthonormal vectors no matter what `F` is, along the inclusion `ι` of `F` as the first summand; the projection back onto that summand is a left inverse, and both maps are contractions. Every Ky Fan gauge is blind to that substitution, so the ε-bound proved in the padded space is a bound in `F`. No case split on the dimension of `F` is needed, and the argument is uniform.

The general fact this rests on is proved once in `ForTauCeti`, at the lowest layer where it is expressible, and consumed by `:=`:

* `ContinuousLinearMap.approximationNumber_comp_eq_of_leftInverse` (`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean`) -- over an arbitrary nontrivially normed field, with no inner product, completeness, or dimension hypothesis: if `‖ι‖ ≤ 1`, `‖π‖ ≤ 1` and `π ∘ ι = id`, then `(ι ∘L T).approximationNumber n = T.approximationNumber n`. Both ideal inequalities apply and the left inverse closes the loop.
* `ContinuousLinearMap.kyFanGauge_comp_eq_of_leftInverse` (`.../ApproximationNumber/KyFan.lean`) -- the same statement summed over the prefix.
* `TauCeti.ApproximationNumber.kyFanApproximationGauge_comp_eq_of_leftInverse` (`.../ApproximationNumber/Core.lean`) -- the mirror in the `kyFanApproximationGauge` spelling the source facade uses.

Files touched:

* `DavisKahan/Sources/DavisKahan1970/Section1UnitaryInvariantNorms.lean`;
* the three `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/` modules named above.

Do **not** replace `IsLUB` by an attained maximum; that statement remains false in infinite dimensions for the reason recorded in the module docstring.

---

### B. M36 / `DK-8.1-thm`: Theorem 8.1 over real Hilbert spaces

**Status:** complex source theorem is complete and strong; real canonical-branch descent infrastructure is now complete. The census status is misleadingly `compiled_exact` while this real scope gap remains.

This should be the next M36 source theorem, not another operator-theory detour.

#### B.1 Complex theorem to reuse

`DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean` contains:

* `canonicalLowBranch`;
* `Theorem81Conclusion`;
* `theorem8_1_canonicalBranch`;
* `theorem8_1_eq_canonicalBranch_of_maximalAngle_le`;
* `theorem8_1_maximalAngle_le_iff_spectrumIn`.

The source theorem assumes only the printed data:

* `A` self-adjoint;
* `P` invariant under `A` (self-adjointness then gives reduction);
* form upper bound `A ≤ α` on `P`;
* form lower bound `A ≥ α+δ` on `P⊥`;
* `H` self-adjoint;
* `H` fully off-diagonal, mapping `P -> P⊥` and `P⊥ -> P`;
* `δ>0`.

It proves spectral repulsion, canonical branch reduction, sharp form bounds, both restricted spectral orientations, strict quarter-acuteness, and hence maximal angle `< π/4`. The uniqueness theorem uses only the printed closed quarter-angle hypothesis.

#### B.2 Real existence theorem: recommended construction

Let real data be `A_R,H_R,P_R,α,δ` with the exact real analogues of the printed hypotheses.

1. **Complexify the operators and subspace.**

   Set `A_C = complexify A_R`, `H_C = complexify H_R`, `P_C = complexifySubmodule P_R`.

   Use:

   * `complexify_isSelfAdjoint_iff`;
   * `mapsTo_complexifySubmodule` and `mapsTo_orthogonal_complexifySubmodule`;
   * `re_inner_le_of_mem_complexifySubmodule`;
   * `le_re_inner_of_mem_complexifySubmodule`.

   This should transfer every source hypothesis with no constant loss.

2. **Apply the complex source theorem.**

   Invoke `theorem8_1_canonicalBranch A_C H_C P_C ...`.

   Obtain the complex conclusion `hC`, especially

   `hC.spectral_repulsion : realSpectrum (A_C+H_C) ⊆ Iic α ∪ Ici (α+δ)`.

3. **Pull the gap back to the real perturbed operator.**

   Rewrite `complexify (A_R+H_R)` using `complexify_add`, and use `realSpectrum_complexify` to derive

   `hgapR : realSpectrum (A_R+H_R) ⊆ Iic α ∪ Ici (α+δ)`.

4. **Define the real canonical branch using the new infrastructure.**

   Let

   `Q_R := realBoundedSpectralSubspaceIicOfGap (A_R+H_R) (hA.add hH) α δ hδ hgapR`.

   This is the actual real spectral branch, not an arbitrary reducing subspace.

5. **Identify its complexification with the complex source branch.**

   Use

   `complexifySubmodule_realBoundedSpectralSubspaceIicOfGap`.

   Its right side is precisely the bounded spectral subspace used by `canonicalLowBranch`, modulo the straightforward `complexify_add` rewrite and the self-adjoint witness spelling.

6. **Pull geometric conclusions back exactly.**

   * reduction: `complexify_reduces_iff`;
   * quarter-acuteness: `isQuarterAcute_complexifySubmodule_iff`;
   * subspace gap/maximal-angle scalar if needed: `subspaceGap_complexifySubmodule`;
   * orthogonal complement: `complexifySubmodule_orthogonal`.

7. **Pull form inequalities back by testing real vectors.**

   For `x∈Q_R`, embed `x` as `ofReal x`, use the complex branch-form inequality, then simplify `re_inner_complexify` / `inner_ofReal` and norm preservation. Do the complement similarly.

This should give a real analogue of `Theorem81Conclusion`, or a source-facing real theorem with the same fields. If a generic `Theorem81Conclusion` over `RCLike` is clean after the proof is known, that may be preferable, but do not force a large refactor merely for a type parameter.

#### B.3 Spectral orientation over `ℝ`

`SpectrumIn` itself is scalar-generic, but the convenient form-bound-to-spectrum lemmas currently live in the complex source theorem. There are two good routes:

* **Preferred if clean:** promote/generalize the reusable implication "reducing subspace + self-adjoint form bound => restricted real spectrum lies in half-line" to an `RCLike` spectral-order layer, and make both real and complex source theorems consume it.
* **Fallback:** prove exact restricted-spectrum transport through complexification, then pull the existing complex `SpectrumIn` fields back.

Do not duplicate a long Section 8-specific spectral proof if the proposition is scalar-generic operator theory.

#### B.4 Real uniqueness: transport, do not replay the complex cfc proof

For a real reducing `M_R` satisfying `maximalAngle P_R M_R ≤ π/4`:

1. complexify `M_R`;
2. transport reduction and angle exactly;
3. apply complex `theorem8_1_eq_canonicalBranch_of_maximalAngle_le`;
4. identify the complex canonical branch with `complexifySubmodule Q_R` using the new bounded-gap theorem;
5. conclude `M_R=Q_R` by submodule extensionality and `ofReal_mem_complexifySubmodule_iff`.

This is considerably cleaner than reproducing the complex uniqueness proof, whose core is commuting a reducing projection with the cfc branch projection.

#### B.5 Real characterization iff

Once real existence/uniqueness and spectral-orientation transport exist, the printed iff should follow by the same high-level structure as the complex theorem. If a restricted-spectrum complexification theorem was introduced for B.3, reuse it here.

**Paper-owned finite-dimensionality:** The finite-dimensional restriction on Theorem 8.1(iii)'s symmetric-gauge statement is part of the paper. Do not count it as a gap to remove unless a stronger theorem is useful independently.

---

### C. Shared `(3.5)` geometry: `DK-8.2-thm` and ambient `tan Θ`

This should probably be one reusable geometry mission followed by thin source wrappers.

The standing assumption is

`dim(U ∩ V⊥) = dim(U⊥ ∩ V)`.

The paper uses it to ensure the two directed angle sides carry compatible singular data. The current infinite-dimensional source path has a directed estimate, but conversion to the symmetric maximal angle still often uses finite-dimensional finrank equality.

#### C.1 Minimal theorem needed

Prove under (3.5):

`subspaceGap U V = directedGap U V`.

Depending existing conventions, it may be cleaner first to prove equality of the two directed gaps

`directedGap U V = directedGap V U`.

Since symmetric gap is the max of the two directions, equality immediately identifies it with either one.

#### C.2 Mathematical decomposition

Use the Halmos decomposition into:

* common pieces;
* crossed defect pieces `U∩V⊥` and `U⊥∩V`;
* generic position.

On the generic part the two crossed sine blocks are adjoint/polar partners and carry the same nonzero singular data. Any asymmetry in the **norm** can only come from a top singular value `1` contributed by a crossed defect. Under (3.5), one crossed defect is nonzero iff the other is nonzero (indeed their dimensions agree), so either both directed gaps are `1`, or neither has the defect `1` block and the generic norms agree.

That proof may be much shorter than formalizing equality of every approximation number. If a clean theorem already expresses a `CrossedDefectsEquivalent` and generic sine-block unitary equivalence, use it.

A stronger reusable endpoint, if natural, is that the two directed sine blocks are equisingular under a crossed-defect equivalence. That would align very closely with the paper and could support later UI-norm statements.

#### C.3 Apply to `DK-8.2-thm`

The current dimension-free source theorem gives

`directedGap P Q < sqrt 2 / 2`.

Under (3.5), replace directed gap with `subspaceGap`, then use the existing maximal-angle dictionary to get

`Θ < π/4`

without `[FiniteDimensional]` or `finrank P = finrank Q`.

Do not use the recorded infinite-dimensional counterexample unless it satisfies (3.5); it does not.

#### C.4 Apply to `S2-tan-theta`

The ambient `tan Θ` theorem still asks explicitly for transversality/acuteness, whereas the printed theorem derives it under the standing assumptions. The directed version already has `isTransverse_of_tanThetaIntervalGap`.

Use (1.5) to obtain the directed bound/transversality on `Θ₀`; use (3.5) / equality of directed sides to identify the ambient sine norm with the directed one; conclude `‖sin Θ‖<1` and feed the existing ambient tangent theorem. Do not reprove the tangent estimate itself.

#### C.5 `DK-8.2-thm` norm and scalar axes

Separate from the dimension issue:

* restate the inherited `sin 2Θ` conclusions at every source unitarily invariant norm under the 8.2 hypotheses; the current source surface exposes only operator-norm versions;
* after real Theorem 8.1 lands, transport the real 8.2 branch argument through the same complexification infrastructure.

The residual/half-gap proofs already exist. Avoid exposing `PerturbationHalfGapBridge` or similar conclusion-like internal records as the source theorem.

---

### D. Section 3: direct rotations, classification, realization, and eigenvector geometry

These rows are related but not identical. The common theme is to reuse Halmos decomposition and functional-calculus intertwiners rather than transport arbitrary complex existential witnesses.

#### D.1 `DK-3.1-prop`: printed characterization by property (i) alone

Existence and uniqueness are already exact over both `ℂ` and `ℝ`. The remaining defect is the third printed clause.

Current characterization theorems still assume equation (3.8), essentially the square/reflection-product identity. The paper does **not** assume that identity in the characterization direction. It starts from a unitary/orthogonal `W` carrying `U` to `V` with both diagonal blocks accretive.

Write `W` in the `U⊕U⊥` / `V⊕V⊥` block form with cosine blocks `C₀,C₁` and crossed blocks `S₀,S₁`. The paper's route is:

1. derive

   `C₀² S₁ = S₁ C₁²`

   from the block equations corresponding to unitarity and intertwining;
2. use continuous functional calculus intertwining to obtain

   `f(C₀²) S₁ = S₁ f(C₁²)`;
3. choose `f(t)=sqrt t`, using positivity of the cosine blocks, to get

   `C₀ S₁ = S₁ C₁`;
4. use density of `Range C₁` in the acute case to conclude the desired crossed-block adjoint relation `S₁ = S₀*`;
5. identify `W` with the principal direct rotation by the already-proved uniqueness result.

Before building a local cfc lemma, inspect

`ForTauCeti/Analysis/InnerProductSpace/SeparatedIntertwiner.lean`, especially `cfcHom_intertwines`.

The likely reusable abstraction is a rectangular intertwiner between two self-adjoint positive operators. If its existing theorem already has the right shape, instantiate it. If not, add the smallest general theorem needed there.

Do **not** smuggle equation (3.8) back into the implication; doing so proves the already-known stronger-hypothesis characterization, not the source clause.

#### D.2 `DK-3.2-prop`: nonacute existence/nonuniqueness and the bilateral-shift remark

Three pieces remain.

**Actual nonuniqueness.** The repository already parameterizes nonacute direct rotations by an isometric equivalence of crossed defect spaces; `proposition3_2_parameterized_nonuniqueness` is injective in that parameter. To turn this into the source's literal nonuniqueness statement, exhibit two distinct parameters when the crossed defect is nonzero. The obvious pair is `J` and `-J`; check the scalar and nontriviality hypotheses carefully. Injectivity of the builder then gives distinct direct rotations.

Do not claim every formally "nonacute" configuration has two parameters before checking the exact definition: if both crossed defect spaces vanish, the parameter space can degenerate. Align the theorem with the source's actual nonunique case.

**Bilateral shift example.** Formalize the remark on `ℓ²(ℤ)` that separates (1.5) from (3.5). The intended geometry is a pair of shift-related half-space subspaces for which the bilateral shift realizes the unitary equivalence required by (1.4)/(1.5), while the two crossed defects have unequal dimensions (one is zero and the other one-dimensional, depending indexing convention). This is also the canonical warning that equality of two infinite ambient dimensions says nothing about equality of crossed defect dimensions.

**Real scalar form.** Do not descend an arbitrary complex defect isometry by taking real parts. Either:

* generalize the algebraic/polar construction of `Section3Nonacute` to `RCLike` if its ingredients are already scalar-generic; or
* build the real construction natively from a real crossed-defect isometric equivalence and the existing real principal/polar factors.

Search `Geometry/Polar/Section3Nonacute.lean`, `GenericRotationPredicates.lean`, and the real direct-rotation modules before choosing.

#### D.3 `DK-3.1-thm`: real classification and cfc cleanup

The complex classification/uniqueness/realization theorem is substantially complete. The remaining scalar problem is not a mechanical complexification transport: the classification contains existential unitary equivalences of invariant data, and an arbitrary complex unitary equivalence need not commute with conjugation.

Preferred architecture:

* inspect whether the Halmos classification theorem can be stated over `RCLike` using the same elementary orthogonal decomposition and positive cosine data;
* if so, generalize the invariant/classification layer rather than attempting to descend existential complex equivalences;
* otherwise define the real Halmos invariant explicitly and prove the real assembly theorem natively.

The realization follow-up in the census is smaller and conceptually separate: current realization data can carry intertwining of `cos Θ` and `sin Θ` separately. The paper packages this through one self-adjoint angle operator `Θ`. If `J Θ₀ = Θ₁ J`, functional calculus should give both trigonometric intertwinings. Conversely, if the current data knows enough spectral information, construct `Θ = arccos C` or `arcsin S` with spectrum in `[0,π/2]`. Again, `SeparatedIntertwiner.cfcHom_intertwines` is the first place to look.

Do not make this nonblocking cleanup prevent a source-exact row if the real classification is the actual blocker.

#### D.4 `DK-3.1-cor`: compact realization sentence

The classification half is on the correct compact object: `P (I-Q) P`, not `PQP`, and the invariant is `genericCosineBlock`, not the symmetrized `genericHalmosCosineSq`.

The remaining source sentence asks for realization of a prescribed decreasing angle sequence

`π/2 ≥ θ₁ ≥ θ₂ ≥ ... -> 0`

with prescribed zero-angle multiplicities.

Use `theorem3_1_realization`. Build a `HalmosAngleDatum` whose generic block is diagonal on an `ℓ²` model:

* cosine entries `c_n = cos θ_n`;
* sine entries `s_n = sin θ_n`;
* `c_n²+s_n²=1` pointwise;
* the generic left/right spaces are paired by the canonical basis equivalence;
* add the four elementary Halmos summands to realize prescribed `0` / `π/2` multiplicities as needed.

Compactness of `P(I-Q)P` corresponds on the generic block to the sine-square defect. Since `θ_n->0`, `sin² θ_n->0`, so the diagonal defect is compact. Search for existing diagonal compactness / prescribed approximation-number results before proving sequence compactness manually.

Then invoke `theorem3_1_realization` rather than reconstructing the pair of subspaces directly.

#### D.5 `DK-3.5-prop`: eigenvector angle clause and infinite-dimensional commutations

The missing printed assertion is essentially:

if `Θ x = θ x`, then `angle(x,Ux)=θ`

for the direct rotation `U`.

The conceptual calculation is straightforward. On an angle eigenvector,

`U = cos Θ + J sin Θ`,

so cfc gives

`cos Θ x = cos θ · x`,

`sin Θ x = sin θ · x`.

The `J` term is orthogonal in real part because `J` is skew-adjoint on the active-angle subspace:

`Re <x,Jx> = 0`.

Therefore

`Re <x,Ux> = cos θ ‖x‖²`.

Since `U` is unitary/orthogonal, `‖Ux‖=‖x‖`, so the geometric angle is `arccos(cos θ)=θ` for `θ∈[0,π/2]`.

The Lean work is mostly API alignment:

* inspect Mathlib's `InnerProductGeometry.angle` definition before fixing the exact formula; it may normalize with a real part/absolute value in a way that changes the final simplification;
* obtain cfc-on-eigenvector lemmas for `cos`/`sin`;
* use the already-proved skew-adjoint properties of `J`.

The second axis is scope: existing commutations are finite-dimensional, while `paperAngleOperatorC` is bounded/infinite-dimensional. Lift commutation to the bounded complex cfc tree first. The `J` clause additionally needs a suitable infinite-dimensional angle complex structure/polar factor.

Do not assert `J²=-1` globally. It is false on the zero-angle kernel. The correct identity is

`J² = -(sin Θ)(sin Θ)^+`,

so `J` acts as a complex structure only on the nonzero-angle part.

---

### E. Section 2 source-fidelity tranche — closed 2026-08-10

The two remaining Section 2 items from this handoff are now compiled and census-exact.

#### E.1 `S2-sin-two-theta`

The final Section 8 sentence extending the `sin 2θ` theorem to
`dim X(E₀) < dim X(F₀)` is covered by the four compiled strict-rank declarations
`unbounded_sinTwoTheta_{,residual_}uiNorm_representative_unequalDimension`
and their real twins.  The underlying directed theorem is stronger: it has no
dimension comparison at all.

A later audit incorrectly reopened this item by requiring a `Θ₀`-to-ambient-`Θ`
bridge.  That reading is incompatible with the source convention: the ambient
Hermitian `Θ` uses the matched-dimension condition (1.5), so it is not available
in the strict-dimension regime named by the closing sentence.  The comparison
with Theorems 6.1 and 6.3 identifies the extension as the directed `Θ₀`
conclusion.  The source facade now records this explicitly.

#### E.2 `S2-sharpness`

All four source constants have compiled admissible equality configurations.
The direct-sum construction is connected to the canonical subspace `sin Θ`,
`Θ`, `tan Θ`, and `tan 2Θ` operators through reusable orthogonal block-sum
functional-calculus geometry.  `S2-sharpness` is `compiled_exact /
proved_in_build` with no remaining scope gap.

---

### F. `S2-unbounded-scope` + `DK-6-appendix`: unbounded `tan 2Θ` at Ky Fan/UI-norm scope

This is probably the hardest remaining analytic proof and the most important place not to rediscover failed approaches.

#### F.1 What is already proved

At complex scalars, for the unbounded residual problem:

* domain-correct reflection equation is proved;
* spectral cutoffs are constructed;
* pole exclusion is unconditional;
* operator-norm (`ν=1`) branch-free residual `tan 2Θ` is proved with sharp factor `2`.

The unrestricted naive transfer of the bounded approximate-pair proof fails because its error coefficient contains `‖A‖`.

#### F.2 Exact obstruction in the bounded proof

The bounded approximate-pair theorem pairs equation (7.6) for right approximate singular vector `x_k` against an approximate **left** singular vector `y_k`. The left residual

`e_k = Sx_k - q_k y_k`

produces a term involving

`<A(Sx_k), e_k>`.

In the unbounded problem `Sx_k` lies in the high spectral side, where `A` is bounded below but not above. The low-side spectral cutoff does not control that term. This is why simply replacing `‖A‖` by a cutoff radius does not work.

#### F.3 Promising repair: define the left vectors exactly from `Sx_k`

Do **not** use the approximate family's supplied left vectors. Take

`y_k := S x_k / ‖S x_k‖`

on indices where the singular magnitude is nonzero. Then

`<A(Sx_k),y_k> = ‖Sx_k‖ <Ay_k,y_k>`

exactly. The high-side operator enters only through its quadratic-form lower bound, not through an uncontrolled norm.

Use `ApproximateLeadingSingularFamily` only for:

* orthonormality of the right vectors `x_k`;
* the approximate composite relation `X*X x_k ≈ q_k² x_k`, obtained from its two residual fields;
* approximation of `q_k` to the desired approximation numbers of the compressed tangent/cross block.

A useful structural observation is already recorded: for the compressed cross block `X=S Ω`,

`X* = Ω S`

because the reflection off-diagonal block is self-adjoint in the ambient reflection. Hence the family's `adjoint_residual` is exactly the low-cutoff leakage estimate for the geometric residual. No extra simultaneous-near-maximizer lemma is required.

#### F.4 The Gram error and the ε^(1/3) split

This is the subtle point most likely to be rediscovered incorrectly.

With approximate singular vectors, neither

`<D₀x_j,D₀x_k> = d_k² δ_jk`

nor orthonormality of the exact normalized `y_k=Sx_k/‖Sx_k‖` is exact. From the reflection Gram identity,

`<D₀x_j,D₀x_k> = δ_jk - <Gx_j,Gx_k>`,

and the same defect controls the `y` Gram matrix.

The error is of order

`O(ε)/(q_j q_k)`.

The family's basic `selected_large` bound only gives `q_k>ε`, which yields an error of order `1/ε` and diverges. Splitting at `q_k≥sqrt ε` leaves an `O(1)` error and is also insufficient.

Use the threshold

`q_k ≥ ε^(1/3)`.

Then:

* retained indices have Gram error `O(ε^(1/3))`;
* dropped indices have small tangent contribution, bounded by the pole lower bound `d_k≥κ`, so roughly `f(q_k)≤ε^(1/3)/κ`;
* both errors vanish as `ε->0`.

This exponent is not cosmetic. Do not replace it by `ε` or `sqrt ε` without recomputing both error channels.

#### F.5 Finish the finite-family estimate

After the split:

1. perform finite-dimensional Gram correction/polar orthonormalization on the high-side `y_k` family; the uniform `d_k≥κ>0` prevents denominator blowup;
2. retain the signed-cosine/polar treatment from M30 so no branch of `cos 2θ` is chosen;
3. apply `sum_abs_le_kyFanApproximationGauge_of_orthonormal` twice to the two residual pairings;
4. preserve the single factor `2` from those pairings;
5. send `ε->0` with spectral cutoff `τ` fixed;
6. then send `τ->∞` using the existing DK-5.1 cutoff/approximation lemma.

The order of limits matters: the low-side unbounded operator is controlled only at fixed cutoff radius.

#### F.6 From Ky Fan to arbitrary UI norm

Once every prefix satisfies

`δ · KyFan_ν(tan 2Θ₀) ≤ 2 · KyFan_ν(R)`,

invoke the existing Fan-dominance infrastructure to get

`δ N(tan 2Θ₀) ≤ 2 N(R)`

for the paper's UI norms/ideal family. Keep the core theorem at the most natural approximation-number/Ky Fan level.

The approximation-family infrastructure lives on the `DavisKahan` side of the import firewall, so the final Ky Fan proof belongs in `DavisKahan`, consuming the generic `ForTauCeti` unbounded reflection engine. Do not move `ApproximateLeadingSingularFamily` into a `ForTauCeti` module merely to make the file look generic.

#### F.7 Perturbation form and real scalars

After the residual theorem exists, derive the perturbation form using the same off-diagonalization/reflection residual relationship as the bounded M30 source path. Check the norm pinching carefully so the right side remains `2 N(H)` and no extra two is introduced.

Only after the complex analytic theorem is stable should the real version be transported. Most real unbounded spectral and sine infrastructure already exists; do not redo the analytic Ky Fan proof over `ℝ` independently unless transport genuinely fails.

#### F.8 Other Appendix obligations

Separate from the unbounded `tan 2Θ` theorem:

* the paper's unbounded Ritz compression `Ω(τ) A₀ Ω(τ)` and leakage estimate `‖F‖₁≤ητ≤ε` are not represented in the literal paper route;
* Proposition 6.1 still lacks the common-domain/unbounded relaxation the Appendix explicitly says is available;
* displayed equations (6.7)--(6.11) themselves are not formalized, although the single-angle theorem conclusion is already proved by a different route.

Prioritize actual source conclusions over reproducing proof-display numbers unless the census definition of completion requires those identities. If the theorem is already source-exact via a stronger alternate proof, the displayed derivation may be documentation fidelity rather than theorem debt; adjudicate explicitly rather than silently assuming either answer.

---

### G. Smaller but real source obligations

#### G.1 `DK-4.2-prop`: identify the right side with `Σ sin² θ_k`

The basis inequality is compiled. The missing source dictionary is the identification of

`Σ_i (1 - ‖C b_i‖²)`

with the principal-angle expression.

In finite dimension:

`Σ_i ‖C b_i‖² = trace(C* C)`.

For the positive cosine block this is the sum of squared principal cosines. Therefore

`dim - trace(C²) = Σ_k (1-cos² θ_k) = Σ_k sin² θ_k`.

Search the existing Section 8 approximation-number/principal-cosine dictionary before building new eigenvalue machinery. If a general finite-dimensional trace/Hilbert--Schmidt identity is missing, put that identity in reusable operator theory and keep the principal-angle substitution in the source facade.

Do not change the right side back to the older `sum cost D b_i` expression; recorded counterexamples show that transcription route was wrong.

#### G.2 `DK-5-hermitian-inequalities`: equation (5.2) and its sharp 2x2 witness

Equation (5.1) is already complete and more general than the paper. The remaining printed inequality is the rank-sensitive Schatten/trace-norm consequence (see the census/transcription for the exact project notation before coding).

The likely route is finite-rank Cauchy--Schwarz between Schatten 1 and 2 quantities together with (5.1): one factor contributes a `sqrt(rank C)`. Do not rely on remembered notation; first inspect which project gauges correspond to the paper's subscripts `1` and `2` in this section.

The paper also gives an explicit 2x2 sharpness/counterexample calculation, with matrices recorded in the census. Compile that arithmetic as part of the row rather than leaving it as prose.

The paper's subsequent open question about replacing rank by a constant is not a completion obligation.

#### G.3 `DK-6.3-thm`: remove the finite-trial wrapper under the paper's separability assumption

The real arbitrary-trial theorem already exists. The complex source-facing finite theorem still has a finite-dimensional trial hypothesis in a place where the paper obtains finiteness from a strict rank inequality under separability.

Rather than reprove the entire theorem for arbitrary trial dimension, derive finite-dimensionality from the paper hypotheses:

1. a closed subspace of a separable Hilbert space is separable, hence Hilbert dimension/rank `≤ aleph0`;
2. if `rank Z < rank V ≤ aleph0`, then `rank Z < aleph0`;
3. use the library equivalence between rank below `aleph0` and finite-dimensionality;
4. invoke the existing theorem.

Search Mathlib/TauCeti for the exact cardinal lemmas first. If the general "separable Hilbert subspace has rank ≤ aleph0" bridge is missing, it is reusable `ForTauCeti` infrastructure.

---

### H. `DK-9-model`: complete the beam model as the paper states it

This row has three logically separate axes. Do them in this order because each supplies infrastructure for the next.

#### H.1 Prove positive spectrum exists, preferably as a discrete unbounded sequence

Current state:

* `beamOperator` is the self-adjoint form realization;
* the form embedding is compact;
* the kernel is the two-dimensional affine plane;
* the positive spectrum is contained above the explicit gap, but nonemptiness is not proved;
* `beamFiniteDataCertificate` still assumes a positive spectral value.

The right general theorem is a compact-resolvent/discrete-spectrum result for a semibounded self-adjoint form realization.

Conceptual route:

1. compactness of the form-domain embedding implies compactness of a shifted resolvent `(A+c)^{-1}`;
2. on `ker A⊥`, the compact resolvent is a nonzero positive compact self-adjoint operator;
3. compact self-adjoint spectral theory supplies nonzero eigenvalues tending to zero on an infinite-dimensional complement;
4. invert the resolvent eigenvalue relation to obtain positive eigenvalues of `A` tending to `+∞`;
5. order them after the two zero modes to obtain the paper's `α₃<α₄<...` framework.

If the general compact-form-embedding-to-compact-resolvent theorem is missing, implement it in the form-method / self-adjoint spectral theory layer of `ForTauCeti`. This is exactly the sort of reusable theorem the roadmap should influence.

At minimum, nonemptiness of positive spectrum is enough to remove the current `α∈realSpectrum` certificate hypothesis; an unbounded sequence is the source-faithful stronger endpoint.

#### H.2 Identify the form realization with the classical fourth derivative and free-end boundary conditions

The paper's operator is the closure of `(d/dt)^4` with free-end boundary conditions. Current Lean defines the form realization and derives boundary conditions for eigenfunctions, which is weaker than identifying the operator domain.

The desired theorem is an operator-domain equivalence:

`u ∈ dom(beamOperator)` iff `u` has the appropriate fourth weak derivative in `L²` and

`u''(0)=u''(1)=u'''(0)=u'''(1)=0`,

with `beamOperator u = u''''`.

Proof strategy:

* from the representation theorem, `a(u,v)=<f,v>` for all form-domain `v`;
* test first against compactly supported smooth functions to identify the distributional fourth derivative with `f`;
* Sobolev regularity upgrades `u` to the required `H^4`/classical trace regularity;
* integrate by parts twice against general `H²` test functions; vanishing of the boundary form forces the four natural free-end conditions;
* converse: an `H^4` function with those boundary conditions satisfies the form identity by two integrations by parts, hence belongs to the form operator domain;
* then identify the form operator with the closure of the classical operator.

Any general interval Sobolev integration-by-parts or natural-boundary-condition lemmas should live below the beam source file.

#### H.3 Real `L²(0,1)`

The paper uses real `L²`; the current beam model uses `Lp ℂ 2`.

The simple complexification route used elsewhere is unavailable because the repository does not yet present `Lp ℂ 2 μ` as the real complexification of `Lp ℝ 2 μ`.

Two architecture-compatible options:

1. build a general real/complex `L²` isometric equivalence, pointwise `f ↦ (re f, im f)`, and transport the form/operator;
2. parameterize the beam form construction over `RCLike` if inspection shows the analytic ingredients are scalar-generic.

Choose after inspecting the actual dependencies. A generic `L²` complexification theorem is valuable mathematics, but do not launch a broad Bochner-integration campaign if the beam construction can be made `RCLike` with substantially less machinery.

---

### I. Section 9 consequences sharing earlier work

#### I.1 `DK-9.5-9.7`: the missing 2-norm sentence after (9.7)

Do **not** do more beam analysis here.

The beam perturbation, spectral gap, Rayleigh--Ritz residual, comparison operator, and operator-norm `tan 2θ₁` bound are already proved.

Once mission F supplies

`δ · KyFan_2(tan 2Θ₀) ≤ 2 · KyFan_2(R)`,

the paper's `tan 2θ₁ + tan 2θ₂` sentence should be a short specialization. `norm_beamRitzOffDiagonal_le` already controls the residual block, and the recentered Gram/rank-one structure already gives the second approximation-number simplification needed on the right.

Keep the hard theorem in `TanTwoThetaUnboundedResidual.lean`; the beam source file should instantiate it in a few lines.

#### I.2 `DK-9-infinite-residual-counterexample`

The operator-domain phenomenon is already formalized with the canonical `LinearPMap` diagonal operator. Three items remain.

**Rayleigh quotient.** For the geometric vector `e_n=μ^n` and diagonal multiplier chosen in the source, evaluate numerator and denominator by geometric series. The recorded arithmetic is

`[1/(1-μ)] / [1/(1-μ²)] = 1+μ`.

Use existing `HasSum` geometric-series lemmas rather than manually manipulating partial sums if possible.

**Self-adjointness of the maximal real diagonal operator.** This should be a reusable theorem: for real diagonal `d_n`, define domain `{x | (d_n x_n)∈ℓ²}` and multiplication `Ax=(d_n x_n)`. Symmetry is coordinatewise. For adjoint-domain equality, test a putative adjoint vector against standard basis vectors to identify its coordinate image as `d_n y_n`; the existence of the adjoint image then says that sequence lies in `ℓ²`, exactly the maximal domain condition. Package this in `ForTauCeti`'s `LinearPMap` diagonal/multiplication operator layer if no theorem exists.

**Weinberger bound.** After the quotient is `1+μ`, apply the appropriate lower-bound/min--max angle estimate from the repository to derive the source contrast

`sin² θ ≤ (1+μ-α̌₁)/(α̌₂-α̌₁)`,

and the best-lower-bound simplification

`sin θ ≤ μ / sqrt(1-μ)`.

Search for the Weinberger/lower-bound theorem before reproving it. The point of the source example is precisely that residual theorems do not apply because the trial vector lies outside the operator domain, while the form/Rayleigh lower-bound method remains meaningful.

---

## 6. Architecture/migration work that affects the credibility of “100%”

### M21: finish the `LinearPMap` migration

Recent work moved spectral reduction and its real companion onto `LinearPMap`; that is the correct foundation. Several source facades still consume the temporary real `ClosedOperator` adapter. Re-search current HEAD for all consumers before editing, then migrate them dependency-order and delete the duplicate abstraction when the last consumer is gone.

This is not merely cosmetic. Remaining unbounded work should not be forced to prove each theorem twice because two domain carriers survive indefinitely.

### M23: frontier `--check` coverage

The existing frontier check can miss source nodes with no census mapping. This matters because the final claim is source completeness, and an omitted row/declaration is exactly the failure the checker should expose.

Keep the fix narrow: improve the existing checker/manifest relationship rather than adding another parallel checker system. Repository policy is explicitly against checker proliferation.

### M28: removable conjugation cleanup

Take removable real/complex conjugation simplifications back to the complex side where they reduce duplicated proof plumbing. Treat this as architecture cleanup, not a source theorem mission.

---

## 7. Standing traps and false routes

These are established by compiler work or counterexample. Do not re-propose them without new mathematics.

1. **Search before declaring an API absent.** Several campaign blockers were false descriptions of the repository.
2. **`omit ... in` must precede the docstring it scopes.** Placing it between `/-- ... -/` and `theorem` produces a misleading parser error.
3. **Bounded Borel spectral calculus is complex-only in the relevant local layer.** A proof reaching `exists_finiteDimensional_le_almostInvariant` cannot become `RCLike` by binder editing.
4. **Use `realSpectrum`, not `spectrum ℝ`, across complexification.** Avoid the real-algebra diamond.
5. **Do not transport `KyFanDominantIdealFamily` gauges across fields.** Transport approximation numbers/Ky Fan inequalities, then rebuild the target-field norm statement.
6. **`PaperUnitaryInvariantNorm` is scalar-agnostic; ideal families are field instances.** This distinction has already routed around several false scalar blockers.
7. **A module not imported by an `All.lean` is invisible to the default build/census/frontier.** Every new source endpoint must enter the build closure.
8. **The census and frontier JSON files have different serialization conventions.** Preserve their existing formatting exactly.
9. **Status edits can trigger frontier obligations.** Run the full source/frontier gate set after metadata changes.
10. **No wildcard imports, no `sorry`, no `admit`, no new axioms.**
11. **`J²=-1` is false globally.** Correct: `J²=-(sinΘ)(sinΘ)^+`; `J` vanishes on the zero-angle kernel.
12. **`DK-3.1-cor` uses `P(I-Q)P`, not `PQP`.** Do not regress the compactness statement.
13. **The Section 3 classification invariant is `genericCosineBlock`, not `genericHalmosCosineSq`.**
14. **The weaker maximal-subspace predicate previously attributed to Proposition 3.5 is false for `c<1`.** Exterior vectors give a counterexample; keep the corrected complement-aware predicate.
15. **The existing Theorem 8.2 infinite-dimensional counterexample does not satisfy (3.5).** It says nothing about the paper's (3.5)-qualified claim.
16. **The naive unrestricted unbounded `tan 2Θ` Sylvester identity has a nonzero commutator defect.** `doubleAngleTangent_sylvesterEquation` carries it explicitly. Do not assume it vanishes.
17. **(1.12)/(1.13) suprema need not be attained.** The `diag(1-1/n)` example rules out an exact maximizer.
18. **The old `sin 2Θ` multiplicity-mismatch counterexample was wrong.** The directed double-angle sine range sits in the relevant source subspace; re-check the actual block geometry.
19. **Proposition 4.4 is false as printed.** It is correctly terminal as `refuted_as_transcribed`; see the compiled counterexample and `papers/davis_kahan_prop_4_4_counterexample.tex`.
20. **The Section 10 questions are the paper's open questions.** They are not proof debt.
21. **M30's factor two is sacred.** Reflection gives the `2`; adjoint/corner transport gives no additional `2`.

---

## 8. Recommended sequencing and parallelism

A good coordinator should dispatch by shared mathematics, not simply by census order.

### Immediate parallel lanes

**Lane 1 — M36 / real Theorem 8.1.** The hard descent infrastructure is now present. Finish the real source theorem while the architecture is fresh.

**Lane 2 — equation (1.12) codomain-room cleanup.** Small, well-scoped, independent. This can retire `S1-ui-norms`.

**Lane 3 — (3.5) directed-gap equality.** High leverage: closes the dimension issue in Theorem 8.2 and ambient tangent acuteness, and supplies the correct framework for the Section 3 bilateral-shift remark.

**Lane 4 — unbounded Ky Fan `tan 2Θ`.** Hard analytic lane, but it unlocks three source locations at once. Give it to an agent with the M30/M30-style approximate singular-family context.

**Lane 5 — Section 3 cfc/intertwiner work.** Proposition 3.1 characterization and Theorem 3.1 realization cleanup may share a generic intertwining lemma.

**Lane 6 — Section 9 spectral/form theory.** Positive beam spectrum and maximal diagonal self-adjointness can proceed largely independently and may contribute reusable `ForTauCeti` theory.

### Shared-file concurrency rule

While multiple mathematical lanes are active, avoid editing shared census/frontier JSON and aggregate `All.lean` files unnecessarily. Land/compile the mathematical declarations first, then make one intentional integration update. This minimizes merge conflicts and prevents metadata from claiming a theorem before its implementation stabilizes.

### When to split a mission

Split when the mathematical dependencies separate. For example, `DK-9-model`'s compact-resolvent theorem and real-`L²` complexification are distinct projects. Do not make one agent hold both merely because they live in one census row.

Conversely, combine tasks when one general theorem is clearly shared: (3.5) geometry and unbounded `tan 2Θ` are the obvious examples.

---

## 9. Startup protocol for a new proof agent

For any mission:

1. inspect `git status --short` and recent commits;
2. read the exact census row, including the **latest** notes, not just `next_action`;
3. inspect the source transcription for the precise hypothesis/conclusion and nearby proof;
4. search declaration names and concepts repository-wide, including `external/TauCeti/` and `ForTauCeti/`;
5. inspect the current variable blocks/signatures of candidate lemmas;
6. identify the lowest reusable mathematical seam;
7. prove that seam without weakening the source theorem;
8. expose a thin source-facing theorem at the printed scope;
9. wire new modules into the build closure;
10. compile the narrowest meaningful target, then integration targets;
11. update census/frontier only after the proof compiles;
12. run the full validation set before claiming the row exact.

When compiler feedback reveals a structural mismatch, inspect surrounding definitions and already-compiled analogous proofs before issuing a one-line speculative patch. The campaign has repeatedly lost time by fighting subtype/coercion representations tactically when the right answer was to use the canonical representation one layer lower.

---

## 10. Definition of done for the full paper

The campaign is complete only when all of the following are simultaneously true:

1. every printed mathematical conclusion has a source-facing Lean declaration at the printed scope, or is explicitly and correctly classified as false/open/not a completion obligation;
2. no completion row remains merely `compiled_specialization` because of an actual paper-scope narrowing;
3. the stale real-scalar blocker has been split/retired and the blockers table is empty;
4. Proposition 4.4 remains documented as refuted rather than "proved" by changing its statement;
5. the Section 10 open questions remain correctly non-obligatory;
6. every source declaration resolves from the intended default build closure;
7. census declaration verification and frontier checks are clean;
8. source endpoints are axiom-clean: no `sorryAx`, `sorry`, `admit`, or new axioms;
9. repository dependency rules and library-structure baselines do not regress;
10. a full `lake build` succeeds without avoidable warning noise introduced by the campaign;
11. `git diff --check` is clean;
12. a final fresh section-by-section audit against `non-distributable/davis-kahan-1970-modernized-transcription.tex` confirms that no printed assertion was omitted merely because no census row named it.

The last item is essential. The gates can verify declarations they know about; they cannot prove that the census itself remembered every sentence in the paper.

---

## 11. Short mission briefs a coordinator can copy

### Real Theorem 8.1

Use the compiled complex `theorem8_1_canonicalBranch` on complexified real data. Pull spectral repulsion back with `realSpectrum_complexify`. Define the real canonical branch with `realBoundedSpectralSubspaceIicOfGap`. Identify its complexification using `complexifySubmodule_realBoundedSpectralSubspaceIicOfGap`. Pull reduction, form bounds, and quarter-angle geometry back exactly. Prove uniqueness by complexifying any competing real branch, applying complex uniqueness, and using injectivity of `complexifySubmodule`. Generalize the restricted-spectrum/form-bound bridge if needed rather than duplicating it inside Section 8.

### Standing assumption (3.5)

Prove that equal crossed-defect dimensions make the two directed gaps equal, preferably through the Halmos decomposition / crossed sine blocks. The generic parts are equisingular; the only possible norm asymmetry is the defect singular value `1`, and (3.5) equalizes its presence. Use the theorem to convert directed Theorem 8.2 bounds into `subspaceGap<sqrt 2/2`, and to derive the ambient tangent transversality that the paper gets from (1.5)+(3.5).

### Unbounded Ky Fan `tan 2Θ`

Start from `TanTwoThetaUnboundedResidual` plus the `ForTauCeti` reflection/cutoff/pole infrastructure. Do not reuse the bounded approximate left singular vectors: define `y_k=Sx_k/‖Sx_k‖` exactly so the high-side unbounded form term has no residual. Use the approximate family for the right vectors and `X*X` relation only. Control Gram errors with the threshold `q_k≥ε^(1/3)`; `ε` and `sqrt ε` thresholds are insufficient. Gram-correct the retained high-side family, apply the magnitude Ky Fan variational estimate twice, send `ε->0` at fixed cutoff, then cutoff to infinity. Preserve the single sharp factor `2`. Fan dominance then gives arbitrary UI norms. Instantiate this result in the Appendix and beam `(9.7)`; do not reprove it downstream.

### Proposition 3.1 characterization

Do not assume equation (3.8). Starting from a unitary/orthogonal intertwiner with accretive diagonal blocks, derive `C₀²S₁=S₁C₁²`, transport through cfc with `f=sqrt` to get `C₀S₁=S₁C₁`, then use acute density of `Range C₁` to recover the crossed-block adjoint relation and invoke the existing direct-rotation uniqueness. Search `SeparatedIntertwiner.cfcHom_intertwines` first.

### Beam positive spectrum

Turn compactness of the form embedding into compactness of a shifted resolvent, restrict away from the known two-dimensional kernel, invoke compact self-adjoint spectral theory, and invert the resolvent spectrum to obtain positive beam eigenvalues (ideally an unbounded sequence). Put the compact-resolvent theorem in reusable form-method spectral theory if it is missing; keep the beam file as an application.

---

## Bottom line

The project is no longer missing a single monolithic "real infinite-dimensional" layer. It is in the endgame of a handful of mathematically distinct obligations. The best way to reach 100% is to solve the shared operator-theory seams once—real canonical spectral branches, (3.5) gap symmetry, cfc intertwiners, unbounded Ky Fan double-angle tangent, compact-resolvent spectral theory—and let thin Davis--Kahan source theorems consume them.

Do not optimize for the smallest local diff. Optimize for source-faithful endpoints resting on canonical, reusable operator theory, while keeping each mission bounded by the mathematics it actually needs.
