# Failed and refuted proof directions — session of 2026-08-10

**Purpose.** Every dead end from this session, in one place, so that (a) a reviewer can check
whether something was missed, and (b) a future mission does not re-walk a route that is already
known to fail. Written for outside review.

**How to read the confidence column.** These are not equally strong claims and should not be
treated as such:

| Grade | Meaning |
|---|---|
| **REFUTED** | A counterexample or reverse theorem is machine-checked in the repository. Do not re-attempt. |
| **MEASURED** | Checked against the build (signatures, instance resolution, import graph). Solid, but scoped to what was measured. |
| **ESTIMATED** | A judgement, not a proof. **Several estimates in this campaign turned out false in both directions** — see §5. |

Anything marked ESTIMATED is a candidate for exactly the review being asked for.

---

## 1. Real spectral multiplicity (row `DK-3.1-thm`)

### 1.1 Lower the symbol *codomain* to `ℝ`, keeping `H` complex — **REFUTED**

Proposed: restate `BorelCalculus/` over `ℝ`-valued symbols with predicate `IsSelfAdjoint`
instead of `IsStarNormal`, keeping the Hilbert space over `ℂ`.

Why it fails: on a complex Hilbert space the two-term polarization sum recovers only
`Re ⟪ψ, Tξ⟫`, for **any** operator including self-adjoint ones. Machine-checked counterexample:
`H = ℂ`, `T = id` (self-adjoint), `ξ = 1`, `ψ = I` — the two-term sum is `0` while the matrix
element is `−I`. So `BorelCalculus/Polarization.lean:79 inner_polarization` is load-bearing for
exactly as long as `H` is complex.

Independently fatal: with `ℝ`-valued symbols the range of `cyclicIsometry` is a real subspace
while `cyclicSubspace` is complex, so `CyclicModel.lean:273 range_cyclicIsometry` becomes
**false** (`H = ℂ`, `a = 1`, `ξ = 1`).

Also measured: the blast radius is 623 transitive dependents, so there is no partial depth at
which the tree is green.

### 1.2 A real-parameter `MultiplicityDatum` as the lever — **MEASURED, and it is the wrong lever**

- **No consumer in the repository needs one. Zero.** `SameSpectralMultiplicity` has exactly one
  consumer (`theorem3_1_spectralMultiplicity_classification`); that consumer has none.
- The blocking hardcode is **not** `base : Measure ℂ` but `operator`'s `Lp ℂ 2` / `→L[ℂ]`, and
  `Lp ℝ 2` over a `Measure ℂ` is type-legal. So a real parameter is neither necessary nor
  sufficient.
- `map_ofReal_realSpectrumDiagMeasure` proves that pushing the real-spectrum diagonal measure
  into `ℂ` returns *literally* the measure the existing model is already built from — a
  real-spectrum model routed through `ℂ` is the old theorem with a longer proof.

### 1.3 The six-module real-spectrum transport layer — **MEASURED: sound, but on the wrong axis**

`RealSpectrumFunctionalCalculus` → `…BorelSymbols` → `…DiagonalMeasure` → `…CyclicModel` →
`…Intertwining` → `…CyclicDecomposition`. All green, axiom-clean, reusable.

They move the **symbol domain** at a complex Hilbert space. The row's gap is the **Hilbert
scalar**. The base module is governed by `[Algebra ℂ A]` and
`ContinuousFunctionalCalculus ℂ A IsStarNormal`; at `A = E →L[ℝ] E` neither instance holds, so
**no part of the layer instantiates at a real Hilbert space at all.** Kept as Tau Ceti
infrastructure; it closes nothing on this row.

*Process note for the reviewer:* six consecutive missions ran on this axis before anyone checked
it against the row's actual binders. Every individual step was verified and green.

### 1.4 What the row actually needs

Only one printed phrase is missing over `ℝ`: "spectral multiplicity function" in the
**noncompact** case — Hahn–Hellinger over a real Hilbert space, which Mathlib lacks and which
Davis and Kahan themselves import from Halmos rather than prove. The real biconditional, the
realization half, and all three real forms of Corollary 3.1 are proved and axiom-clean.

---

## 2. Unbounded `tan 2Θ` beyond the operator norm (rows `S2-unbounded-scope`, `DK-6-appendix` (b), `DK-9.5-9.7`)

### 2.1 The graph lane / spectral-cutoff route — **MEASURED no-go, but LANE-scoped**

The census recorded a no-go "for any argument resting only on strong convergence of spectral
cutoffs". That is true **of the graph lane** and false as a statement about the theorem.

Sharp form, derived fresh: taking `y := X x / ‖X x‖` makes the first defect vanish exactly and
the seam collapses to one scalar requirement — an approximate eigenvector of `X*X` inside
`dom A₀` whose residual beats its graph norm. Fixing the `A₀`-band first *does* control the
compressed residual, but the same vector enters the bounded `B₀₁` terms
(`FinishTanTwoTheta/…/Unbounded.lean:461,483`) needing the **full** norm small, and the
uncompressed leak arrives with no sign advantage.

**⚠ For review — a recorded mechanism that could not be reproduced.** The census had asserted
the surviving pairing "evaluates EXACTLY to `(‖P X x‖ − a)·⟪A₁ y, y⟫` — the leakage term is
ANNIHILATED because `y` lies in the band and the band projection commutes with `A₁`". A mission
could not derive this: with `y ∝ X x` the surviving pairing is an `A₀`-side quantity, and the
band is a band of `A₀`, whose projection lives on `E₀` and cannot commute with `A₁` on `E₁`.
**Probably wrong. Worth a second opinion.**

### 2.2 Global `IsDoubleAngleEigenbasis` — **ESTIMATED insufficient**

Proving an exact global double-angle eigenbasis is judged too strong in infinite dimension,
because the relevant operator may have continuous spectrum. This is a judgement, not a proof.

### 2.3 Discharging the eigenbasis by finite-dimensional `A`-invariant compression — **REFUTED**

This was the successor plan, and it is refuted by a reverse theorem rather than by difficulty.

`sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily` proves
`Σᵢ qᵢ/√(1−qᵢ²) ≤ kyFanApproximationGauge n T` for **every** double-angle tangent and **every**
compressed eigenfamily — three lines, because at a compressed family the systems `S xᵢ/qᵢ` and
`C xᵢ/cᵢ` are already exactly orthonormal and the pairing is exactly `qᵢ/cᵢ`.

Consequence (`kyFan_eq_sum_tangent_of_isCompressedDoubleAngleEigenbasis`): the blocking clause
can only hold **with equality**. It is not an inequality a construction can over-satisfy — it is
a **Ky Fan extremality condition**: the compression of `sin² 2Θ` to its span must *attain* the
prefix. Finite-dimensional `A`-invariance says nothing about extremality for `S²`, and
`sum_tangent_le_kyFan_of_invariantSubspace` records that the construction supplies precisely the
opposite inequality.

**No subspace construction of that shape can discharge the clause. This is mathematics, not a
Lean difficulty.** It is the live obstruction on all three rows.

#### 2.3a The replacement route — **LIVE, first two stages COMPILED 2026-08-10**

The refutation above is unchanged and still governs: `IsCompressedDoubleAngleEigenbasis` must
never be attacked directly. What changed is that the clause can be *removed from the proof*
rather than discharged. Target chain, on the **typed** directed corners
(`paperBlockCompression Uᗮ U`, never the ambient `unboundedReflectionTangent : H →L[ℂ] H`,
which carries both adjoint corners and would risk double-counting the sharp `2`):

```
kyFan k T₀  ≤  Σ_{n<k} tan(arcsin aₙ(S₀))  ≤  (2/δ) · kyFan k R₀
```

Compiled in `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedGramBridge.lean` (570 lines,
26 declarations, no `sorry`, zero warnings; `IsCompressedDoubleAngleEigenbasis` occurs nowhere
in it or its dependency closure):

- **The whole left half**, at every index and every prefix —
  `approximationNumber_reflectionTangentCorner_le` and `kyFan_reflectionTangentCorner_le`,
  under `IsSelfAdjoint Z`, `Z * Z = 1` and pole exclusion `‖offDiagonalPart Z‖ < 1` only.
- **The limit apparatus for the right half** —
  `tendsto_sum_tanArcsin_approximationNumber_reflectionSineCorner_comp`.
- **Cutoff-fixity of the Gram-selected vectors**, which had been flagged as an abandon point
  and is not one: 29 lines.

The step that made it work was not predicted by anyone: `adjoint_mul_unboundedReflectionTangent`
proves `T⋆T = Ring.inverse (C²) − 1` from `unboundedReflectionTangent_comp_diagonalPart` and
`diagonalPart_sq_add_offDiagonalPart_sq` alone, putting `T⋆T` inside the commutative subalgebra
generated by `C²` — after which the Gram-resolvent equation `T⋆T = S² + S²(T⋆T)` is
`noncomm_ring`.

**What remains is exactly the middle inequality**, the fixed-cutoff prefix theorem with no
extremality hypothesis. Measured, so it is not mistaken for a checkpoint: the approximate
*per-vector* layer exists (`TanTwoThetaUnboundedKyFan.lean` lines 577, 619, 748), the approximate
*sum* layer does not; it needs approximate analogues of two ~140-line theorems (lines 1266 and
1084), the θ-threshold split, and the `ρ → 0` passage **at fixed τ** — that ordering being what
avoids the `τ · cutoff-error(τ)` rate problem measured as a no-go in §2.1.

Everything in the new module is **ℂ-only** (the Gram-resolvent and selection layers are
`→L[ℂ]`). Real scalars are UNKNOWN here, not assumed.

### 2.4 `tanTwoThetaIdealBlock` as the operator `T` — **MEASURED wrong object**

It is a function of a submodule **pair** `(U,V)` requiring `IsQuarterAcute U V`, and there is no
second submodule anywhere in the unbounded module's scope — the perturbed subspace enters only
through the free involution `Z`, whose range is never exposed as a submodule. Its gauge theorem
also carries a spurious `1/(1 − 2·directedGap²)` factor. The right object is built from `Z`
alone: `unboundedReflectionTangent = S·(C·C)⁻¹·C`.

### 2.5 The Theorem 8.2 sine result as a template — **MEASURED: does not transfer**

`sinTwoTheta_directedResidual_all_kyFan` is stated for **bounded** `A : E →L[ℂ] E`, not for
`A : H →ₗ.[ℂ] H`. The Ky-Fan-to-arbitrary-UI-norm passage is a generic bridge and needed no 8.2
material at all.

---

## 3. Section 9 beam model (row `DK-9-model`)

### 3.1 The `Lp` complexification isometry (route (a)) — **MEASURED larger, and incomplete**

The isometry **alone does not produce a real beam operator.** There is no complex→real descent
of the needed kind in the tree, so route (a) additionally needs a conjugation on `BeamL2`, a
proof that `beamOperator` commutes with it, and a descent theorem for conjugation-invariant
complex `LinearPMap`s. Route (b), `RCLike` parameterization, was measured cheaper — the abstract
form method contains **zero** `Complex.*` tokens.

### 3.2 `contToLp p ≠ 0` for a nonzero polynomial, to get infinite-dimensionality — **MEASURED unsupported**

The moments are fine, but the positivity step `∫|p|² > 0` is positive-definiteness of the
Hilbert matrix, and no "continuous and a.e. zero ⇒ zero" lemma exists for `unitIocMeasure`.
Disjoint-interval indicators need neither, and the repository already had indicator machinery for
this measure that the recorded route overlooked.

---

## 4. Claims about *the paper* that were tested and did not hold

These are recorded because they concern source fidelity, not tactics.

- **Theorem 8.2 "is false under the cardinal reading of (1.5)".** The stated counterexample
  (`P = span{e₁,e₂,…}×0`, `Q = E×0`) gives `dim(P ⊓ Qᗮ) = 0` but `dim(Pᗮ ⊓ Q) = 1`, **violating
  standing (3.5)**, so it is not a counterexample to the printed theorem.
  `maximalAngle_lt_pi_div_four_of_crossedDefects` gets the printed conclusion in any dimension
  from (3.5) alone. **This prose is still live in production source** —
  `Section8SourceTheorem82.lean` L57–90 — and mirrored in
  `dev/section8-source-theorems-2026-08-07.md` L100–103. Flagged as audit disagreement 19 on
  2026-08-09 and not yet fixed.
- **`DK-3.5-prop`'s justification for the extra maximality conjuncts.** The row claims a nonzero
  vector of the exterior `Uᗮ ⊓ Vᗮ` "satisfies the printed conditions vacuously". False: such a
  vector lies in `P̃𝓗`, so printed **(c)** applies and gives `‖Q̃x‖ = ‖x‖ = c‖x‖`, excluding it
  for `c < 1`. The census describes the printed pair as `{M∩U, M∩V}`; the transcription's pair is
  `{M∩U, M∩Uᗮ}`.
- **Proposition 4.4** remains genuinely `refuted_as_transcribed` — that one stands.

---

## 5. Coordinator estimates that turned out FALSE — read this before trusting §2.2

Listed because they are the reason the confidence grades above matter, and because a reviewer
should know which "obstructions" have already been overturned.

| Claim | Reality |
|---|---|
| "Mathlib has no enumeration of an unbounded locally finite subset of `ℝ`" | It does — `orderIsoNatOfLinearSuccPredArch` plus `LocallyFiniteOrder.ofFiniteIcc`. Instance plumbing, elaborated first try. |
| "Extracting the eigenvector bridge restructures ~90 lines of Fredholm assembly" | The assembly was reused verbatim; 28 lines were **deleted**. The proof got shorter. |
| "The orthonormal Ky Fan upper bound may not exist" | It exists at `DavisKahan/DoubleAngle/KyFanOrthonormal.lean:45`, and the campaign's own endpoints already depended on it. |
| "The contraction Ky Fan lemma needs SVD + Abel summation, ~200 lines" | Needs neither; absorbs the contraction through the adjoint. |
| "There is no complex→real descent anywhere in this tree" | Descent is extensive and load-bearing; the repository's own real functional calculus **is** a descent construction. The true claim is much narrower: no descent of an *isometric equivalence*. |
| "Complexify-and-descend is dead / circular" | True only for an **arbitrary** intertwiner. False for **conjugation-fixed** objects — which is what a multiplicity model is assembled from. The blanket verdict would have suppressed a viable route. |
| "The 8.2 constant-4 route is not improvable, and constant 2 needs the Halmos generic decomposition" | Improvable. Resolved at constant 2 via a Ky Fan even-prefix pinch plus two matching-singular-sequence lemmas. No Halmos decomposition used. |
| "`IsUniformlyAcute` enters `DK-3.1-prop` through clause (a) only" | False as a statement about signatures — it rides on all five endpoints. Clause (a) is the root cause only. |
| "The repository proves `IsAcute` and `IsUniformlyAcute` differ in infinite dimension" | It does not. One direction is unconditional; the converse `projectionGap_lt_one_of_isAcute` is **finite-dimensional only**. A compiled witness pair separating them is still outstanding (`DK-3.2-def`). |
| "Prop 3.1 at `IsAcute` may be genuinely unprovable — `cos Θ` need not be boundedly invertible" | It is provable, in arbitrary dimension over both fields, and without (1.5). The construction is **polar, not spectral**: a partial isometry is unitary exactly when both polar projections are `⊤`, which *is* Definition 3.2. Bounded invertibility is never needed. |

---

## 5b. A recurring shape worth checking elsewhere: the fake scope gap

`DK-3.1-prop` was recorded for weeks as narrowed by `IsUniformlyAcute`. The object it was
narrowed *around*, `spectraDirectRotation U V hacute`, binds that hypothesis as **`_hacute`** — a
literal underscore — and returns `spectraCanonicalPolarFactor U V`, which is defined for every
pair. The definition's own docstring said so. Only the *theorem statements* were narrowed; the
mathematics was never gap-dependent.

**Reviewers and future missions: when a row records a hypothesis as a scope gap, check whether
the underlying definition actually consumes it.** An underscore binder means the recorded
obstacle may be pure bookkeeping. This has now cost this campaign at least once, with a standing
note already on the books warning about exactly it.

---

## 6. Suggested review targets

Ranked by how much a second opinion would be worth:

1. **§2.3, the extremality obstruction.** It is machine-checked, so the *theorem* is not in doubt
   — but is there a different formulation of the endpoint that does not route through this
   clause at all? The clause exists because `T` was left a free variable; tying it to
   `unboundedReflectionTangent` converts the clause into extremality rather than removing it.
2. **§2.1, the unreproducible band-commutation mechanism.** Either the original derivation was
   wrong, or it was right in a setting nobody has reconstructed.
3. **§2.2, global `IsDoubleAngleEigenbasis`.** The only ESTIMATED entry doing load-bearing work.
4. **§1.4.** Is real Hahn–Hellinger genuinely required for the printed sentence, or is there a
   formulation of "complete system of invariants" that avoids it in the noncompact case?
