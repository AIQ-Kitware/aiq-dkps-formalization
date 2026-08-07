/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Frontier.Section8Perturbation
import DavisKahan.Frontier.Section8Krein

/-!
# Davis--Kahan 1970, Theorem 8.2: the printed residual branch

Theorem 8.2 offers two alternatives, `‖H‖ < δ/2` *or* `‖R‖ < δ/2`.
`DavisKahan/Frontier/Section8Perturbation.lean` proves the first from the
printed hypotheses.  This module proves the second, and the printed proof of it
is one sentence:

> If instead `‖R‖₁ < δ/2`, we use the fact that, without changing `A₁ + H₁`,
> `R`, or the `Λⱼ`, one may change `H₁`.  A theorem of Krein gives a choice
> with `‖H‖₁ = ‖R‖₁`, reducing the argument to the preceding case.

Both halves of that sentence are now theorems, so this module is exactly the
reduction and nothing else: no contour, no continuation, no projection path.

## What `R` is

The paper's residual is equation (1.8),

```
R = (A + H) E₀ - E₀ A₀,
```

which is `DavisKahanExt.residual (A + K) P.subtypeL (compressOperator P A)`
in the maintained source surface -- `E₀` is the isometric inclusion of the
unperturbed reducing subspace and `A₀ = E₀⋆ A E₀` its block.  The source also
records the two identities that pin it down: `R = H E₀` (Section 1), and

```
R⋆ R = H₀² + B⋆ B,
```

so `R` is the *first block column* `(H₀, B)` of the perturbation, not merely
its off-diagonal corner `B`.  That is what makes the reduction exact rather
than lossy: Krein's theorem completes a column to a self-adjoint operator of
the *same* norm, so `‖H'‖ = ‖R‖` on the nose.

`residual_eq_comp_subtypeL` below proves `R = K ∘L P.subtypeL` from invariance
alone, so the capstone can be stated with the source-literal (1.8) residual and
still reach the Krein theorem.

## The four preservation identities

With `H' := K'` the Krein completion and `A' := A + K - K'`:

```
A' + K' = A + K          -- every perturbed datum is literally unchanged
A'|P    = A|P            -- every unperturbed datum on P is literally unchanged
K'|P    = K|P  = R       -- the residual itself is unchanged
‖K'‖    = ‖R‖            -- Krein, with the exact norm
```

Only the `Pᗮ` diagonal block `H₁` moves, which is precisely the freedom the
printed sentence uses.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section8

open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Experimental.Foundation

universe u

section Residual

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ### 1. The printed residual is the first column of the perturbation -/

omit [CompleteSpace H] in
/-- **The paper's `R = (A + H) E₀ - E₀ A₀` equals `H E₀`.**

This is the Section 1 remark "`R`, left-multiplied by the isometry `(E₀⋆; E₁⋆)`,
gives the first column of `H`; or that `R = H E₀`", and it needs nothing beyond
invariance of `P` under the unperturbed operator: on `P` the compression `A₀` is
the honest restriction, so the two `A`-terms cancel. -/
theorem residual_eq_comp_subtypeL (A K : H →L[ℂ] H) (P : Submodule ℂ H)
    [P.HasOrthogonalProjection] (hPinv : ∀ x ∈ P, A x ∈ P) :
    residual (A + K) P.subtypeL (compressOperator P A) = K ∘L P.subtypeL := by
  ext u
  have hAu : A (u : H) ∈ P := hPinv (u : H) u.2
  have hco : ((compressOperator P A u : P) : H) = A (u : H) := by
    change P.starProjection (A (u : H)) = A (u : H)
    exact Submodule.starProjection_eq_self_iff.mpr hAu
  show (A + K) (u : H) - ((compressOperator P A u : P) : H) = K (u : H)
  rw [hco]
  show A (u : H) + K (u : H) - A (u : H) = K (u : H)
  abel

/-! ### 2. Spectral data on `P` only sees the operator on `P` -/

omit [CompleteSpace H] in
/-- **`SpectrumIn` transfers along agreement on the subspace.**

`restrictedSpectrum` is the spectrum of an honest restriction, so two operators
agreeing pointwise on `P` have the same `P`-block and therefore the same
`P`-spectrum.  This is what makes the Krein replacement free on the unperturbed
side: `A'` and `A` agree on `P`, so the printed placement of `A₀` transfers
literally rather than being re-derived. -/
theorem spectrumIn_of_eqOn {A B : H →L[ℂ] H} {P : Submodule ℂ H} {s : Set ℝ}
    (heq : ∀ x ∈ P, A x = B x) (h : SpectrumIn A P s) : SpectrumIn B P s := by
  have hinv : InvariantFor B P := by
    intro x hx
    rw [← heq x hx]
    exact h.1 x hx
  refine ⟨hinv, ?_⟩
  have hres : B.restrict hinv = A.restrict h.1 := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    show B (u : H) = A (u : H)
    exact (heq (u : H) u.2).symm
  rw [restrictedSpectrum_eq_restrictionSpectrum B P hinv, hres,
    ← restrictedSpectrum_eq_restrictionSpectrum A P h.1]
  exact h.2

/-! ### 3. Theorem 8.2, the residual alternative -/

section Capstone

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative: the branch is
strictly inside the quarter turn.**

The hypotheses are the printed ones, identical to
`theorem8_2_perturbationHalfGap_source` except that the smallness assumption is
the printed residual condition `‖R‖ < δ/2` in place of `‖H‖ < δ/2`.  `R` is the
source residual (1.8), `R = (A + K) E₀ - E₀ A₀`.

No caller-supplied certificate appears: no `ResidualHalfGapBridge`, no
`SpectralContinuationWitness`, no Krein completion, no alternative perturbation
`A'`, no branch-selection datum.  All of those are proof internals.

The proof is the printed reduction.  Krein's theorem
(`Krein.exists_selfAdjoint_completion_eq_norm_restriction`) replaces `K` by a
self-adjoint `K'` with the same first column and with `‖K'‖ = ‖R‖`; setting
`A' := A + K - K'` leaves `A' + K' = A + K` and `A'|P = A|P`, so every printed
hypothesis transfers verbatim and
`theorem8_2_perturbationHalfGap_source` applies to `(A', K')`. -/
theorem theorem8_2_residualHalfGap_source
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hRsmall : ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    directedGap P Q < Real.sqrt 2 / 2 := by
  classical
  letI : CompleteSpace P :=
    (P.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  -- the printed residual is the first block column of the perturbation
  have hRcol : residual (A + K) P.subtypeL (compressOperator P A) = K ∘L P.subtypeL :=
    residual_eq_comp_subtypeL A K P hPred.1
  rw [hRcol, Krein.norm_comp_subtypeL_eq_norm_comp_starProjection] at hRsmall
  -- Krein's replacement: same first column, norm exactly the residual norm
  obtain ⟨K', hK'sa, hK'col, hK'norm⟩ :=
    Krein.exists_selfAdjoint_completion_eq_norm_restriction K
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hK) P
  have hK'sym : IsSelfAdjointOperator K' :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK'sa
  -- `‖H'‖ = ‖R‖ < δ/2`
  have hK'small : ‖K'‖ < delta / 2 := by rw [hK'norm]; exact hRsmall
  -- `H'|P = H|P`: the residual data is unchanged
  have hK'P : ∀ x ∈ P, K' x = K x := by
    intro x hx
    have hfix : P.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    have h := congrArg (fun M : H →L[ℂ] H => M x) hK'col
    simpa only [ContinuousLinearMap.comp_apply, hfix] using h
  -- the replacement problem
  set A' : H →L[ℂ] H := A + K - K' with hA'def
  -- (1) the perturbed operator is literally unchanged
  have htotal : A' + K' = A + K := by rw [hA'def]; abel
  have hA'sym : IsSelfAdjointOperator A' := by
    intro x y
    have hAxy : ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := hA x y
    have hKxy : ⟪K x, y⟫_ℂ = ⟪x, K y⟫_ℂ := hK x y
    have hK'xy : ⟪K' x, y⟫_ℂ = ⟪x, K' y⟫_ℂ := hK'sym x y
    show ⟪A x + K x - K' x, y⟫_ℂ = ⟪x, A y + K y - K' y⟫_ℂ
    rw [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
      hAxy, hKxy, hK'xy]
  -- (2) the unperturbed operator is unchanged on `P`
  have hA'P : ∀ x ∈ P, A' x = A x := by
    intro x hx
    show A x + K x - K' x = A x
    rw [hK'P x hx]
    abel
  have hA'inv : ∀ x ∈ P, A' x ∈ P := by
    intro x hx
    rw [hA'P x hx]
    exact hPred.1 x hx
  have hA'red : Reduces A' P := reduces_orthogonalComplement hA'sym hA'inv
  -- the printed placement of `A₀` transfers, because `A'` and `A` agree on `P`
  have hA'spec : SpectrumIn A' P (Set.Icc (beta - delta / 2) (alpha + delta / 2)) :=
    spectrumIn_of_eqOn (fun x hx => (hA'P x hx).symm) hP
  -- every perturbed hypothesis transfers by rewriting along `A' + K' = A + K`
  have hQ' : SpectrumIn (A' + K') Q (Set.Icc beta alpha) := by rw [htotal]; exact hQ
  have hQperp' : SpectrumIn (A' + K') Qᗮ (gapExterior beta alpha delta) := by
    rw [htotal]; exact hQperp
  -- the printed reduction to the perturbation-norm case
  exact theorem8_2_perturbationHalfGap_source hA'sym hK'sym hdelta hab hQ' hQperp'
    hA'red hA'spec hK'small

/-- **The residual alternative in the printed scalar form.** -/
theorem theorem8_2_residualHalfGap_source_angle_lt
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hRsmall : ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    Real.arcsin (directedGap P Q) < Real.pi / 4 := by
  have h := theorem8_2_residualHalfGap_source hA hK hdelta hab hQ hQperp hPred hP
    hRsmall
  have h0 : (0 : ℝ) ≤ directedGap P Q := norm_nonneg _
  rw [← DavisKahan1970.Section8.arcsin_sqrt_two_div_two]
  refine Real.arcsin_lt_arcsin (by linarith) h ?_
  have : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  linarith

/-- **Theorem 8.2's printed disjunction.**  Either half-gap alternative --
small perturbation norm *or* small residual norm -- gives the strict quarter
angle.  Dispatch only; both branches are already theorems. -/
theorem theorem8_2_branch_source
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hsmall : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    directedGap P Q < Real.sqrt 2 / 2 := by
  rcases hsmall with h | h
  · exact theorem8_2_perturbationHalfGap_source hA hK hdelta hab hQ hQperp hPred hP h
  · exact theorem8_2_residualHalfGap_source hA hK hdelta hab hQ hQperp hPred hP h

end Capstone

end Residual

end Section8
end Frontier
end Experimental
end DavisKahan
end TauCeti
