/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

import DavisKahan.TanTheta.Theorem63TrialData
import DavisKahan.TanTheta.UnboundedSpectrum
import DavisKahan.SpectralTheory.ReflectionRestriction
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramSpectralRank

/-!
# Theorem 6.3 for unbounded self-adjoint operators

Davis--Kahan's Section 2 claims the four angle theorems for unbounded self-adjoint
operators, with the extra work concentrated in Theorem 5.2 and the Appendix to Section 6.
For the single-angle tangent family that claim is at **arbitrary unitarily invariant
norm**, and the compiled unbounded coverage was an operator-norm graph-angle companion.

This module closes the gap by instantiating the abstract chain of
`DavisKahan/TanTheta/Theorem63TrialData.lean` at an `UnboundedTrialBlock`.

## Why the abstract chain applies

The tangent argument never evaluates the ambient operator anywhere except

* on the trial subspace, where an `UnboundedTrialBlock` bundles the action, its
  compression and its residual as *bounded* maps, and
* at vectors `P_{Vᗮ} z` with `z` in the trial subspace, through the crossed quadratic
  form.

Both are available for an unbounded operator whose domain contains the trial subspace and
whose `V` is a spectral subspace: spectral projections preserve the domain
(`selfAdjointSpectralProjection_mem_domain`) and commute with the operator there
(`selfAdjoint_apply_spectralProjection`), so `P_{Vᗮ} z` lies in the domain and
`P_{Vᗮ} (A z) = A (P_{Vᗮ} z)`.  Nothing asks for a bounded ambient operator, and nothing
asks for the quadratic form at a vector where it is undefined.

## The gap hypothesis

`V` is the spectral subspace of `Set.Iic α`, and the lower form bound on `Vᗮ` is the
paper's spectral gap: no spectrum in `Set.Ioo α (α + δ)`.  A vector of `Vᗮ` then has no
spectral mass in `Set.Iic c` for any `c < α + δ`, so the vector-local energy bound applies
at every such `c`, and the constant `α + δ` follows by taking `c` up to it.  The endpoint
`α + δ` itself is allowed to carry spectrum, which is why the argument goes through `c`
rather than applying the bound once.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactTanTheta

open ExactSinTheta
open TanTheta
open Module (finrank)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Trial-block data from an unbounded trial block.**  The action is reassembled from
the bundled compression and residual, so every field is a bounded map even though the
ambient operator is not. -/
noncomputable def Theorem63TrialData.ofUnbounded
    {A : DKClosedOperator (H := H)} {Z : Submodule ℂ H}
    [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : UnboundedTrialBlock A Z) (V : Submodule ℂ H) [V.HasOrthogonalProjection] :
    Theorem63TrialData Z V where
  action := Z.subtypeL ∘L D.operator + D.residual
  compression := D.operator
  residual := D.residual
  compression_isSymmetric := by
    intro x y
    have h := D.operator_selfAdjoint
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at h
    exact h x y
  action_eq := fun z => rfl
  residual_orthogonal := fun z z' =>
    Submodule.inner_left_of_mem_orthogonal z'.2 (D.residual_mem_orthogonal z)

omit [CompleteSpace H] in
/-- The action of the unbounded trial data is the operator's own action. -/
theorem Theorem63TrialData.ofUnbounded_action
    {A : DKClosedOperator (H := H)} {Z : Submodule ℂ H}
    [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : UnboundedTrialBlock A Z) (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (z : Z) :
    (Theorem63TrialData.ofUnbounded D V).action z =
      A.toLinearMap ⟨(z : H), D.domain_le z.property⟩ := by
  have h := D.residual_apply z
  change ((D.operator z : Z) : H) + D.residual z = _
  rw [h]
  abel

section SpectralGap

variable (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)

/-- A spectral projection of a subset of a null set is null. -/
theorem specProjection_eq_zero_of_subset {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : S ⊆ T)
    (hzero : TauCeti.LinearPMap.specProjection hA T hT = 0) :
    TauCeti.LinearPMap.specProjection hA S hS = 0 := by
  have hinter : S ∩ T = S := Set.inter_eq_left.mpr hST
  have hmul := (TauCeti.LinearPMap.spectralPVM hA).proj_inter S T hS hT
  rw [(TauCeti.LinearPMap.spectralPVM hA).proj_congr hinter (hS.inter hT) hS] at hmul
  have hzero' : (TauCeti.LinearPMap.spectralPVM hA).proj T hT = 0 := by
    rw [← TauCeti.LinearPMap.specProjection_def]
    exact hzero
  rw [TauCeti.LinearPMap.specProjection_def, ← hmul, hzero', mul_zero]

/-- **A vector of `Vᗮ` carries no spectral mass below the gap.**

`V` is the spectral subspace of `Set.Iic α`, so `Vᗮ` is the spectral range of
`Set.Ioi α`; intersecting with `Set.Iic c` for `c < α + δ` lands inside the gap. -/
theorem specProjection_Iic_apply_eq_zero_of_gap
    {α δ : ℝ}
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo α (α + δ))
      measurableSet_Ioo = 0)
    {c : ℝ} (hc : c < α + δ) (x : H) :
    TauCeti.LinearPMap.specProjection hA (Set.Iic c) measurableSet_Iic
      (TauCeti.LinearPMap.specProjection hA (Set.Iic α)ᶜ measurableSet_Iic.compl x)
      = 0 := by
  have hmul := (TauCeti.LinearPMap.spectralPVM hA).proj_inter
    (Set.Iic c) (Set.Iic α)ᶜ measurableSet_Iic measurableSet_Iic.compl
  have hset : Set.Iic c ∩ (Set.Iic α)ᶜ = Set.Ioc α c := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_compl_iff, Set.mem_Ioc,
      not_le]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hsub : Set.Ioc α c ⊆ Set.Ioo α (α + δ) := by
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hc⟩
  have hzero : TauCeti.LinearPMap.specProjection hA (Set.Ioc α c)
      measurableSet_Ioc = 0 :=
    specProjection_eq_zero_of_subset A hA measurableSet_Ioc measurableSet_Ioo hsub hgap
  have hcomp : (TauCeti.LinearPMap.spectralPVM hA).proj (Set.Iic c) measurableSet_Iic *
      (TauCeti.LinearPMap.spectralPVM hA).proj (Set.Iic α)ᶜ measurableSet_Iic.compl = 0 := by
    rw [hmul, (TauCeti.LinearPMap.spectralPVM hA).proj_congr hset
      (measurableSet_Iic.inter measurableSet_Iic.compl) measurableSet_Ioc]
    rw [← TauCeti.LinearPMap.specProjection_def]
    exact hzero
  have happ := congrArg (fun L : H →L[ℂ] H => L x) hcomp
  simpa [TauCeti.LinearPMap.specProjection_def] using happ

end SpectralGap

/-- **The crossed form bound for an unbounded self-adjoint operator.**

`V` is the spectral subspace of `Iic α`; the gap hypothesis says the operator has no
spectrum in `Ioo α (α + δ)`.  Then on `Vᗮ` the quadratic form is bounded below by
`α + δ`, which is exactly the hypothesis the abstract chain consumes. -/
theorem crossed_lower_of_spectralGap
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : UnboundedTrialBlock A Z)
    {α δ : ℝ}
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo α (α + δ))
      measurableSet_Ioo = 0)
    (z : Z) :
    (α + δ) * ‖(selfAdjointSpectralSubspace A hA (Set.Iic α)
        measurableSet_Iic)ᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪(selfAdjointSpectralSubspace A hA (Set.Iic α)
          measurableSet_Iic)ᗮ.starProjection ((z : Z) : H),
        (selfAdjointSpectralSubspace A hA (Set.Iic α)
          measurableSet_Iic)ᗮ.starProjection
            ((Theorem63TrialData.ofUnbounded D
              (selfAdjointSpectralSubspace A hA (Set.Iic α)
                measurableSet_Iic)).action z)⟫_ℂ := by
  classical
  -- Replace `Vᗮ.starProjection` by the spectral projection of the complementary set
  -- **in the goal, once, before anything depends on it**: `hydom` below is a proof
  -- about a specific vector, so rewriting under it later would not typecheck.
  have hprojV : (selfAdjointSpectralSubspace A hA (Set.Iic α)
      measurableSet_Iic)ᗮ.starProjection =
      TauCeti.LinearPMap.specProjection hA (Set.Iic α)ᶜ measurableSet_Iic.compl := by
    rw [Submodule.starProjection_orthogonal',
      ← selfAdjointSpectralProjection_eq_starProjection A hA
        (Set.Iic α) measurableSet_Iic,
      TauCeti.LinearPMap.specProjection_def,
      (TauCeti.LinearPMap.spectralPVM hA).proj_compl (Set.Iic α) measurableSet_Iic]
    rfl
  rw [hprojV]
  set Q : H →L[ℂ] H :=
    TauCeti.LinearPMap.specProjection hA (Set.Iic α)ᶜ measurableSet_Iic.compl with hQ_def
  have hzdom : ((z : Z) : H) ∈ A.domain := D.domain_le z.property
  have hydom : Q ((z : Z) : H) ∈ A.domain :=
    selfAdjointSpectralProjection_mem_domain A hA measurableSet_Iic.compl
      ⟨((z : Z) : H), hzdom⟩
  -- The projection commutes with the operator on the domain.
  have hcomm : Q (A.toLinearMap ⟨((z : Z) : H), hzdom⟩) =
      A.toLinearMap ⟨(Q ((z : Z) : H)), hydom⟩ :=
    (selfAdjoint_apply_spectralProjection A hA measurableSet_Iic.compl
      ⟨((z : Z) : H), hzdom⟩).symm
  -- The energy bound, at every threshold strictly below the gap.
  have hstep : ∀ c : ℝ, c < α + δ →
      c * ‖(Q ((z : Z) : H))‖ ^ 2 ≤ (⟪A.toLinearMap ⟨(Q ((z : Z) : H)), hydom⟩, (Q ((z : Z) : H))⟫_ℂ).re := by
    intro c hc
    refine TauCeti.ApproximationNumber.LinearPMap.le_re_inner_of_specProjection_Iic_apply_eq_zero
      hA (c := c) ⟨(Q ((z : Z) : H)), hydom⟩ ?_
    exact specProjection_Iic_apply_eq_zero_of_gap A hA hgap hc ((z : Z) : H)
  -- Take `c` up to `α + δ`.
  have hfinal : (α + δ) * ‖(Q ((z : Z) : H))‖ ^ 2 ≤ (⟪A.toLinearMap ⟨(Q ((z : Z) : H)), hydom⟩, (Q ((z : Z) : H))⟫_ℂ).re := by
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le (sq_nonneg ‖(Q ((z : Z) : H))‖) with hzero | hpos
    · rw [← hzero, mul_zero] at hcon
      have hy0 : (Q ((z : Z) : H)) = 0 := by
        have : ‖(Q ((z : Z) : H))‖ ^ 2 = 0 := hzero.symm
        simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      simp only [hy0, inner_zero_right, Complex.zero_re] at hcon
      exact absurd hcon (lt_irrefl 0)
    · obtain ⟨c, hc1, hc2⟩ := exists_between
        (show (⟪A.toLinearMap ⟨(Q ((z : Z) : H)), hydom⟩, (Q ((z : Z) : H))⟫_ℂ).re / ‖(Q ((z : Z) : H))‖ ^ 2 < α + δ by
          rw [div_lt_iff₀ hpos]
          exact hcon)
      have h := hstep c hc2
      rw [div_lt_iff₀ hpos] at hc1
      linarith
  -- Transfer to the goal.
  have haction : (Theorem63TrialData.ofUnbounded D
      (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic)).action z =
      A.toLinearMap ⟨((z : Z) : H), hzdom⟩ :=
    Theorem63TrialData.ofUnbounded_action D _ z
  rw [haction, hcomm]
  have hre : RCLike.re ⟪(Q ((z : Z) : H)), A.toLinearMap ⟨(Q ((z : Z) : H)), hydom⟩⟫_ℂ =
      (⟪A.toLinearMap ⟨(Q ((z : Z) : H)), hydom⟩, (Q ((z : Z) : H))⟫_ℂ).re := by
    rw [RCLike.re_to_complex, ← inner_conj_symm]
    exact Complex.conj_re _
  rw [hre]
  exact hfinal


/-! ### The unbounded Section 2 tangent theorem -/

/-- **Davis--Kahan Theorem 6.3 for an unbounded self-adjoint operator, at arbitrary
Fan-dominant unitarily invariant ideal gauge.**

`V` is the spectral subspace of `Set.Iic α`; the operator has no spectrum in the gap
`Set.Ioo α (α + δ)`; the Ritz compression of the trial subspace is bounded above by `α`.
The conclusion is the paper's tangent bound `δ · N(tan Θ₀) ≤ N(R)` for **every**
Fan-dominant unitarily invariant ideal gauge, not merely the operator norm.

This is the Section 2 scope claim for the single-angle tangent family: the ambient
operator is closed, unbounded and self-adjoint, and nothing in the statement or the proof
requires it to be bounded. -/
theorem theorem6_3_unbounded_ideal
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    [FiniteDimensional ℂ Z]
    (D : UnboundedTrialBlock A Z)
    {α δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo α (α + δ))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z, RCLike.re ⟪D.operator z, z⟫_ℂ ≤ α * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbers Z
      (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧ δ * N.gauge tanTheta0 ≤ N.gauge D.residual :=
  Theorem63TrialData.ideal_of_formBounds
    (Theorem63TrialData.ofUnbounded D
      (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic))
    N hδ hCompression (crossed_lower_of_spectralGap A hA D hgap) tanTheta0 htan
    hResidual

/-- **The unbounded tangent theorem with the representative exhibited.**

The tangent representative is the one `Theorem63FiniteSource` constructs — diagonal in the
right singular basis of the directed sine block, with entries `tan (arcsin sᵢ)` — and the
`sᵢ < 1` it needs is derived from the same spectral gap, not assumed.  So this carries no
hypothesis the printed theorem does not. -/
theorem theorem6_3_unbounded_ideal_directedTangent
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : DKClosedOperator (H := H)) (hA : A.IsSelfAdjoint)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    [FiniteDimensional ℂ Z]
    (D : UnboundedTrialBlock A Z)
    {α δ : ℝ} (hδ : 0 < δ)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo α (α + δ))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z, RCLike.re ⟪D.operator z, z⟫_ℂ ≤ α * ‖z‖ ^ 2)
    (hResidual : N.Mem D.residual) :
    N.Mem (theorem63DirectedTangent Z
        (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic)) ∧
      δ * N.gauge (theorem63DirectedTangent Z
        (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic)) ≤
        N.gauge D.residual := by
  refine theorem6_3_unbounded_ideal N A hA D hδ hgap hCompression _ ?_ hResidual
  exact hasTheorem63DirectedTangentApproximationNumbers_theorem63DirectedTangent
    Z (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic)
    (fun i => Theorem63TrialData.sine_lt_one_of_formBounds
      (Theorem63TrialData.ofUnbounded D
        (selfAdjointSpectralSubspace A hA (Set.Iic α) measurableSet_Iic))
      hδ hCompression (crossed_lower_of_spectralGap A hA D hgap) i)

end ExactTanTheta
end Experimental
end DavisKahan
end TauCeti
