/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.GenuineUnbounded
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The honest unbounded `sin Θ` layer: unitary-invariant ideal scope

Ideal-gauge companion to `SinTheta/GenuineUnbounded.lean`, lifting the
operator-norm unbounded `sin Θ` endpoint to the paper's unitary-invariant
norm scope over any `RectangularSymmetricIdealFamily`.

Main results, all fully proved:

* `exists_bounded_shift_extension`: a symmetric closed operator whose
  quadratic form lies in `[β, α]` admits a bounded extension of its shift
  by the center `c = (α+β)/2`, of norm at most the radius `r = (α-β)/2` —
  the continuous extension along the dense domain embedding of the shifted
  graph map.
* `mem_and_gauge_le_of_boundedLeft_exteriorRight`: the ideal-gauge
  constant-one Sylvester estimate in the `sin Θ` orientation — bounded
  interval block on the left (through its shift extension), exterior closed
  block on the right through a proof-carrying bounded shifted right inverse.
  The solution is exhibited as the ideal-gauge limit of the Neumann
  iteration `Y = S Y J - C J`, membership coming from the family's
  `gauge_complete` field and operator-norm limit uniqueness.
* `sinTheta_unbounded_gauge`: **the unbounded Davis--Kahan `sin Θ` theorem
  at unitary-invariant ideal scope** — for the paper-shaped
  `UnboundedSinThetaData` with the trial block's form in `[β, α]`, the
  complementary block's shifted resolvent bounded by `((α-β)/2 + δ)⁻¹`,
  and the projected residual in the ideal, the projected angle operator is
  in the ideal with `δ ‖X⋆ F₁‖_N ≤ ‖R⋆ F₁‖_N`.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **Bounded extension of the centered interval block.**  A symmetric closed
operator whose quadratic form lies in `[β, α]` has a bounded shift `B - c`
on its dense domain (`c = (α+β)/2`, radius `r = (α-β)/2`), which therefore
extends to a bounded operator on the whole space with the same norm bound
and agreeing with `B - c` on the domain. -/
theorem exists_bounded_shift_extension
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    (hsym : B.IsSymmetric) {β α : ℝ} (hβα : β ≤ α)
    (hlow : SemiboundedBelow B β) (hhigh : SemiboundedAbove B α) :
    ∃ S : F →L[𝕜] F, ‖S‖ ≤ (α - β) / 2 ∧
      ∀ y : B.domain, S (y : F) =
        B.toLinearMap y - (((α + β) / 2 : ℝ) : 𝕜) • (y : F) := by
  have hr0 : (0 : ℝ) ≤ (α - β) / 2 := by linarith
  set g : B.domain →ₗ[𝕜] F :=
    B.toLinearMap - (((α + β) / 2 : ℝ) : 𝕜) • B.domain.subtype with hgdef
  have hgapply : ∀ y : B.domain,
      g y = B.toLinearMap y - (((α + β) / 2 : ℝ) : 𝕜) • (y : F) := by
    intro y
    simp [hgdef, LinearMap.sub_apply, LinearMap.smul_apply]
  have hgbound : ∀ y : B.domain, ‖g y‖ ≤ (α - β) / 2 * ‖y‖ := by
    intro y
    rw [hgapply y]
    exact ForMathlib.DavisKahanExt.ClosedOperator.norm_shift_apply_le_of_form_bounds
      hsym hβα hlow hhigh y
  set f : B.domain →L[𝕜] F := g.mkContinuous ((α - β) / 2) hgbound with hfdef
  have hrange : Set.range ((B.domain.subtypeL : B.domain →L[𝕜] F)) =
      (B.domain : Set F) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hdense : DenseRange ((B.domain.subtypeL : B.domain →L[𝕜] F)) := by
    show Dense (Set.range _)
    rw [hrange]
    exact B.dense_domain
  have hui : IsUniformInducing ((B.domain.subtypeL : B.domain →L[𝕜] F)) :=
    isometry_subtype_coe.isUniformInducing
  refine ⟨f.extend (B.domain.subtypeL), ?_, ?_⟩
  · have h1 : ‖f.extend (B.domain.subtypeL)‖ ≤ ((1 : NNReal) : ℝ) * ‖f‖ := by
      refine ContinuousLinearMap.opNorm_extend_le f hdense fun x => ?_
      rw [NNReal.coe_one, one_mul]
      exact le_of_eq rfl
    have h2 : ‖f‖ ≤ (α - β) / 2 :=
      LinearMap.mkContinuous_norm_le g hr0 hgbound
    calc ‖f.extend (B.domain.subtypeL)‖
        ≤ ((1 : NNReal) : ℝ) * ‖f‖ := h1
      _ = ‖f‖ := by rw [NNReal.coe_one, one_mul]
      _ ≤ (α - β) / 2 := h2
  · intro y
    have h := ContinuousLinearMap.extend_eq f hdense hui y
    calc (f.extend (B.domain.subtypeL)) (y : F)
        = f y := h
      _ = B.toLinearMap y - (((α + β) / 2 : ℝ) : 𝕜) • (y : F) := hgapply y

/- The two one-unbounded Neumann engines and the bounded-realization
transfer lemma live in `Core.UnboundedSpectral`, below this source-facing
assembly layer. -/

/-- **Ideal-gauge interval/exterior Sylvester estimate, exterior block on
the left.**  The interval block `B` (quadratic form in `[β, α]`) is realized
bounded through its shift extension and the equation transfers by density;
the exterior block `A` carries a proof-carrying two-sided shifted inverse.
Both closed blocks may be genuinely unbounded a priori. -/
theorem mem_and_gauge_le_of_exteriorLeft_intervalRight
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    {X C : F →L[𝕜] E} {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hBsym : B.IsSymmetric)
    (hBlow : SemiboundedBelow B β) (hBhigh : SemiboundedAbove B α)
    (hAres : TwoSidedShiftedInverseBound A ((α + β) / 2)
      ((α - β) / 2 + δ))
    (hEq : HasClosedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  have hr0 : (0 : ℝ) ≤ (α - β) / 2 := by linarith
  obtain ⟨S, hSnorm, hSeq⟩ :=
    exists_bounded_shift_extension hBsym hβα hBlow hBhigh
  obtain ⟨J, hdom, hleft, hright, hJnorm⟩ := hAres
  -- the bounded realization of `B` and the transferred equation
  set T : F →L[𝕜] F :=
    S + (((α + β) / 2 : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 F with hTdef
  have hT : ∀ y : B.domain, T (y : F) = B.toLinearMap y := by
    intro y
    simp only [hTdef, add_apply, smul_apply, ContinuousLinearMap.id_apply]
    rw [hSeq y]
    abel
  have hEqT : HasUnboundedBoundedSylvesterEquation A T X C :=
    closedSylvesterEquation_boundedRealization hEq hT
  -- shift both blocks by the center
  set c𝕜 : 𝕜 := (((α + β) / 2 : ℝ) : 𝕜) with hc𝕜
  set A' : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E) :=
    A.addBounded (-(c𝕜 • ContinuousLinearMap.id 𝕜 E)) with hA'def
  have hA'domain : A'.domain = A.domain := rfl
  have hA'apply : ∀ x : A.domain,
      A'.toLinearMap x = A.toLinearMap x - c𝕜 • (x : E) := by
    intro x
    change A.toLinearMap x + (-(c𝕜 • ContinuousLinearMap.id 𝕜 E)) (x : E) =
      A.toLinearMap x - c𝕜 • (x : E)
    simp [sub_eq_add_neg]
  have hEq' : HasUnboundedBoundedSylvesterEquation A' S X C := by
    refine ⟨fun x => hEqT.mapsTo_domain x, fun x => ?_⟩
    have h1 : A.toLinearMap ⟨X (x : F), hEqT.mapsTo_domain x⟩ -
        X (T (x : F)) = C (x : F) := hEqT.equation x
    have h2 : A'.toLinearMap ⟨X (x : F), hEqT.mapsTo_domain x⟩ =
        A.toLinearMap ⟨X (x : F), hEqT.mapsTo_domain x⟩ -
          c𝕜 • X (x : F) :=
      hA'apply ⟨X (x : F), hEqT.mapsTo_domain x⟩
    have h3 : X (S (x : F)) = X (T (x : F)) - c𝕜 • X (x : F) := by
      have : S (x : F) = T (x : F) - c𝕜 • (x : F) := by
        simp only [hTdef, add_apply, smul_apply, ContinuousLinearMap.id_apply]
        abel
      rw [this, map_sub, map_smul]
    change A'.toLinearMap ⟨X (x : F), hEqT.mapsTo_domain x⟩ -
      X (S (x : F)) = C (x : F)
    rw [h2, h3, ← h1]
    abel
  -- the everywhere-defined inverse of the shifted exterior block
  refine sylvester_mem_and_gauge_le_of_unbounded_bound_inverse N
    (⟨J, hdom, ?_, ?_⟩ : HasBoundedEverywhereInverse A') S hr0 hδ
    hJnorm hSnorm hEq' hC
  · intro y
    change A.toLinearMap ⟨J y, hdom y⟩ + -(c𝕜 • J y) = y
    have h := hright y
    rw [sub_eq_add_neg] at h
    exact h
  · intro x
    change J (A.toLinearMap x + -(c𝕜 • (x : E))) = (x : E)
    have h := hleft x
    rw [sub_eq_add_neg] at h
    exact h

/-- **The unbounded Davis--Kahan `sin Θ` theorem at unitary-invariant ideal
scope.**  For the paper-shaped `UnboundedSinThetaData` with the trial
block's quadratic form in `[β, α]` and the complementary block's shifted
resolvent bounded by `((α-β)/2 + δ)⁻¹`, if the projected residual
`R⋆ ∘ F₁` lies in the rectangular symmetric ideal family `N`, then so does
`X⋆ ∘ F₁`, with `δ · gauge (X⋆ ∘ F₁) ≤ gauge (R⋆ ∘ F₁)`. -/
theorem sinTheta_unbounded_gauge
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : SemiboundedBelow D.A₀ β) (hA₀high : SemiboundedAbove D.A₀ α)
    (hΛres : TwoSidedShiftedInverseBound D.Λ₁ ((α + β) / 2)
      ((α - β) / 2 + δ))
    (hC : N.Mem (D.residual.adjoint ∘L D.F₁)) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤
        N.gauge (D.residual.adjoint ∘L D.F₁) := by
  obtain ⟨S, hSnorm, hSeq⟩ :=
    exists_bounded_shift_extension hA₀.isSymmetric hβα hA₀low hA₀high
  obtain ⟨J, hdom, _hleft, hright, hJnorm⟩ := hΛres
  have hEqu := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hρ : (0 : ℝ) ≤ (α - β) / 2 := by linarith
  have hEq' : ∀ y : D.Λ₁.domain,
      S ((D.X.adjoint ∘L D.F₁) (y : G)) -
        ((D.X.adjoint ∘L D.F₁) (D.Λ₁.toLinearMap y) -
          (((α + β) / 2 : ℝ) : 𝕜) • (D.X.adjoint ∘L D.F₁) (y : G)) =
      (-(D.residual.adjoint ∘L D.F₁)) (y : G) := by
    intro y
    have h1 := hEqu.equation y
    have h2 := hSeq ⟨(D.X.adjoint ∘L D.F₁) (y : G), hEqu.mapsTo_domain y⟩
    rw [h2]
    calc D.A₀.toLinearMap
          ⟨(D.X.adjoint ∘L D.F₁) (y : G), hEqu.mapsTo_domain y⟩ -
            (((α + β) / 2 : ℝ) : 𝕜) • (D.X.adjoint ∘L D.F₁) (y : G) -
          ((D.X.adjoint ∘L D.F₁) (D.Λ₁.toLinearMap y) -
            (((α + β) / 2 : ℝ) : 𝕜) • (D.X.adjoint ∘L D.F₁) (y : G))
        = D.A₀.toLinearMap
            ⟨(D.X.adjoint ∘L D.F₁) (y : G), hEqu.mapsTo_domain y⟩ -
          (D.X.adjoint ∘L D.F₁) (D.Λ₁.toLinearMap y) := by abel
      _ = (-(D.residual.adjoint ∘L D.F₁)) (y : G) := h1
  have hmain := mem_and_gauge_le_of_boundedLeft_exteriorRight N hρ hδ
    hSnorm hdom hright hJnorm hEq' (N.neg_mem hC)
  refine ⟨hmain.1, ?_⟩
  have hgC : N.gauge (-(D.residual.adjoint ∘L D.F₁)) =
      N.gauge (D.residual.adjoint ∘L D.F₁) := N.gauge_neg hC
  calc δ * N.gauge (D.X.adjoint ∘L D.F₁)
      ≤ N.gauge (-(D.residual.adjoint ∘L D.F₁)) := hmain.2
    _ = N.gauge (D.residual.adjoint ∘L D.F₁) := hgC

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
