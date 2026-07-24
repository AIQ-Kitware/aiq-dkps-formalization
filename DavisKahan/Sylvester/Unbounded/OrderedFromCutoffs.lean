/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.Spectra.BoundedTruncation
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Interface-level cutoff mechanics for the ordered unbounded Sylvester proof

This leaf ports the projection, filled-truncation, domain-equation, and strong
Ky Fan limit steps to the coherent cutoff interfaces.  It deliberately stops
before the finite bounded Sylvester estimate.  That remaining estimate is a
separate dependency seam and can be completed without reopening the Spectra
cutoff proofs.
-/

open scoped InnerProductSpace Topology
open Filter

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

abbrev ComplexClosedOperatorOnE :=
  TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)
abbrev ComplexClosedOperatorOnF :=
  TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := F)

/-- Fill the complement of an interface cutoff by a real scalar. -/
noncomputable def interfaceFilledTruncation
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)}
    {hA : A.IsSelfAdjoint}
    (P : GenuineSpectralCutoffInterface A hA)
    (T : GenuineBoundedTruncationInterface A hA P)
    (a τ : ℝ) : H →L[ℂ] H :=
  T.truncation τ + (a : ℂ) •
    (ContinuousLinearMap.id ℂ H - P.cutoff τ)

/-- An interface-filled truncation is symmetric. -/
theorem interfaceFilledTruncation_isSymmetric
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)}
    {hA : A.IsSelfAdjoint}
    (P : GenuineSpectralCutoffInterface A hA)
    (T : GenuineBoundedTruncationInterface A hA P)
    (a τ : ℝ) :
    (interfaceFilledTruncation P T a τ).IsSymmetric := by
  have hT := T.isSymmetric τ
  have hP := (P.isOrthogonalProjection τ).2
  exact hT.add (LinearMap.IsSymmetric.smul (RCLike.conj_ofReal a)
    (LinearMap.IsSymmetric.id.sub hP))

/-- Orthogonality and Pythagoras for an interface cutoff. -/
theorem interfaceCutoff_complement_identities
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)}
    {hA : A.IsSelfAdjoint}
    (P : GenuineSpectralCutoffInterface A hA)
    (τ : ℝ) (x : H) :
    ⟪P.cutoff τ x, x - P.cutoff τ x⟫_ℂ = 0 ∧
      ‖P.cutoff τ x‖ ^ 2 + ‖x - P.cutoff τ x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hP := P.isOrthogonalProjection τ
  have hPP : P.cutoff τ (P.cutoff τ x) = P.cutoff τ x := by
    have h := congrArg (fun S : H →L[ℂ] H => S x) hP.1
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hPQ : P.cutoff τ (x - P.cutoff τ x) = 0 := by
    rw [map_sub, hPP, sub_self]
  have horth : ⟪P.cutoff τ x, x - P.cutoff τ x⟫_ℂ = 0 := by
    calc
      ⟪P.cutoff τ x, x - P.cutoff τ x⟫_ℂ =
          ⟪x, P.cutoff τ (x - P.cutoff τ x)⟫_ℂ :=
        hP.2 x (x - P.cutoff τ x)
      _ = 0 := by simp only [hPQ, inner_zero_right]
  refine ⟨horth, ?_⟩
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (P.cutoff τ x) (x - P.cutoff τ x) horth
  rw [show P.cutoff τ x + (x - P.cutoff τ x) = x by abel] at h
  rw [sq, sq, sq]
  linarith

/-- A lower bound on the cutoff range becomes a global lower bound after
filling the orthogonal complement by the same scalar. -/
theorem interfaceFilledTruncation_lowerBound
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)}
    {hA : A.IsSelfAdjoint}
    (P : GenuineSpectralCutoffInterface A hA)
    (T : GenuineBoundedTruncationInterface A hA P)
    {a τ : ℝ} (hτ : 0 ≤ τ) (ha : SemiboundedBelow A a) :
    ∀ x, a * ‖x‖ ^ 2 ≤
      RCLike.re ⟪interfaceFilledTruncation P T a τ x, x⟫_ℂ := by
  intro x
  have hproj := interfaceCutoff_complement_identities P τ x
  have hcomm := T.commutes_cutoff τ
  have hPT : P.cutoff τ (T.truncation τ x) = T.truncation τ x := by
    have h := congrArg (fun S : H →L[ℂ] H => S x) hcomm.2
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hPP : P.cutoff τ (P.cutoff τ x) = P.cutoff τ x := by
    have h := congrArg (fun S : H →L[ℂ] H => S x)
      (P.isOrthogonalProjection τ).1
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hPQ : P.cutoff τ (x - P.cutoff τ x) = 0 := by
    rw [map_sub, hPP, sub_self]
  have hTorth : ⟪T.truncation τ x, x - P.cutoff τ x⟫_ℂ = 0 := by
    calc
      ⟪T.truncation τ x, x - P.cutoff τ x⟫_ℂ =
          ⟪P.cutoff τ (T.truncation τ x), x - P.cutoff τ x⟫_ℂ := by
        rw [hPT]
      _ = ⟪T.truncation τ x, P.cutoff τ (x - P.cutoff τ x)⟫_ℂ :=
        (P.isOrthogonalProjection τ).2
          (T.truncation τ x) (x - P.cutoff τ x)
      _ = 0 := by simp only [hPQ, inner_zero_right]
  have hQorth : ⟪x - P.cutoff τ x, P.cutoff τ x⟫_ℂ = 0 := by
    rw [← inner_conj_symm, hproj.1, map_zero]
  have hx : x = P.cutoff τ x + (x - P.cutoff τ x) := by abel
  have hTinner : RCLike.re ⟪T.truncation τ x, x⟫_ℂ =
      RCLike.re ⟪T.truncation τ x, P.cutoff τ x⟫_ℂ := by
    calc
      RCLike.re ⟪T.truncation τ x, x⟫_ℂ =
          RCLike.re ⟪T.truncation τ x,
            P.cutoff τ x + (x - P.cutoff τ x)⟫_ℂ :=
        congrArg RCLike.re
          (congrArg (fun y => ⟪T.truncation τ x, y⟫_ℂ) hx)
      _ = RCLike.re ⟪T.truncation τ x, P.cutoff τ x⟫_ℂ := by
        rw [inner_add_right, map_add, hTorth, map_zero, add_zero]
  have hQinner : RCLike.re ⟪x - P.cutoff τ x, x⟫_ℂ =
      ‖x - P.cutoff τ x‖ ^ 2 := by
    calc
      RCLike.re ⟪x - P.cutoff τ x, x⟫_ℂ =
          RCLike.re ⟪x - P.cutoff τ x,
            P.cutoff τ x + (x - P.cutoff τ x)⟫_ℂ :=
        congrArg RCLike.re
          (congrArg (fun y => ⟪x - P.cutoff τ x, y⟫_ℂ) hx)
      _ = ‖x - P.cutoff τ x‖ ^ 2 := by
        rw [inner_add_right, map_add, hQorth, map_zero, zero_add,
          inner_self_eq_norm_sq]
  have hcut := T.lowerBound ha hτ x
  change a * ‖x‖ ^ 2 ≤
    RCLike.re ⟪T.truncation τ x +
      (a : ℂ) • (x - P.cutoff τ x), x⟫_ℂ
  have hre : ∀ w : ℂ, RCLike.re ((a : ℂ) * w) = a * RCLike.re w := by
    intro w
    simp [RCLike.re_to_complex, Complex.mul_re]
  rw [inner_add_left, map_add, inner_smul_left, Complex.conj_ofReal,
    hre, hTinner, hQinner]
  rw [← hproj.2]
  linarith

/-- An upper bound on the cutoff range becomes a global upper bound after
filling the orthogonal complement by the same scalar. -/
theorem interfaceFilledTruncation_upperBound
    {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)}
    {hA : A.IsSelfAdjoint}
    (P : GenuineSpectralCutoffInterface A hA)
    (T : GenuineBoundedTruncationInterface A hA P)
    {a τ : ℝ} (hτ : 0 ≤ τ) (ha : SemiboundedAbove A a) :
    ∀ x, RCLike.re ⟪interfaceFilledTruncation P T a τ x, x⟫_ℂ ≤
      a * ‖x‖ ^ 2 := by
  intro x
  have hproj := interfaceCutoff_complement_identities P τ x
  have hcomm := T.commutes_cutoff τ
  have hPT : P.cutoff τ (T.truncation τ x) = T.truncation τ x := by
    have h := congrArg (fun S : H →L[ℂ] H => S x) hcomm.2
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hPP : P.cutoff τ (P.cutoff τ x) = P.cutoff τ x := by
    have h := congrArg (fun S : H →L[ℂ] H => S x)
      (P.isOrthogonalProjection τ).1
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hPQ : P.cutoff τ (x - P.cutoff τ x) = 0 := by
    rw [map_sub, hPP, sub_self]
  have hTorth : ⟪T.truncation τ x, x - P.cutoff τ x⟫_ℂ = 0 := by
    calc
      ⟪T.truncation τ x, x - P.cutoff τ x⟫_ℂ =
          ⟪P.cutoff τ (T.truncation τ x), x - P.cutoff τ x⟫_ℂ := by
        rw [hPT]
      _ = ⟪T.truncation τ x, P.cutoff τ (x - P.cutoff τ x)⟫_ℂ :=
        (P.isOrthogonalProjection τ).2
          (T.truncation τ x) (x - P.cutoff τ x)
      _ = 0 := by simp only [hPQ, inner_zero_right]
  have hQorth : ⟪x - P.cutoff τ x, P.cutoff τ x⟫_ℂ = 0 := by
    rw [← inner_conj_symm, hproj.1, map_zero]
  have hx : x = P.cutoff τ x + (x - P.cutoff τ x) := by abel
  have hTinner : RCLike.re ⟪T.truncation τ x, x⟫_ℂ =
      RCLike.re ⟪T.truncation τ x, P.cutoff τ x⟫_ℂ := by
    calc
      RCLike.re ⟪T.truncation τ x, x⟫_ℂ =
          RCLike.re ⟪T.truncation τ x,
            P.cutoff τ x + (x - P.cutoff τ x)⟫_ℂ :=
        congrArg RCLike.re
          (congrArg (fun y => ⟪T.truncation τ x, y⟫_ℂ) hx)
      _ = RCLike.re ⟪T.truncation τ x, P.cutoff τ x⟫_ℂ := by
        rw [inner_add_right, map_add, hTorth, map_zero, add_zero]
  have hQinner : RCLike.re ⟪x - P.cutoff τ x, x⟫_ℂ =
      ‖x - P.cutoff τ x‖ ^ 2 := by
    calc
      RCLike.re ⟪x - P.cutoff τ x, x⟫_ℂ =
          RCLike.re ⟪x - P.cutoff τ x,
            P.cutoff τ x + (x - P.cutoff τ x)⟫_ℂ :=
        congrArg RCLike.re
          (congrArg (fun y => ⟪x - P.cutoff τ x, y⟫_ℂ) hx)
      _ = ‖x - P.cutoff τ x‖ ^ 2 := by
        rw [inner_add_right, map_add, hQorth, map_zero, zero_add,
          inner_self_eq_norm_sq]
  have hcut := T.upperBound ha hτ x
  change RCLike.re ⟪T.truncation τ x +
      (a : ℂ) • (x - P.cutoff τ x), x⟫_ℂ ≤ a * ‖x‖ ^ 2
  have hre : ∀ w : ℂ, RCLike.re ((a : ℂ) * w) = a * RCLike.re w := by
    intro w
    simp [RCLike.re_to_complex, Complex.mul_re]
  rw [inner_add_left, map_add, inner_smul_left, Complex.conj_ofReal,
    hre, hTinner, hQinner]
  rw [← hproj.2]
  linarith

section ApproximationNumberEndpointAssumptions

variable [HasApproximationNumberStrongCutoff.{0, v, 0} ℂ]
variable [HasKyFanApproximationGaugeTriangle.{0, v} ℂ]

/-- Right interface-cutoff inequalities pass to the uncut operators. -/
theorem kyFan_le_of_interfaceRightCutoff_le
    {B : ComplexClosedOperatorOnF (F := F)}
    {hB : B.IsSelfAdjoint}
    (P : GenuineSpectralCutoffInterface B hB)
    {X C : F →L[ℂ] E} {δ : ℝ} (k : ℕ)
    (hcut : ∀ τ : ℝ, 0 ≤ τ →
      δ * kyFanApproximationGauge k (X ∘L P.cutoff τ) ≤
        kyFanApproximationGauge k (C ∘L P.cutoff τ)) :
    δ * kyFanApproximationGauge k X ≤ kyFanApproximationGauge k C := by
  have hPproj : ∀ τ : ℝ, IsOrthogonalProjectionMap (P.cutoff τ) :=
    P.isOrthogonalProjection
  have hPstrong : StronglyTendsto (fun τ : ℝ => P.cutoff τ) atTop
      (ContinuousLinearMap.id ℂ F) := by
    intro x
    simpa using P.tendsto_identity x
  have hX := kyFanApproximationGauge_comp_strongProjection_tendsto
    hPproj hPstrong k X
  have hC := kyFanApproximationGauge_comp_strongProjection_tendsto
    hPproj hPstrong k C
  have hcutEventually : ∀ᶠ τ : ℝ in atTop,
      δ * kyFanApproximationGauge k (X ∘L P.cutoff τ) ≤
        kyFanApproximationGauge k (C ∘L P.cutoff τ) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact hcut τ hτ
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul hX) hC hcutEventually

/-- Finite Ky Fan gauges converge under strong orthogonal cutoffs on the target
side. -/
theorem kyFan_left_comp_interfaceCutoff_tendsto
    {ι : Type} {P : ι → E →L[ℂ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℂ E))
    (k : ℕ) (K : F →L[ℂ] E) :
    Tendsto (fun i => kyFanApproximationGauge k (P i ∘L K)) l
      (𝓝 (kyFanApproximationGauge k K)) := by
  have hright := kyFanApproximationGauge_comp_strongProjection_tendsto
    hPproj hP k K.adjoint
  have hpoint : ∀ i,
      kyFanApproximationGauge k (P i ∘L K) =
        kyFanApproximationGauge k (K.adjoint ∘L P i) := by
    intro i
    rw [← kyFanApproximationGauge_adjoint k (P i ∘L K)]
    simp only [ContinuousLinearMap.adjoint_comp]
    rw [(hPproj i).2.clm_adjoint_eq]
  have hlimit : kyFanApproximationGauge k K =
      kyFanApproximationGauge k K.adjoint := by
    symm
    exact kyFanApproximationGauge_adjoint k K
  simpa only [hpoint, hlimit] using hright

/-- Left interface-cutoff inequalities pass to the uncut operators. -/
theorem kyFan_le_of_interfaceLeftCutoff_le
    {A : ComplexClosedOperatorOnE (E := E)}
    {hA : A.IsSelfAdjoint}
    (P : GenuineSpectralCutoffInterface A hA)
    {X C : F →L[ℂ] E} {δ : ℝ} (k : ℕ)
    (hcut : ∀ τ : ℝ, 0 ≤ τ →
      δ * kyFanApproximationGauge k (P.cutoff τ ∘L X) ≤
        kyFanApproximationGauge k (P.cutoff τ ∘L C)) :
    δ * kyFanApproximationGauge k X ≤ kyFanApproximationGauge k C := by
  have hPproj : ∀ τ : ℝ, IsOrthogonalProjectionMap (P.cutoff τ) :=
    P.isOrthogonalProjection
  have hPstrong : StronglyTendsto (fun τ : ℝ => P.cutoff τ) atTop
      (ContinuousLinearMap.id ℂ E) := by
    intro x
    simpa using P.tendsto_identity x
  have hX := kyFan_left_comp_interfaceCutoff_tendsto hPproj hPstrong k X
  have hC := kyFan_left_comp_interfaceCutoff_tendsto hPproj hPstrong k C
  have hcutEventually : ∀ᶠ τ : ℝ in atTop,
      δ * kyFanApproximationGauge k (P.cutoff τ ∘L X) ≤
        kyFanApproximationGauge k (P.cutoff τ ∘L C) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact hcut τ hτ
  exact le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul hX) hC hcutEventually

/-- Double interface cutoff turns a domain-aware equation into a bounded
Sylvester equation between the filled truncations. -/
theorem interfaceDoubleCutoff_sylvester_equation
    {A : ComplexClosedOperatorOnE (E := E)}
    {B : ComplexClosedOperatorOnF (F := F)}
    {hA : A.IsSelfAdjoint} {hB : B.IsSelfAdjoint}
    (PAi : GenuineSpectralCutoffInterface A hA)
    (TAi : GenuineBoundedTruncationInterface A hA PAi)
    (PBi : GenuineSpectralCutoffInterface B hB)
    (TBi : GenuineBoundedTruncationInterface B hB PBi)
    {X C : F →L[ℂ] E}
    (hEq : HasClosedSylvesterEquation A B X C)
    (a b τA τB : ℝ) :
    interfaceFilledTruncation PAi TAi a τA ∘L
        (PAi.cutoff τA ∘L X ∘L PBi.cutoff τB) -
      (PAi.cutoff τA ∘L X ∘L PBi.cutoff τB) ∘L
        interfaceFilledTruncation PBi TBi b τB =
      PAi.cutoff τA ∘L C ∘L PBi.cutoff τB := by
  let PA : E →L[ℂ] E := PAi.cutoff τA
  let PB : F →L[ℂ] F := PBi.cutoff τB
  let TA : E →L[ℂ] E := TAi.truncation τA
  let TB : F →L[ℂ] F := TBi.truncation τB
  have hPAidem := (PAi.isOrthogonalProjection τA).1
  have hPBidem := (PBi.isOrthogonalProjection τB).1
  have hTAcomm := TAi.commutes_cutoff τA
  have hTBcomm := TBi.commutes_cutoff τB
  ext x
  have hPBdom : PB x ∈ B.domain :=
    PBi.range_le_domain τB ⟨x, rfl⟩
  have hXdom : X (PB x) ∈ A.domain :=
    hEq.mapsTo_domain ⟨PB x, hPBdom⟩
  obtain ⟨hPAxdom, hAcomm⟩ :=
    PAi.commutes_on_domain τA ⟨X (PB x), hXdom⟩
  obtain ⟨_hPAcutdom, hTAcut⟩ :=
    TAi.eq_on_cutoff τA (X (PB x))
  obtain ⟨_hPBcutdom, hTBcut⟩ := TBi.eq_on_cutoff τB x
  have hPAPAx : PA (PA (X (PB x))) = PA (X (PB x)) := by
    have h := congrArg (fun S : E →L[ℂ] E => S (X (PB x))) hPAidem
    simpa only [PA, ContinuousLinearMap.comp_apply] using h
  have hPBPBx : PB (PB x) = PB x := by
    have h := congrArg (fun S : F →L[ℂ] F => S x) hPBidem
    simpa only [PB, ContinuousLinearMap.comp_apply] using h
  have hTAPA : TA (PA (X (PB x))) = TA (X (PB x)) := by
    have h := congrArg (fun S : E →L[ℂ] E => S (X (PB x))) hTAcomm.1
    simpa only [TA, PA, ContinuousLinearMap.comp_apply] using h
  have hPBTB : PB (TB x) = TB x := by
    have h := congrArg (fun S : F →L[ℂ] F => S x) hTBcomm.2
    simpa only [PB, TB, ContinuousLinearMap.comp_apply] using h
  have hPBFilled :
      PB (interfaceFilledTruncation PBi TBi b τB x) = TB x := by
    change PB (TB x + (b : ℂ) • (x - PB x)) = TB x
    rw [map_add, map_smul, hPBTB, map_sub, hPBPBx, sub_self,
      smul_zero, add_zero]
  have hAFilled :
      interfaceFilledTruncation PAi TAi a τA (PA (X (PB x))) =
        PA (A.toLinearMap ⟨X (PB x), hXdom⟩) := by
    change TA (PA (X (PB x))) +
        (a : ℂ) • (PA (X (PB x)) - PA (PA (X (PB x)))) =
      PA (A.toLinearMap ⟨X (PB x), hXdom⟩)
    rw [hTAPA, hPAPAx, sub_self, smul_zero, add_zero]
    rw [hTAcut]
    exact hAcomm
  have heq := hEq.equation ⟨PB x, hPBdom⟩
  have heqPA := congrArg PA heq
  change
    interfaceFilledTruncation PAi TAi a τA (PA (X (PB x))) -
      PA (X (PB (interfaceFilledTruncation PBi TBi b τB x))) =
        PA (C (PB x))
  rw [hAFilled, hPBFilled]
  rw [show TB x = B.toLinearMap ⟨PB x, hPBdom⟩ by
    simpa only [TB, PB] using hTBcut]
  simpa only [map_sub] using heqPA

end ApproximationNumberEndpointAssumptions

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti