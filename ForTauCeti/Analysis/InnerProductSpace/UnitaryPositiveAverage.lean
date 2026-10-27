/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import ForTauCeti.Analysis.CStarAlgebra.PositiveSquareRootCommute
public import TauCeti.Analysis.Normed.Operator.RealAlgebra

/-!
# Two unitaries with a positive average

Both summands commute with their positive average C. Their discrepancy
from being adjoints is annihilated by C, and hence vanishes if C is
injective. The kernel exception is essential: when C=0 the two
summands are negatives of one another and need not be adjoints.

This is a reusable algebraic step toward nuclear transport optimizer
parametrization. It does not itself identify transporter blocks.

## Provenance

Developed in the DKPS formalization for the nuclear optimizer classification,
with a new direct proof from unitary identities and the existing positive
square-root commutation lemma. No proof is copied from an external source,
and no Spectra implementation is involved. This is local research donor
mathematics, not an assertion of historical priority or accepted roadmap
ownership; submission requires a separately justified roadmap target.
-/

public section

noncomputable section

namespace TauCeti.ContinuousLinearMap

attribute [local instance] _root_.ContinuousLinearMap.realAlgebra
  _root_.ContinuousLinearMap.realIsScalarTower

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Two unitaries whose average is positive both commute with it, and
can fail to be adjoints only through its kernel. Neither invertibility
nor a spectral gap nor finite dimension is assumed. -/
theorem unitary_positive_average_structure (C U W : E →L[𝕜] E)
    (hC : C.IsPositive) (hU : U ∈ unitary (E →L[𝕜] E))
    (hW : W ∈ unitary (E →L[𝕜] E)) (hsum : U + W = C + C) :
    Commute C U ∧ Commute C W ∧ C * (U - star W) = 0 := by
  have hstar : star U + star W = C + C := by
    simpa only [star_add, hC.isSelfAdjoint.star_eq] using congrArg star hsum
  have hcancel (A B : E →L[𝕜] E) (h : A + A = B + B) : A = B := by
    apply smul_right_injective (E →L[𝕜] E) (by norm_num : (2 : ℝ) ≠ 0)
    simpa only [two_smul] using h
  have hUW : U * C = C * star W := by
    apply hcancel
    have h : U * (C + C) = (C + C) * star W := by
      calc
        _ = U * (star U + star W) := by rw [hstar]
        _ = 1 + U * star W := by rw [mul_add, Unitary.mul_star_self_of_mem hU]
        _ = (U + W) * star W := by rw [add_mul, Unitary.mul_star_self_of_mem hW, add_comm]
        _ = _ := by rw [hsum]
    simpa only [mul_add, add_mul] using h
  have hWU : star W * C = C * U := by
    apply hcancel
    have h : star W * (C + C) = (C + C) * U := by
      calc
        _ = star W * (U + W) := by rw [hsum]
        _ = star W * U + 1 := by rw [mul_add, Unitary.star_mul_self_of_mem hW]
        _ = (star U + star W) * U := by rw [add_mul, Unitary.star_mul_self_of_mem hU, add_comm]
        _ = _ := by rw [hstar]
    simpa only [mul_add, add_mul] using h
  have hsquare : Commute (C * C) U := by
    change (C * C) * U = U * (C * C)
    calc
      _ = C * (C * U) := mul_assoc _ _ _
      _ = C * (star W * C) := by rw [hWU]
      _ = (C * star W) * C := (mul_assoc _ _ _).symm
      _ = (U * C) * C := by rw [hUW]
      _ = _ := mul_assoc _ _ _
  have hCU : Commute C U := TauCeti.commute_of_commute_mul_self
    ((_root_.ContinuousLinearMap.nonneg_iff_isPositive).mpr hC) hsquare
  have hWexp : W = (C + C) - U := by rw [← hsum]; abel
  have hCW : Commute C W := by
    rw [hWexp]
    exact ((Commute.refl C).add_right (Commute.refl C)).sub_right hCU
  refine ⟨hCU, hCW, ?_⟩
  rw [mul_sub, hCU.eq, hUW, sub_self]

/-- If the positive average is injective, its two unitary summands
are adjoints. Injectivity suffices even without a bounded inverse. -/
theorem unitary_eq_adjoint_of_positive_average_injective (C U W : E →L[𝕜] E)
    (hC : C.IsPositive) (hU : U ∈ unitary (E →L[𝕜] E))
    (hW : W ∈ unitary (E →L[𝕜] E)) (hsum : U + W = C + C)
    (hinj : Function.Injective C) : U = star W := by
  have h := (unitary_positive_average_structure C U W hC hU hW hsum).2.2
  rw [mul_sub, sub_eq_zero] at h
  ext x
  exact hinj (congrArg (fun A : E →L[𝕜] E => A x) h)

/-- On the orthogonal complement of the average's kernel, the summands
are adjoints even when the average has no bounded inverse. This keeps
the exceptional zero-cosine sector separate without discarding it. -/
theorem unitary_positive_average_adjoint_on_support (C U W : E →L[𝕜] E)
    (hC : C.IsPositive) (hU : U ∈ unitary (E →L[𝕜] E))
    (hW : W ∈ unitary (E →L[𝕜] E)) (hsum : U + W = C + C)
    (x : E) (hx : x ∈ C.kerᗮ) : U x = (star W) x := by
  obtain ⟨hCU, hCW, hzero⟩ := unitary_positive_average_structure C U W hC hU hW hsum
  let A := U - star W
  have hCstarW : Commute C (star W) := by
    change C * star W = star W * C
    have h := congrArg star hCW.eq
    simpa only [star_mul, hC.isSelfAdjoint.star_eq] using h.symm
  have hCA : Commute C A := hCU.sub_right hCstarW
  have hAC : A * C = 0 := hCA.eq.symm.trans hzero
  have hCadj : C * star A = 0 := by
    have h := congrArg star hAC
    simpa only [star_mul, hC.isSelfAdjoint.star_eq, star_zero] using h
  have hmem : A.adjoint (A x) ∈ C.ker := by
    change C (A.adjoint (A x)) = 0
    exact congrArg (fun T : E →L[𝕜] E => T (A x)) hCadj
  have hinner := hx _ hmem
  rw [A.adjoint_inner_left] at hinner
  have hAx : A x = 0 := inner_self_eq_zero.mp hinner
  exact sub_eq_zero.mp hAx

end TauCeti.ContinuousLinearMap
