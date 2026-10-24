/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Modulus
public import Mathlib.Algebra.Star.Unitary

/-!
# Rigidity of a positive average of two unitary operators

If `U + V = 2 D` with `D` positive, both unitaries commute with `D`.
On its range they are adjoints of one another; on its kernel they are
negatives. This separates the acute and right-angle cases of the smoothed
transport equality problem. The result permits infinite-dimensional real
or complex Hilbert spaces and does not assume that the range is closed.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A positive average forces each of its unitary summands to preserve
every spectral subspace of the average. -/
theorem commute_of_unitary_sum_eq_two_smul
    (U V : unitary (E →L[𝕜] E)) (D : E →L[𝕜] E) (hD : D.IsPositive)
    (havg : (U : E →L[𝕜] E) + (V : E →L[𝕜] E) = (2 : 𝕜) • D) :
    Commute (U : E →L[𝕜] E) D ∧ Commute (V : E →L[𝕜] E) D := by
  have hstar : star (U : E →L[𝕜] E) + star (V : E →L[𝕜] E) = (2 : 𝕜) • D := by
    simpa only [star_add, star_smul, star_ofNat, hD.isSelfAdjoint.star_eq] using
      congrArg star havg
  have h₁ : (U : E →L[𝕜] E) * D = D * star (V : E →L[𝕜] E) := by
    apply smul_right_injective _ (by norm_num : (2 : 𝕜) ≠ 0)
    change (2 : 𝕜) • ((U : E →L[𝕜] E) * D) =
      (2 : 𝕜) • (D * star (V : E →L[𝕜] E))
    calc
      _ = (U : E →L[𝕜] E) * ((2 : 𝕜) • D) := (mul_smul_comm _ _ _).symm
      _ = (U : E →L[𝕜] E) * (star (U : E →L[𝕜] E) + star (V : E →L[𝕜] E)) :=
        congrArg (fun T => (U : E →L[𝕜] E) * T) hstar.symm
      _ = ((U : E →L[𝕜] E) + (V : E →L[𝕜] E)) * star (V : E →L[𝕜] E) := by
        rw [mul_add, add_mul, Unitary.mul_star_self_of_mem U.property,
          Unitary.mul_star_self_of_mem V.property]
        abel
      _ = ((2 : 𝕜) • D) * star (V : E →L[𝕜] E) :=
        congrArg (fun T => T * star (V : E →L[𝕜] E)) havg
      _ = _ := smul_mul_assoc _ _ _
  have h₂ : star (V : E →L[𝕜] E) * D = D * (U : E →L[𝕜] E) := by
    apply smul_right_injective _ (by norm_num : (2 : 𝕜) ≠ 0)
    change (2 : 𝕜) • (star (V : E →L[𝕜] E) * D) =
      (2 : 𝕜) • (D * (U : E →L[𝕜] E))
    calc
      _ = star (V : E →L[𝕜] E) * ((2 : 𝕜) • D) := (mul_smul_comm _ _ _).symm
      _ = star (V : E →L[𝕜] E) * ((U : E →L[𝕜] E) + (V : E →L[𝕜] E)) :=
        congrArg (fun T => star (V : E →L[𝕜] E) * T) havg.symm
      _ = (star (U : E →L[𝕜] E) + star (V : E →L[𝕜] E)) * (U : E →L[𝕜] E) := by
        rw [mul_add, add_mul, Unitary.coe_star_mul_self, Unitary.coe_star_mul_self]
        abel
      _ = ((2 : 𝕜) • D) * (U : E →L[𝕜] E) :=
        congrArg (fun T => T * (U : E →L[𝕜] E)) hstar
      _ = _ := smul_mul_assoc _ _ _
  have hsq : Commute (U : E →L[𝕜] E) (D * D) := by
    change (U : E →L[𝕜] E) * (D * D) = (D * D) * (U : E →L[𝕜] E)
    calc
      _ = ((U : E →L[𝕜] E) * D) * D := (mul_assoc _ _ _).symm
      _ = (D * star (V : E →L[𝕜] E)) * D := by rw [h₁]
      _ = D * (star (V : E →L[𝕜] E) * D) := mul_assoc _ _ _
      _ = D * (D * (U : E →L[𝕜] E)) := by rw [h₂]
      _ = _ := (mul_assoc _ _ _).symm
  have hgram : Commute (U : E →L[𝕜] E) (D.adjoint ∘L D) := by
    simpa only [hD.isSelfAdjoint.adjoint_eq, ← ContinuousLinearMap.mul_def] using hsq
  have hU : Commute (U : E →L[𝕜] E) D := by
    simpa only [hD.modulus_eq] using commute_modulus_of_commute hgram
  refine ⟨hU, ?_⟩
  have hV : (V : E →L[𝕜] E) = (2 : 𝕜) • D - (U : E →L[𝕜] E) := by
    rw [← havg]
    abel
  change (V : E →L[𝕜] E) * D = D * (V : E →L[𝕜] E)
  rw [hV, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hU.eq]

/-- The two unitary summands are adjoints on the range of their positive
average, and are negatives on its kernel. -/
theorem unitary_sum_eq_two_smul_range_kernel
    (U V : unitary (E →L[𝕜] E)) (D : E →L[𝕜] E) (hD : D.IsPositive)
    (havg : (U : E →L[𝕜] E) + (V : E →L[𝕜] E) = (2 : 𝕜) • D) :
    (∀ x : E, (V : E →L[𝕜] E) (D x) = star (U : E →L[𝕜] E) (D x)) ∧
      (∀ x : E, D x = 0 → (V : E →L[𝕜] E) x = -(U : E →L[𝕜] E) x) := by
  obtain ⟨hU, hV⟩ := commute_of_unitary_sum_eq_two_smul U V D hD havg
  have hstar : star (U : E →L[𝕜] E) + star (V : E →L[𝕜] E) = (2 : 𝕜) • D := by
    simpa only [star_add, star_smul, star_ofNat, hD.isSelfAdjoint.star_eq] using
      congrArg star havg
  have hDU : D * (U : E →L[𝕜] E) = star (V : E →L[𝕜] E) * D := by
    apply smul_right_injective _ (by norm_num : (2 : 𝕜) ≠ 0)
    change (2 : 𝕜) • (D * (U : E →L[𝕜] E)) =
      (2 : 𝕜) • (star (V : E →L[𝕜] E) * D)
    calc
      _ = ((2 : 𝕜) • D) * (U : E →L[𝕜] E) := (smul_mul_assoc _ _ _).symm
      _ = (star (U : E →L[𝕜] E) + star (V : E →L[𝕜] E)) * (U : E →L[𝕜] E) :=
        congrArg (fun T => T * (U : E →L[𝕜] E)) hstar.symm
      _ = star (V : E →L[𝕜] E) * ((U : E →L[𝕜] E) + (V : E →L[𝕜] E)) := by
        rw [add_mul, mul_add, Unitary.coe_star_mul_self, Unitary.coe_star_mul_self]
        abel
      _ = star (V : E →L[𝕜] E) * ((2 : 𝕜) • D) :=
        congrArg (fun T => star (V : E →L[𝕜] E) * T) havg
      _ = _ := mul_smul_comm _ _ _
  have hDstar := congrArg star hDU
  simp only [star_mul, star_star, hD.isSelfAdjoint.star_eq] at hDstar
  constructor
  · intro x
    have h := hV.eq.trans hDstar.symm
    exact congrArg (fun T : E →L[𝕜] E => T x) h
  · intro x hx
    have h := congrArg (fun T : E →L[𝕜] E => T x) havg
    change (U : E →L[𝕜] E) x + (V : E →L[𝕜] E) x = (2 : 𝕜) • D x at h
    rw [hx, smul_zero] at h
    exact eq_neg_of_add_eq_zero_right h

/-- If the positive average is injective, its two unitary summands are
adjoints on the whole Hilbert space. Neither a bounded inverse nor a
closed-range assumption is needed. -/
theorem eq_star_of_unitary_sum_eq_two_smul_of_injective
    (U V : unitary (E →L[𝕜] E)) (D : E →L[𝕜] E) (hD : D.IsPositive)
    (havg : (U : E →L[𝕜] E) + (V : E →L[𝕜] E) = (2 : 𝕜) • D)
    (hinj : Function.Injective D) :
    (V : E →L[𝕜] E) = star (U : E →L[𝕜] E) := by
  obtain ⟨hU, hV⟩ := commute_of_unitary_sum_eq_two_smul U V D hD havg
  have hrange := (unitary_sum_eq_two_smul_range_kernel U V D hD havg).1
  have hstar : star (U : E →L[𝕜] E) * D = D * star (U : E →L[𝕜] E) := by
    simpa only [star_mul, hD.isSelfAdjoint.star_eq] using (congrArg star hU.eq).symm
  ext x
  apply hinj
  calc
    _ = (V : E →L[𝕜] E) (D x) :=
      (congrArg (fun T : E →L[𝕜] E => T x) hV.eq).symm
    _ = star (U : E →L[𝕜] E) (D x) := hrange x
    _ = _ := congrArg (fun T : E →L[𝕜] E => T x) hstar

/-- On every nonzero eigenspace of a positive twisted average, the
unitary has the prescribed real part and commutes with the self-adjoint
unitary grading. No finite-dimensional or closed-range assumption is used. -/
theorem rigidity_of_unitary_twisted_average_on_eigenvector
    (U S : unitary (E →L[𝕜] E)) (hS : IsSelfAdjoint (S : E →L[𝕜] E))
    (D : E →L[𝕜] E) (hD : D.IsPositive)
    (havg : (U : E →L[𝕜] E) + (S : E →L[𝕜] E) * star (U : E →L[𝕜] E) *
      (S : E →L[𝕜] E) = (2 : 𝕜) • D)
    (mu : 𝕜) (hmu : mu ≠ 0) (x : E) (hx : D x = mu • x) :
    (U : E →L[𝕜] E) x + star (U : E →L[𝕜] E) x = (2 * mu) • x ∧
      (U : E →L[𝕜] E) ((S : E →L[𝕜] E) x) =
        (S : E →L[𝕜] E) ((U : E →L[𝕜] E) x) := by
  let V := S * star U * S
  have havg' : (U : E →L[𝕜] E) + (V : E →L[𝕜] E) = (2 : 𝕜) • D := havg
  have hcomm := (commute_of_unitary_sum_eq_two_smul U V D hD havg').1
  have hrange := (unitary_sum_eq_two_smul_range_kernel U V D hD havg').1
  have hSS (y : E) : (S : E →L[𝕜] E) ((S : E →L[𝕜] E) y) = y := by
    have h := congrArg (fun T : E →L[𝕜] E => T y) (Unitary.star_mul_self_of_mem S.property)
    rwa [hS.star_eq] at h
  have hleft (y : E) : star (U : E →L[𝕜] E) ((U : E →L[𝕜] E) y) = y :=
    congrArg (fun T : E →L[𝕜] E => T y) (Unitary.star_mul_self_of_mem U.property)
  have hright (y : E) : (U : E →L[𝕜] E) (star (U : E →L[𝕜] E) y) = y :=
    congrArg (fun T : E →L[𝕜] E => T y) (Unitary.mul_star_self_of_mem U.property)
  have hadj (y : E) (hy : D y = mu • y) :
      (S : E →L[𝕜] E) (star (U : E →L[𝕜] E) ((S : E →L[𝕜] E) y)) =
        star (U : E →L[𝕜] E) y := by
    have h := hrange y
    rw [hy, map_smul, map_smul] at h
    exact smul_right_injective E hmu h
  have hstarcomm (y : E) (hy : D y = mu • y) :
      star (U : E →L[𝕜] E) ((S : E →L[𝕜] E) y) =
        (S : E →L[𝕜] E) (star (U : E →L[𝕜] E) y) := by
    apply (Unitary.linearIsometryEquiv S).injective
    change (S : E →L[𝕜] E) (star (U : E →L[𝕜] E) ((S : E →L[𝕜] E) y)) =
      (S : E →L[𝕜] E) ((S : E →L[𝕜] E) (star (U : E →L[𝕜] E) y))
    rw [hadj y hy, hSS]
  refine ⟨?_, ?_⟩
  · have h := congrArg (fun T : E →L[𝕜] E => T x) havg
    change (U : E →L[𝕜] E) x +
      (S : E →L[𝕜] E) (star (U : E →L[𝕜] E) ((S : E →L[𝕜] E) x)) =
        (2 : 𝕜) • D x at h
    simpa only [hadj x hx, hx, smul_smul] using h
  · have heig : D ((U : E →L[𝕜] E) x) = mu • (U : E →L[𝕜] E) x := by
      have h := congrArg (fun T : E →L[𝕜] E => T x) hcomm.eq
      change (U : E →L[𝕜] E) (D x) = D ((U : E →L[𝕜] E) x) at h
      rw [hx, map_smul] at h
      exact h.symm
    have h := congrArg (fun y => (U : E →L[𝕜] E) y)
      (hstarcomm ((U : E →L[𝕜] E) x) heig)
    rw [hleft, hright] at h
    exact h.symm

end ContinuousLinearMap
