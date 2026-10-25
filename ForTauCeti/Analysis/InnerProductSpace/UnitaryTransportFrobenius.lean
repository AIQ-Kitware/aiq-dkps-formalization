/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.NuclearTrace
public import ForTauCeti.Analysis.InnerProductSpace.SchattenFrobenius
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FixedRightCompression
import Mathlib.Tactic.NoncommRing

/-!
# Positive-compression certificates for unitary transport

A transporter with positive diagonal compression relative to its source
projection maximizes real trace over the entire transport fiber. It
therefore minimizes Frobenius displacement. If it is a reflection, the
bounded Schatten comparison makes it optimal for every `1 ≤ p ≤ 2`.
The certificate is the classical block Procrustes trace argument.
## Provenance

The trace argument is the classical block Procrustes certificate;
compare Bolotnikov, Li and Rodman, *Minimal distortion problems for
classes of unitary matrices* (2001), Theorems 3.4 and 4.2. The Lean
proof is independently written here using the accepted Schatten API
and the local nuclear trace-support theorem.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal InnerProductSpace
open UnitarilyInvariantSeminorm

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A unitary displacement's Frobenius square is twice its real trace
defect. Only finite dimension is needed; no ambient completeness is used. -/
theorem frobenius_displacement_sq_eq_trace (T : E ≃ₗᵢ[𝕜] E) :
    frobenius 𝕜 E E (LinearMap.id - T.toLinearMap) ^ 2 =
      2 * ((Module.finrank 𝕜 E : ℝ) - RCLike.re (LinearMap.trace 𝕜 E T.toLinearMap)) := by
  let e := stdOrthonormalBasis 𝕜 E
  have hdelta (i) : ‖((LinearMap.id : E →ₗ[𝕜] E) - T.toLinearMap) (e i)‖ ^ 2 =
      2 * (1 - RCLike.re ⟪e i, T (e i)⟫_𝕜) := by
    have h := norm_sub_sq (𝕜 := 𝕜) (e i) (T (e i))
    rw [e.norm_eq_one, T.norm_map, e.norm_eq_one] at h
    change ‖e i - T (e i)‖ ^ 2 = _
    linarith
  have htrace : RCLike.re (LinearMap.trace 𝕜 E T.toLinearMap) =
      ∑ i, RCLike.re ⟪e i, T (e i)⟫_𝕜 := by
    rw [LinearMap.trace_eq_sum_inner _ e, map_sum]
    rfl
  rw [sq_frobenius_apply e, htrace]
  simp only [hdelta, mul_sub, mul_one, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [← Finset.mul_sum]
  ring

omit [FiniteDimensional 𝕜 E] in
/-- Diagonal compression by an idempotent preserves trace. -/
theorem trace_diagonalCompression (P A : E →ₗ[𝕜] E) (hP : IsIdempotentElem P) :
    LinearMap.trace 𝕜 E (P * A * P + (1 - P) * A * (1 - P)) =
      LinearMap.trace 𝕜 E A := by
  have hPc : IsIdempotentElem (1 - P) := hP.one_sub
  rw [map_add, LinearMap.trace_mul_cycle 𝕜 P A P,
    LinearMap.trace_mul_cycle 𝕜 (1 - P) A (1 - P), hP.eq, hPc.eq]
  rw [← map_add]
  congr 1
  noncomm_ring

omit [FiniteDimensional 𝕜 E] in
/-- A source-commuting factor can be paired under the trace with just
the source-diagonal compression of an operator. -/
theorem trace_diagonalCompression_mul_of_commute (P A D : E →ₗ[𝕜] E)
    (hP : IsIdempotentElem P) (hD : Commute D P) :
    LinearMap.trace 𝕜 E ((P * A * P + (1 - P) * A * (1 - P)) * D) =
      LinearMap.trace 𝕜 E (A * D) := by
  have hDc : Commute D (1 - P) := (Commute.one_right D).sub_right hD
  have hprod : (P * A * P + (1 - P) * A * (1 - P)) * D =
      P * (A * D) * P + (1 - P) * (A * D) * (1 - P) := by
    simp only [add_mul, mul_assoc, hD.eq, hDc.eq]
  rw [hprod, trace_diagonalCompression P (A * D) hP]

variable [CompleteSpace E]

/-- A transporter with positive source-diagonal compression maximizes
real trace among all unitary transports with the same source and target. -/
theorem re_trace_transport_le_of_isPositive_diagonalCompression
    (P : E →L[𝕜] E) (hP : IsStarProjection P)
    (R W : E ≃ₗᵢ[𝕜] E)
    (hpos : (P * (R : E →L[𝕜] E) * P +
      (1 - P) * (R : E →L[𝕜] E) * (1 - P)).toLinearMap.IsPositive)
    (htrans : (W : E →L[𝕜] E) * P * star (W : E →L[𝕜] E) =
      (R : E →L[𝕜] E) * P * star (R : E →L[𝕜] E)) :
    RCLike.re (LinearMap.trace 𝕜 E W.toLinearMap) ≤
      RCLike.re (LinearMap.trace 𝕜 E R.toLinearMap) := by
  let D := W.trans R.symm
  let H := P * (R : E →L[𝕜] E) * P + (1 - P) * (R : E →L[𝕜] E) * (1 - P)
  have hDval : (D : E →L[𝕜] E) = star (R : E →L[𝕜] E) * (W : E →L[𝕜] E) := by
    rw [show star (R : E →L[𝕜] E) = (R.symm : E →L[𝕜] E) from R.adjoint_eq_symm]
    rfl
  have hDunit : (D : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) :=
    (Unitary.linearIsometryEquiv.symm D).property
  have hRunit : (R : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) :=
    (Unitary.linearIsometryEquiv.symm R).property
  have hDconj : (D : E →L[𝕜] E) * P * star (D : E →L[𝕜] E) = P := by
    rw [hDval, star_mul, star_star]
    calc
      _ = star (R : E →L[𝕜] E) *
          ((W : E →L[𝕜] E) * P * star (W : E →L[𝕜] E)) * (R : E →L[𝕜] E) := by
        simp only [mul_assoc]
      _ = _ := by
        rw [htrans]
        calc
          _ = (star (R : E →L[𝕜] E) * (R : E →L[𝕜] E)) * P *
              (star (R : E →L[𝕜] E) * (R : E →L[𝕜] E)) := by simp only [mul_assoc]
          _ = P := by rw [Unitary.star_mul_self_of_mem hRunit, one_mul, mul_one]
  have hDP : Commute (D : E →L[𝕜] E) P :=
    (commute_unitary_iff_star_right_conjugate hDunit).mpr hDconj
  have hDP' : Commute D.toLinearMap P.toLinearMap := by
    change D.toLinearMap * P.toLinearMap = P.toLinearMap * D.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap hDP.eq
  have hPlin : IsIdempotentElem P.toLinearMap := by
    change P.toLinearMap * P.toLinearMap = P.toLinearMap
    exact congrArg ContinuousLinearMap.toLinearMap hP.isIdempotentElem.eq
  have htrace := trace_diagonalCompression_mul_of_commute P.toLinearMap R.toLinearMap
    D.toLinearMap hPlin hDP'
  have hRD : R.toLinearMap * D.toLinearMap = W.toLinearMap := by
    ext x
    exact R.apply_symm_apply (W x)
  have hsupport := re_trace_isometry_comp_le_nuclear D H.toLinearMap
  have hHD : LinearMap.trace 𝕜 E (D.toLinearMap ∘ₗ H.toLinearMap) =
      LinearMap.trace 𝕜 E W.toLinearMap := by
    change LinearMap.trace 𝕜 E (D.toLinearMap * H.toLinearMap) = _
    rw [LinearMap.trace_mul_comm]
    exact htrace.trans (congrArg (LinearMap.trace 𝕜 E) hRD)
  rw [hHD, ← (re_trace_eq_nuclear_iff_isPositive H.toLinearMap).mpr hpos] at hsupport
  have htrH : LinearMap.trace 𝕜 E H.toLinearMap = LinearMap.trace 𝕜 E R.toLinearMap :=
    trace_diagonalCompression P.toLinearMap R.toLinearMap
      hPlin
  rwa [htrH] at hsupport

/-- A positive source-diagonal compression certifies global Frobenius
optimality over all unitary transporters of the same source projection. -/
theorem frobenius_transport_le_of_isPositive_diagonalCompression
    (P : E →L[𝕜] E) (hP : IsStarProjection P) (R W : E ≃ₗᵢ[𝕜] E)
    (hpos : (P * (R : E →L[𝕜] E) * P +
      (1 - P) * (R : E →L[𝕜] E) * (1 - P)).toLinearMap.IsPositive)
    (htrans : (W : E →L[𝕜] E) * P * star (W : E →L[𝕜] E) =
      (R : E →L[𝕜] E) * P * star (R : E →L[𝕜] E)) :
    frobenius 𝕜 E E (LinearMap.id - R.toLinearMap) ^ 2 ≤
      frobenius 𝕜 E E (LinearMap.id - W.toLinearMap) ^ 2 := by
  rw [frobenius_displacement_sq_eq_trace, frobenius_displacement_sq_eq_trace]
  have h := re_trace_transport_le_of_isPositive_diagonalCompression P hP R W hpos htrans
  linarith

/-- A positive source-diagonal compression of a reflection certifies
global Schatten optimality for every finite exponent between one and two. -/
theorem schatten_transport_le_of_reflection_isPositive_diagonalCompression
    (P : E →L[𝕜] E) (hP : IsStarProjection P) (R W : E ≃ₗᵢ[𝕜] E)
    (hR : IsSelfAdjoint (R : E →L[𝕜] E))
    (hpos : (P * (R : E →L[𝕜] E) * P +
      (1 - P) * (R : E →L[𝕜] E) * (1 - P)).toLinearMap.IsPositive)
    (htrans : (W : E →L[𝕜] E) * P * star (W : E →L[𝕜] E) =
      (R : E →L[𝕜] E) * P * star (R : E →L[𝕜] E))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp2 : p.toReal ≤ 2) :
    schatten 𝕜 E E p (LinearMap.id - R.toLinearMap) ^ p.toReal ≤
      schatten 𝕜 E E p (LinearMap.id - W.toLinearMap) ^ p.toReal := by
  have hRcost := schatten_displacement_rpow_eq_two_rpow_mul_frobenius_sq_of_isSelfAdjoint
    (Unitary.linearIsometryEquiv.symm R) hR p hp
  have hRlin : (Unitary.linearIsometryEquiv.symm R : E →L[𝕜] E).toLinearMap =
      R.toLinearMap := congrArg ContinuousLinearMap.toLinearMap
    (Unitary.coe_symm_linearIsometryEquiv_apply R)
  rw [hRlin] at hRcost
  rw [hRcost]
  calc
    _ ≤ (2 : ℝ) ^ (p.toReal - 2) * frobenius 𝕜 E E (LinearMap.id - W.toLinearMap) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (frobenius_transport_le_of_isPositive_diagonalCompression P hP R W hpos htrans)
        (Real.rpow_nonneg (by norm_num) _)
    _ ≤ _ := two_rpow_mul_frobenius_displacement_sq_le_schatten_rpow W p hp hp2

/-- A reflection with a spanning fixed/right block family is globally
Schatten optimal among all unitary transports of the same source, for
`1 ≤ p ≤ 2`. No angle list, block-preserving competitor or prescribed
orthogonality of the family is required. -/
theorem schatten_transport_le_of_fixed_or_exchange_blocks
    (P : E →L[𝕜] E) (hP : IsStarProjection P) (R W : E ≃ₗᵢ[𝕜] E)
    (hR : IsSelfAdjoint (R : E →L[𝕜] E))
    (F : Finset (Submodule 𝕜 E)) (hspan : F.sup id = ⊤)
    (hblocks : ∀ N ∈ F, (∀ x ∈ N, P x ∈ N) ∧ (∀ x ∈ N, R x ∈ N) ∧
      ((∀ x ∈ N, R x = x) ∨ (∀ x ∈ N, R (P (R x)) = x - P x)))
    (htrans : (W : E →L[𝕜] E) * P * star (W : E →L[𝕜] E) =
      (R : E →L[𝕜] E) * P * star (R : E →L[𝕜] E))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp2 : p.toReal ≤ 2) :
    schatten 𝕜 E E p (LinearMap.id - R.toLinearMap) ^ p.toReal ≤
      schatten 𝕜 E E p (LinearMap.id - W.toLinearMap) ^ p.toReal := by
  have hRR (x : E) : R (R x) = x := by
    have h := congrArg (fun A : E →L[𝕜] E => A x)
      (Unitary.star_mul_self_of_mem (Unitary.linearIsometryEquiv.symm R).property)
    change star (R : E →L[𝕜] E) (R x) = x at h
    rwa [hR.star_eq] at h
  have hproj := isStarProjection_diagonalCompression_of_fixed_or_exchange_blocks
    P (R : E →L[𝕜] E) hP hR hRR F hspan hblocks
  exact schatten_transport_le_of_reflection_isPositive_diagonalCompression P hP R W hR
    (ContinuousLinearMap.IsPositive.of_isStarProjection hproj).toLinearMap htrans p hp hp2

end TauCeti
