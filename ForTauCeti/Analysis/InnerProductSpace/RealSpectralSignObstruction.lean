/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.OrthogonalComplexStructure
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Real spectral sign obstructions

A commuting sign projection in a nondegenerate real complex-structure
block has even rank. If an involution exchanges it with its complement,
the entire block dimension is divisible by four. These finite spectral
block results apply inside infinite-rank compact operators.
-/

public section

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- An invariant subspace of a real operator whose square is a negative
nonzero scalar has even real dimension. Orthogonality is unnecessary. -/
theorem even_finrank_invariant_of_square_neg_real
    (G : E →L[ℝ] E) (c : ℝ) (hc : c ≠ 0)
    (hG : G * G = -(c * c) • 1)
    (M : Submodule ℝ E) (hM : ∀ x ∈ M, G x ∈ M) :
    Even (Module.finrank ℝ M) := by
  let H : M →ₗ[ℝ] M := (c⁻¹ : ℝ) • (G.toLinearMap.restrict hM)
  have hsquare : H.comp H = -LinearMap.id := by
    ext x
    have hx := congrArg (fun A : E →L[ℝ] E => A (x : E)) hG
    change G (G x) = -(c * c) • (x : E) at hx
    change c⁻¹ • G (c⁻¹ • G x) = -(x : E)
    rw [map_smul, smul_smul, hx, smul_smul]
    have hcoeff : c⁻¹ * c⁻¹ * -(c * c) = -1 := by field_simp
    rw [hcoeff, neg_one_smul]
  exact (show AlmostComplexStructure M from ⟨H, hsquare⟩).even_finrank_real

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A commuting projection in a negative-square real block has even
rank. This is the real obstruction hidden by complex phase choices. -/
theorem even_finrank_range_of_commuting_projection_square_neg_real
    (G P : E →L[ℝ] E) (c : ℝ) (hc : c ≠ 0)
    (hG : G * G = -(c * c) • 1) (hPG : Commute P G) :
    Even (Module.finrank ℝ P.range) := by
  apply even_finrank_invariant_of_square_neg_real G c hc hG P.range
  rintro x ⟨y, rfl⟩
  refine ⟨G y, ?_⟩
  exact congrArg (fun A : E →L[ℝ] E => A y) hPG.eq

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- An involution exchanging a projection with its complement gives
equal dimensions of its range and kernel. No isometry is needed. -/
theorem finrank_range_eq_ker_of_projection_exchange_real
    (P J : E →L[ℝ] E) (hP : IsIdempotentElem P) (hJ : J * J = 1)
    (hexchange : P * J + J * P = J) :
    Module.finrank ℝ P.range = Module.finrank ℝ P.ker := by
  have hJx (x : E) : J (J x) = x := congrArg (fun A : E →L[ℝ] E => A x) hJ
  have hPx (x : P.range) : P (x : E) = x := by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy]
    exact congrArg (fun A : E →L[ℝ] E => A y) hP.eq
  have hto (x : P.range) : J x ∈ P.ker := by
    have h := congrArg (fun A : E →L[ℝ] E => A (x : E)) hexchange
    change P (J x) + J (P x) = J x at h
    rw [hPx] at h
    exact add_right_cancel (h.trans (zero_add (J (x : E))).symm)
  have hfrom (y : P.ker) : J y ∈ P.range := by
    have h := congrArg (fun A : E →L[ℝ] E => A (y : E)) hexchange
    have hy : P (y : E) = 0 := y.property
    change P (J y) + J (P y) = J y at h
    rw [hy, map_zero, add_zero] at h
    exact ⟨J y, h⟩
  let e : P.range ≃ₗ[ℝ] P.ker :=
    { toFun := fun x => ⟨J x, hto x⟩
      invFun := fun y => ⟨J y, hfrom y⟩
      left_inv := fun x => Subtype.ext (hJx x)
      right_inv := fun y => Subtype.ext (hJx y)
      map_add' := fun x y => Subtype.ext (J.map_add x y)
      map_smul' := fun r x => Subtype.ext (J.map_smul r x) }
  exact e.finrank_eq

/-- **Fourfold real spectral obstruction.** In a nonzero negative-square
block, an orthogonal projection commuting with the complex structure and
exchanged with its complement by an involution can exist only in real
dimension divisible by four. Zero-square blocks are explicitly excluded. -/
theorem four_dvd_finrank_of_spectral_sign_projection_real
    (G J P : E →L[ℝ] E) (c : ℝ) (hc : c ≠ 0)
    (hG : G * G = -(c * c) • 1) (hJ : J * J = 1)
    (hP : IsStarProjection P) (hPG : Commute P G)
    (hexchange : P * J + J * P = J) :
    4 ∣ Module.finrank ℝ E := by
  obtain ⟨m, hm⟩ :=
    even_finrank_range_of_commuting_projection_square_neg_real G P c hc hG hPG
  have hdim := LinearMap.finrank_range_add_finrank_ker P.toLinearMap
  have heq := finrank_range_eq_ker_of_projection_exchange_real P J hP.isIdempotentElem hJ hexchange
  exact ⟨m, by omega⟩

end TauCeti
