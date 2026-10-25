/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Singular values determined by a Gram characteristic polynomial

The accepted symmetric spectral theorem identifies the sorted eigenvalues
from a characteristic polynomial. Applying it to the source Gram maps
identifies all singular values, including their zero padding. This avoids
constructing eigenvectors when explicit small matrices have repeated or
vanishing singular values.
-/

public section

noncomputable section

namespace LinearMap

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]

/-- Equal source dimensions and equal source-Gram characteristic polynomials
give equal singular-value sequences. The target dimensions may differ.
The proof compares the accepted sorted Gram eigenvalues and then uses
nonnegativity to take square roots; indices outside the source dimension
vanish on both sides. -/
theorem singularValues_eq_of_gram_charpoly_eq
    (A : E →ₗ[𝕜] F) (B : G →ₗ[𝕜] H)
    (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 G)
    (hchar : (A.adjoint ∘ₗ A).charpoly = (B.adjoint ∘ₗ B).charpoly) :
    A.singularValues = B.singularValues := by
  have heig := (A.isSymmetric_adjoint_comp_self.eigenvalues_eq_eigenvalues_iff
    rfl B.isSymmetric_adjoint_comp_self hdim.symm).mpr hchar
  ext i
  by_cases hi : i < Module.finrank 𝕜 E
  · have hsq : A.singularValues i ^ 2 = B.singularValues i ^ 2 := by
      rw [A.sq_singularValues_of_lt rfl hi,
        B.sq_singularValues_of_lt hdim.symm hi, heig]
    nlinarith [A.singularValues_nonneg i, B.singularValues_nonneg i]
  · rw [A.singularValues_of_finrank_le (Nat.le_of_not_gt hi),
      B.singularValues_of_finrank_le (hdim ▸ Nat.le_of_not_gt hi)]

/-- A real map and a complex map have the same singular values when their
source Gram characteristic polynomials agree after scalar extension.
The proof maps the full real Gram root multiset into `ℂ` and sorts its real
parts. This includes all zero singular values and empty source spaces. -/
theorem singularValues_eq_complex_of_gram_charpoly_map_eq
    {E₁ F₁ E₂ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [FiniteDimensional ℂ F₂]
    (A : E₁ →ₗ[ℝ] F₁) (B : E₂ →ₗ[ℂ] F₂)
    (hdim : Module.finrank ℝ E₁ = Module.finrank ℂ E₂)
    (hchar : (B.adjoint ∘ₗ B).charpoly =
      (A.adjoint ∘ₗ A).charpoly.map Complex.ofRealHom) :
    A.singularValues = B.singularValues := by
  have hroots := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (f := Complex.ofRealHom) Complex.ofReal_injective
    (Polynomial.splits_iff_card_roots.mp A.isSymmetric_adjoint_comp_self.splits_charpoly)
  have heig : A.isSymmetric_adjoint_comp_self.eigenvalues rfl =
      B.isSymmetric_adjoint_comp_self.eigenvalues hdim.symm := by
    apply List.ofFn_inj.mp
    rw [← A.isSymmetric_adjoint_comp_self.sort_roots_charpoly_eq_eigenvalues rfl,
      ← B.isSymmetric_adjoint_comp_self.sort_roots_charpoly_eq_eigenvalues hdim.symm,
      hchar, ← hroots]
    simp only [Multiset.map_map, Function.comp_def]
    change ((A.adjoint ∘ₗ A).charpoly.roots.map (fun x : ℝ => x)).sort (· ≥ ·) =
      ((A.adjoint ∘ₗ A).charpoly.roots.map (fun x : ℝ => (x : ℂ).re)).sort (· ≥ ·)
    simp only [Complex.ofReal_re]
  ext i
  by_cases hi : i < Module.finrank ℝ E₁
  · have hsq : A.singularValues i ^ 2 = B.singularValues i ^ 2 := by
      rw [A.sq_singularValues_of_lt rfl hi,
        B.sq_singularValues_of_lt hdim.symm hi, heig]
    nlinarith [A.singularValues_nonneg i, B.singularValues_nonneg i]
  · rw [A.singularValues_of_finrank_le (Nat.le_of_not_gt hi),
      B.singularValues_of_finrank_le (hdim ▸ Nat.le_of_not_gt hi)]

end LinearMap
