/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Complexification.FiniteDimensional
public import ForTauCeti.Analysis.InnerProductSpace.ScaledOrthonormalExtension
public import ForTauCeti.Analysis.InnerProductSpace.OrthonormalMatrix
public import ForTauCeti.Analysis.InnerProductSpace.NormalCharpolyCost

/-!
# Complexification preserves finite singular values and spectral costs

A real orthonormal basis extends, with the same indices, to a complex
orthonormal basis of the concrete Hilbert complexification. In these
bases complexification is entrywise scalar extension. The established
matrix scalar-extension theorem therefore preserves every singular
value, including zeros. This transports arbitrary spectral sums and
the accepted finite Schatten seminorm without a dimension-doubling factor.
These are classical scalar-extension facts.
-/

public section

noncomputable section

namespace TauCeti.RealComplexification

open scoped InnerProductSpace ENNReal

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A real orthonormal basis is a complex orthonormal basis of the
complexification after the actual real inclusion, with its original labels. -/
theorem exists_orthonormalBasis_ofReal [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    ∃ c : OrthonormalBasis ι ℂ (RealComplexification E), ∀ i, c i = ofReal (b i) := by
  classical
  have hdim : Module.finrank ℂ (RealComplexification E) = Fintype.card ι :=
    finrank_complex.trans (Module.finrank_eq_card_basis b.toBasis)
  have hGram (i j : ι) : ⟪ofReal (b i), ofReal (b j)⟫_ℂ =
      if i = j then (((1 : ℝ)^2 : ℝ) : ℂ) else 0 := by
    rw [inner_ofReal, b.inner_eq_ite]
    split_ifs <;> simp_all
  obtain ⟨c, hc⟩ := OrthonormalBasis.exists_smul_eq_of_inner_eq_ite
    hdim (fun i => ofReal (b i)) (fun _ => 1) hGram
  exact ⟨c, fun i => by simpa only [RCLike.ofReal_one, one_smul] using (hc i).symm⟩

/-- Complexification preserves the entire singular-value sequence of a
finite real endomorphism, including its zero padding. -/
theorem singularValues_complexify (T : E →L[ℝ] E) :
    (complexify T).toLinearMap.singularValues = T.toLinearMap.singularValues := by
  classical
  let b := stdOrthonormalBasis ℝ E
  obtain ⟨c, hc⟩ := exists_orthonormalBasis_ofReal b
  have hmatrix : LinearMap.toMatrixOrthonormal c (complexify T).toLinearMap =
      (LinearMap.toMatrixOrthonormal b T.toLinearMap).map Complex.ofRealHom := by
    ext i j
    simp only [LinearMap.toMatrixOrthonormal_apply_apply, Matrix.map_apply]
    change ⟪c i, complexify T (c j)⟫_ℂ = (⟪b i, T (b j)⟫_ℝ : ℂ)
    rw [hc, hc, complexify_ofReal, inner_ofReal]
  calc
    _ = (LinearMap.toMatrixOrthonormal c
        (complexify T).toLinearMap).toEuclideanLin.singularValues :=
      (c.singularValues_toMatrixOrthonormal _).symm
    _ = (LinearMap.toMatrixOrthonormal b T.toLinearMap).toEuclideanLin.singularValues := by
      rw [hmatrix, ← Matrix.singularValues_toEuclideanLin_map_ofReal]
    _ = _ := b.singularValues_toMatrixOrthonormal _

/-- Any spectral sum is unchanged by complexification. In particular fixed
directions contribute exactly the same zero values over either field. -/
theorem sum_singularValues_complexify (T : E →L[ℝ] E) (rho : ℝ → ℝ) :
    (∑ i : Fin (Module.finrank ℂ (RealComplexification E)),
      rho ((complexify T).toLinearMap.singularValues i)) =
        ∑ i : Fin (Module.finrank ℝ E), rho (T.toLinearMap.singularValues i) := by
  rw [singularValues_complexify, finrank_complex]

/-- The accepted finite Schatten seminorm has no field-extension factor. -/
theorem schatten_complexify (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : E →L[ℝ] E) :
    UnitarilyInvariantSeminorm.schatten ℂ (RealComplexification E) (RealComplexification E) p
      (complexify T).toLinearMap =
        UnitarilyInvariantSeminorm.schatten ℝ E E p T.toLinearMap := by
  rw [UnitarilyInvariantSeminorm.schatten_apply_of_ne_top p hp,
    UnitarilyInvariantSeminorm.schatten_apply_of_ne_top p hp,
    singularValues_complexify]

end TauCeti.RealComplexification
