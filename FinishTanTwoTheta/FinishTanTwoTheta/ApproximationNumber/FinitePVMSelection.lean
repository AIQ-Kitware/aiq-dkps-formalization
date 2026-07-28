/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.ApproximationNumber.GramSpectralRank
import DavisKahan.Interop.Spectra.PVMSubspace
import Spectra.SpectralTheory.Essential.Discrete

/-!
# Finite selection from spectral projection ranges

The Spectra library supplies projection algebra and spectral localization, but
not the finite-dimensional selection wrapper needed by the approximation-number
argument.  This file supplies that missing wrapper without tactic search.
-/

namespace TauCeti
namespace FinishTanTwoTheta

open scoped InnerProductSpace
open Set
open TauCeti.DavisKahan.Experimental.SpectraBridge

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A natural-number rank lower bound on a PVM projection yields an orthonormal
family of that length inside its range. -/
theorem exists_orthonormal_mem_pvmRange_of_natCast_le_rank
    (P : Spectra.ProjValMeasure H) (B : Set ℝ) (hB : MeasurableSet B)
    (m : ℕ) (hm : (m : Cardinal) ≤ (P.proj B hB).rank) :
    ∃ v : Fin m → H, Orthonormal ℂ v ∧
      ∀ i, v i ∈ pvmRangeSubspace P B hB := by
  classical
  let W : Submodule ℂ H := pvmRangeSubspace P B hB
  have hmW : (m : Cardinal) ≤ Module.rank ℂ W := by
    change (m : Cardinal) ≤ (P.proj B hB).rank
    exact hm
  obtain ⟨g, hg⟩ := (Module.le_rank_iff).1 hmW
  let V : Submodule ℂ W := Submodule.span ℂ (Set.range g)
  let b : Module.Basis (Fin m) ℂ V := Module.Basis.span hg
  letI : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  have hfinrank : finrank ℂ V = m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  let bV := stdOrthonormalBasis ℂ V
  let v : Fin m → H := fun i =>
    ((((bV (Fin.cast hfinrank.symm i) : V) : W) : H))
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    change
      ⟪bV (Fin.cast hfinrank.symm i), bV (Fin.cast hfinrank.symm j)⟫_ℂ =
        if i = j then 1 else 0
    rw [orthonormal_iff_ite.mp bV.orthonormal]
    simp only [Fin.cast_inj]
  refine ⟨v, hv, ?_⟩
  intro i
  change (((bV (Fin.cast hfinrank.symm i) : V) : W) : H) ∈ W
  exact (((bV (Fin.cast hfinrank.symm i) : V) : W)).property

/-- Vectors selected from disjoint PVM ranges are orthogonal. -/
theorem inner_eq_zero_of_mem_disjoint_pvmRanges
    (P : Spectra.ProjValMeasure H)
    {B₁ B₂ : Set ℝ} (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂)
    (hdisj : Disjoint B₁ B₂) {x y : H}
    (hx : x ∈ pvmRangeSubspace P B₁ hB₁)
    (hy : y ∈ pvmRangeSubspace P B₂ hB₂) :
    ⟪x, y⟫_ℂ = 0 := by
  rcases hx with ⟨x₀, rfl⟩
  rcases hy with ⟨y₀, rfl⟩
  exact P.inner_proj_eq_zero_of_disjoint hB₁ hB₂ hdisj x₀ y₀

end

end FinishTanTwoTheta
end TauCeti
