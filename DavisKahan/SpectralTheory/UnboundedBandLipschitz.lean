/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.SpectralTheory.UnboundedCentralBand
import DavisKahan.Sources.DavisKahan1970.Section8.Theorem82UnboundedBranchBound

/-!
# The moving band is Lipschitz in the perturbation, with no Riesz projector

Step (c) of the unbounded Theorem 8.2 path.  Two self-adjoint partial maps
differing by a bounded `K`, each with real spectrum in `[l, r] ∪ exterior`, have
band subspaces at projection distance at most `‖K‖ / d`.

The estimate is the unbounded `sin Θ` theorem read at the operator norm
(`directedGap_le_of_reducingGap_unbounded_complex`), applied once in each
orientation and combined by `projectionGap_eq_max_directedProjectionGap`.  The
separation it consumes is `formBoundedSylvesterGap_band_exterior`.

This is what replaces the bounded proof's Riesz-projection continuity: no
contour, no continuation API, and the constant depends only on the gap.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan

open DavisKahan.Sylvester

noncomputable section

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The band subspace of a self-adjoint partial map: the spectral range of the
closed interval `[l, r]`. -/
def bandSubspace {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (l r : ℝ) :
    Submodule ℂ H :=
  TauCeti.LinearPMap.specRange hA (Set.Icc l r) measurableSet_Icc

instance bandSubspace_hasOrthogonalProjection {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (l r : ℝ) : (bandSubspace hA l r).HasOrthogonalProjection :=
  TauCeti.LinearPMap.instHasOrthogonalProjection_specRange hA _ _

theorem reducesSubspace_bandSubspace {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (l r : ℝ) :
    TauCeti.LinearPMap.ReducesSubspace A (bandSubspace hA l r) :=
  TauCeti.LinearPMap.reducesSubspace_specRange hA _ _

/-- **The directed half of the Lipschitz estimate.**

`d · directedGap (band of A) (band of A + K) ≤ ‖K‖`, from the unbounded `sin Θ`
theorem at the operator norm. -/
theorem directedGap_bandSubspace_le
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (K : H →L[ℂ] H) (hK : DavisKahan.IsSelfAdjointOperator K)
    (hAB : B = TauCeti.LinearPMap.addBounded A K)
    {l r d : ℝ} (hlr : l ≤ r) (hd : 0 < d)
    (hAspec : TauCeti.LinearPMap.realSpectrum A ⊆
      Set.Icc l r ∪ bandExterior l r d)
    (hBspec : TauCeti.LinearPMap.realSpectrum B ⊆
      Set.Icc l r ∪ bandExterior l r d) :
    d * DavisKahan.directedGap (bandSubspace hA l r) (bandSubspace hB l r) ≤ ‖K‖ := by
  subst hAB
  have hQred : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A K)
      (bandSubspace hB l r) := reducesSubspace_bandSubspace hB l r
  have hperp : (bandSubspace hB l r)ᗮ =
      TauCeti.LinearPMap.specRange hB (bandExterior l r d)
        (measurableSet_bandExterior l r d) :=
    (specRange_bandExterior_eq_orthogonal hB hlr hd hBspec).symm
  have hgap := formBoundedSylvesterGap_band_exterior (A := A)
    (B := TauCeti.LinearPMap.addBounded A K) hA hB hlr
    (W := bandSubspace hA l r) (W' := (bandSubspace hB l r)ᗮ)
    rfl hperp (reducesSubspace_bandSubspace hA l r) hQred.orthogonal
  exact TauCeti.DavisKahan1970.Section8.directedGap_le_of_reducingGap_unbounded_complex
    hA K hK (reducesSubspace_bandSubspace hA l r) hQred hd hgap

/-- **The moving band is Lipschitz in the perturbation.**

`d · ‖P_{band A} − P_{band B}‖ ≤ ‖K‖` when `B = A + K`.  The two directed
estimates come from the unbounded `sin Θ` theorem in each orientation; the
reverse one is the same theorem applied to `A = B + (−K)`. -/
theorem subspaceGap_bandSubspace_le
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (K : H →L[ℂ] H) (hK : DavisKahan.IsSelfAdjointOperator K)
    (hAB : B = TauCeti.LinearPMap.addBounded A K)
    {l r d : ℝ} (hlr : l ≤ r) (hd : 0 < d)
    (hAspec : TauCeti.LinearPMap.realSpectrum A ⊆
      Set.Icc l r ∪ bandExterior l r d)
    (hBspec : TauCeti.LinearPMap.realSpectrum B ⊆
      Set.Icc l r ∪ bandExterior l r d) :
    d * DavisKahan.subspaceGap (bandSubspace hA l r) (bandSubspace hB l r) ≤ ‖K‖ := by
  have hnegK : DavisKahan.IsSelfAdjointOperator (-K) := by
    intro x y
    have h : ⟪K x, y⟫_ℂ = ⟪x, K y⟫_ℂ := hK x y
    show ⟪-(K x), y⟫_ℂ = ⟪x, -(K y)⟫_ℂ
    rw [inner_neg_left, inner_neg_right, h]
  have hBA : A = TauCeti.LinearPMap.addBounded B (-K) := by
    rw [hAB]
    exact (TauCeti.LinearPMap.addBounded_neg_cancel A K).symm
  have h1 := directedGap_bandSubspace_le hA hB K hK hAB hlr hd hAspec hBspec
  have h2 := directedGap_bandSubspace_le hB hA (-K) hnegK hBA hlr hd hBspec hAspec
  rw [norm_neg] at h2
  have hmax := Submodule.projectionGap_eq_max_directedProjectionGap
    (bandSubspace hA l r) (bandSubspace hB l r)
  show d * (bandSubspace hA l r).projectionGap (bandSubspace hB l r) ≤ ‖K‖
  rw [hmax]
  rcases max_cases ((bandSubspace hA l r).directedProjectionGap (bandSubspace hB l r))
    ((bandSubspace hB l r).directedProjectionGap (bandSubspace hA l r)) with ⟨he, -⟩ | ⟨he, -⟩
  · rw [he]; exact h1
  · rw [he]; exact h2

end

end DavisKahan
end TauCeti
