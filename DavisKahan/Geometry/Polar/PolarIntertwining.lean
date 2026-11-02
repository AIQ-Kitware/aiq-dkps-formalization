/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

module

public import ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry
public import DavisKahan.Geometry.Polar.DirectRotation
public import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Polar factors and reducing projections

This file isolates the functional-analytic facts used by the nonacute
Davis--Kahan direct rotation.  The key principle is that an intertwining
relation `T P = Q T`, together with the adjoint relation, passes from `T` to
its polar partial isometry.  The proof is carried out first on `range |T|`,
then on its closure, and finally on the orthogonal complement, where the polar
factor vanishes.
-/

public section

open scoped InnerProductSpace InnerProduct

namespace TauCeti
namespace DavisKahan

open DavisKahan.Foundation

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]


/-- A self-adjoint projection commuting with `|T|` preserves the initial polar
space. -/
theorem polarInitial_invariant_of_commute_modulus
    (T P : H →L[𝕜] H)
    (hcomm : T.modulus ∘L P = P ∘L T.modulus)
    {x : H} (hx : x ∈ (T.ker)ᗮ) : P x ∈ (T.ker)ᗮ := by
  let M : Submodule 𝕜 H := Submodule.comap (P : H →ₗ[𝕜] H) ((T.ker)ᗮ)
  have hMclosed : IsClosed (M : Set H) := by
    have hcl : IsClosed (((T.ker)ᗮ : Set H)) := by
      rw [← T.topologicalClosure_range_modulus]
      exact Submodule.isClosed_topologicalClosure _
    exact hcl.preimage P.continuous
  have hrange : LinearMap.range (T.modulus).toLinearMap ≤ M := by
    rintro y ⟨z, rfl⟩
    change P (T.modulus z) ∈ (T.ker)ᗮ
    have hpoint := DFunLike.congr_fun hcomm z
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hpoint
    rw [← hpoint]
    rw [← T.topologicalClosure_range_modulus]
    exact (T.modulus.range).le_topologicalClosure ⟨P z, rfl⟩
  have hclosure : (T.ker)ᗮ ≤ M := by
    rw [← T.topologicalClosure_range_modulus]
    exact Submodule.topologicalClosure_minimal _ hrange hMclosed
  exact hclosure hx

/-- If a self-adjoint projection preserves the initial polar space, it also
preserves its orthogonal complement. -/
theorem polarInitial_orthogonal_invariant_of_selfAdjoint
    (T P : H →L[𝕜] H) (hP : IsSelfAdjoint P)
    (hpres : ∀ x ∈ (T.ker)ᗮ, P x ∈ (T.ker)ᗮ)
    {x : H} (hx : x ∈ ((T.ker)ᗮ)ᗮ) : P x ∈ ((T.ker)ᗮ)ᗮ := by
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (ContinuousLinearMap.star_eq_adjoint P).symm.trans hP.star_eq
  rw [hPadj]
  exact hx (P y) (hpres y hy)

/-- The absolute value commutes with the initial projection whenever `T`
intertwines two orthogonal projections. -/
theorem modulus_commutes_of_projection_intertwining
    (T P Q : H →L[𝕜] H)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hTP : T ∘L P = Q ∘L T) :
    T.modulus ∘L P = P ∘L T.modulus := by
  have hPsa : IsSelfAdjoint P := LinearMap.IsSymmetric.isSelfAdjoint hP.2
  have hQsa : IsSelfAdjoint Q := LinearMap.IsSymmetric.isSelfAdjoint hQ.2
  have hPadj : ContinuousLinearMap.adjoint P = P :=
    (ContinuousLinearMap.star_eq_adjoint P).symm.trans hPsa.star_eq
  have hQadj : ContinuousLinearMap.adjoint Q = Q :=
    (ContinuousLinearMap.star_eq_adjoint Q).symm.trans hQsa.star_eq
  have hstar : P ∘L T† = T† ∘L Q := by
    have h := congrArg ContinuousLinearMap.adjoint hTP
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      hPadj, hQadj] at h
    exact h
  have hgram : (T† ∘L T) ∘L P = P ∘L (T† ∘L T) := by
    calc
      (T† ∘L T) ∘L P = T† ∘L (T ∘L P) := by
        ext x
        rfl
      _ = T† ∘L (Q ∘L T) := by rw [hTP]
      _ = (T† ∘L Q) ∘L T := by
        ext x
        rfl
      _ = (P ∘L T†) ∘L T := by rw [← hstar]
      _ = P ∘L (T† ∘L T) := by
        ext x
        rfl
  have hcomm : Commute (star T * T) P := by
    have hmul : (star T * T) * P = P * (star T * T) := by
      simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]
      exact hgram
    exact hmul
  simpa [ContinuousLinearMap.mul_def] using
    ((ContinuousLinearMap.commute_modulus_of_commute hcomm.symm).symm).eq

/-- The polar partial isometry intertwines the same two projections as the
original operator. -/
theorem polarPartial_intertwines_of_projection_intertwining
    (T P Q : H →L[𝕜] H)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hTP : T ∘L P = Q ∘L T) :
    T.polarFactor ∘L P = Q ∘L T.polarFactor := by
  have habs : T.modulus ∘L P = P ∘L T.modulus :=
    modulus_commutes_of_projection_intertwining T P Q hP hQ hTP
  let V := T.polarFactor ∘L P - Q ∘L T.polarFactor
  have hcomp : V ∘L T.modulus = 0 := by
    calc
      V ∘L T.modulus = T.polarFactor ∘L (P ∘L T.modulus) -
          Q ∘L (T.polarFactor ∘L T.modulus) := by
        simp only [V, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]
      _ = T.polarFactor ∘L (T.modulus ∘L P) - Q ∘L T := by
        rw [habs, T.polarFactor_comp_modulus]
      _ = T ∘L P - Q ∘L T := by
        rw [← ContinuousLinearMap.comp_assoc, T.polarFactor_comp_modulus]
      _ = 0 := sub_eq_zero.mpr hTP
  have hker : ∀ y ∈ T.modulus.rangeᗮ, V y = 0 := by
    intro y hy
    rw [T.orthogonal_range_modulus] at hy
    have hPy : P y ∈ T.ker := by
      change T (P y) = 0
      have h := congrArg (fun S : H →L[𝕜] H => S y) hTP
      change T (P y) = Q (T y) at h
      rw [show T y = 0 from hy, map_zero] at h
      exact h
    simp only [V, _root_.sub_apply, ContinuousLinearMap.comp_apply,
      T.polarFactor_apply_of_mem_ker hy, T.polarFactor_apply_of_mem_ker hPy,
      map_zero, sub_self]
  have hV := ContinuousLinearMap.eq_factorThru
    (T := (0 : H →L[𝕜] H)) (A := T.modulus) hcomp hker
  have hzero := ContinuousLinearMap.eq_factorThru
    (T := (0 : H →L[𝕜] H)) (A := T.modulus) (V := 0) (by simp) (by simp)
  exact sub_eq_zero.mp (hV.trans hzero.symm)

/-- The polar factor of the canonical two-projection intertwiner intertwines
both projections without an acuteness assumption. -/
theorem canonicalPolarFactor_intertwines_from_polar
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    spectraCanonicalPolarFactor U V ∘L U.starProjection =
      V.starProjection ∘L spectraCanonicalPolarFactor U V := by
  rw [spectraCanonicalPolarFactor]
  apply polarPartial_intertwines_of_projection_intertwining
  · exact ⟨U.isIdempotentElem_starProjection,
      (isSelfAdjoint_starProjection U).isSymmetric⟩
  · exact ⟨V.isIdempotentElem_starProjection,
      (isSelfAdjoint_starProjection V).isSymmetric⟩
  · simpa [ContinuousLinearMap.mul_def] using
      spectraCanonicalIntertwiner_mul_projection U V

/-- Taking adjoints exchanges the ordered pair of subspaces in the canonical
polar factor. -/
theorem canonicalPolarFactor_adjoint_swap_from_polar
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    star (spectraCanonicalPolarFactor U V) =
      spectraCanonicalPolarFactor V U := by
  rw [spectraCanonicalPolarFactor, spectraCanonicalPolarFactor,
    ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.polarFactor_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint, star_spectraCanonicalIntertwiner]

end

end DavisKahan
end TauCeti
