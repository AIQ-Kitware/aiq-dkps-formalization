/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.MathAhead.HiddenFoundations.PolarIsometryFinal
import DavisKahan.Interop.Spectra.DirectRotation

/-!
# Polar factors and reducing projections

This file isolates the functional-analytic facts used by the nonacute
Davis--Kahan direct rotation.  The key principle is that an intertwining
relation `T P = Q T`, together with the adjoint relation, passes from `T` to
its polar partial isometry.  The proof is carried out first on `range |T|`,
then on its closure, and finally on the orthogonal complement, where the polar
factor vanishes.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open SpectraBridge
open Spectra.QuantumMechanics.Channels

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A self-adjoint projection commuting with `|T|` preserves the initial polar
space. -/
theorem polarRange_invariant_of_commute_abs
    (T P : H →L[ℂ] H)
    (hcomm : absOp T ∘L P = P ∘L absOp T)
    {x : H} (hx : x ∈ polarRange T) : P x ∈ polarRange T := by
  let M : Submodule ℂ H := {x | P x ∈ polarRange T}
  have hMclosed : IsClosed (M : Set H) := by
    exact (polarRange T).isClosed.preimage P.continuous
  have hrange : LinearMap.range (absOp T).toLinearMap ≤ M := by
    rintro y ⟨z, rfl⟩
    change P (absOp T z) ∈ polarRange T
    have hpoint := DFunLike.congr_fun hcomm z
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hpoint
    rw [← hpoint]
    exact absOp_mem_polarRange T (P z)
  have hclosure : polarRange T ≤ M := by
    rw [polarRange]
    exact Submodule.topologicalClosure_minimal hrange hMclosed
  exact hclosure hx

/-- If a self-adjoint projection preserves the initial polar space, it also
preserves its orthogonal complement. -/
theorem polarRange_orthogonal_invariant_of_selfAdjoint
    (T P : H →L[ℂ] H) (hP : IsSelfAdjoint P)
    (hpres : ∀ x ∈ polarRange T, P x ∈ polarRange T)
    {x : H} (hx : x ∈ (polarRange T)ᗮ) : P x ∈ (polarRange T)ᗮ := by
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [hP.star_eq]
  exact hx (P y) (hpres y hy)

/-- The absolute value commutes with the initial projection whenever `T`
intertwines two orthogonal projections. -/
theorem absOp_commutes_of_projection_intertwining
    (T P Q : H →L[ℂ] H)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hTP : T ∘L P = Q ∘L T) :
    absOp T ∘L P = P ∘L absOp T := by
  have hstar : P ∘L T† = T† ∘L Q := by
    have h := congrArg star hTP
    simpa [star_mul, hP.2.star_eq, hQ.2.star_eq,
      ContinuousLinearMap.mul_def] using h
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
  exact absOp_commutes_of_gram_commutes T P hgram

/-- The polar partial isometry intertwines the same two projections as the
original operator. -/
theorem polarIsometry_intertwines_of_projection_intertwining
    (T P Q : H →L[ℂ] H)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (hTP : T ∘L P = Q ∘L T) :
    polarIsometry T ∘L P = Q ∘L polarIsometry T := by
  have habs : absOp T ∘L P = P ∘L absOp T :=
    absOp_commutes_of_projection_intertwining T P Q hP hQ hTP
  have hpres : ∀ x ∈ polarRange T, P x ∈ polarRange T :=
    fun x hx => polarRange_invariant_of_commute_abs T P habs hx
  have hpresOrth : ∀ x ∈ (polarRange T)ᗮ, P x ∈ (polarRange T)ᗮ :=
    fun x hx => polarRange_orthogonal_invariant_of_selfAdjoint T P hP.2 hpres hx
  refine ContinuousLinearMap.ext fun x => ?_
  obtain ⟨m, hm, k, hk, rfl⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal
      (K := polarRange T) x
  have hUk : polarIsometry T k = 0 := by
    rw [polarIsometry_apply_eq]
    rw [Submodule.orthogonalProjection_eq_zero_iff.mpr hk]
    simp
  have hUPk : polarIsometry T (P k) = 0 := by
    rw [polarIsometry_apply_eq]
    rw [Submodule.orthogonalProjection_eq_zero_iff.mpr (hpresOrth k hk)]
    simp
  rw [map_add, map_add, hUk, hUPk, add_zero, add_zero,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have heqOnDense :
      polarPartial T ((polarRange T).orthogonalProjection (P m)) =
        Q (polarPartial T ((polarRange T).orthogonalProjection m)) := by
    let f : polarRange T →L[ℂ] H :=
      polarPartial T ∘L
        (P ∘L (polarRange T).subtypeL).codRestrict
          (polarRange T) (fun z => hpres z z.property)
    let g : polarRange T →L[ℂ] H := Q ∘L polarPartial T
    have hfg : f = g := by
      apply DenseRange.equalizer (denseRange_absOpCorestrict T)
        f.continuous g.continuous
      funext z
      change polarPartial T
          ⟨P (absOp T z), hpres _ (absOp_mem_polarRange T z)⟩ =
        Q (polarPartial T (absOpCorestrict T z))
      have hpabs := DFunLike.congr_fun habs z
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hpabs
      have hleft :
          (⟨P (absOp T z), hpres _ (absOp_mem_polarRange T z)⟩ : polarRange T) =
            absOpCorestrict T (P z) := by
        apply Subtype.ext
        simpa using hpabs.symm
      rw [hleft, polarPartial_absOpCorestrict, polarPartial_absOpCorestrict]
      exact DFunLike.congr_fun hTP z
    have hmproj : (polarRange T).orthogonalProjection m = ⟨m, hm⟩ := by
      apply Subtype.ext
      exact Submodule.starProjection_eq_self_iff.mpr hm
    have hPm : P m ∈ polarRange T := hpres m hm
    have hPmproj : (polarRange T).orthogonalProjection (P m) = ⟨P m, hPm⟩ := by
      apply Subtype.ext
      exact Submodule.starProjection_eq_self_iff.mpr hPm
    simpa [f, g, hmproj, hPmproj] using
      DFunLike.congr_fun hfg ⟨m, hm⟩
  simpa [polarIsometry_apply_eq] using heqOnDense

/-- The polar factor of the canonical two-projection intertwiner intertwines
both projections without an acuteness assumption. -/
theorem canonicalPolarFactor_intertwines_from_polar :
    spectraCanonicalPolarFactor U V ∘L projection U =
      projection V ∘L spectraCanonicalPolarFactor U V := by
  rw [spectraCanonicalPolarFactor, spectraPolarIsometry]
  apply polarIsometry_intertwines_of_projection_intertwining
  · exact ⟨U.isIdempotentElem_starProjection,
      (isSelfAdjoint_starProjection U).isSymmetric⟩
  · exact ⟨V.isIdempotentElem_starProjection,
      (isSelfAdjoint_starProjection V).isSymmetric⟩
  · simpa [ContinuousLinearMap.mul_def] using
      spectraCanonicalIntertwiner_mul_projection U V

/-- Taking adjoints exchanges the ordered pair of subspaces in the canonical
polar factor. -/
theorem canonicalPolarFactor_adjoint_swap_from_polar :
    star (spectraCanonicalPolarFactor U V) =
      spectraCanonicalPolarFactor V U := by
  rw [spectraCanonicalPolarFactor, spectraCanonicalPolarFactor,
    spectraPolarIsometry, spectraPolarIsometry]
  rw [← Spectra.QuantumMechanics.Channels.adjoint_polarIsometry]
  congr 1
  exact star_spectraCanonicalIntertwiner U V

end

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end ForMathlib
