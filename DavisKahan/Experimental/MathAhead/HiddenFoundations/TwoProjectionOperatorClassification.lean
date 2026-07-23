/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.MathAhead.HiddenFoundations.OrthogonalSummandCoordinates

/-!
# Operator-level classification of two projections

The spectral-multiplicity formulation in Davis--Kahan Theorem 3.1 requires a
separate direct-integral classification theorem.  The operator-theoretic core
is more elementary: the four Halmos summands and the pair of restricted
projections on the generic part form a complete invariant.  This file proves
that core statement by joining an equivalence on the trivial part with an
equivalence on the generic part.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open SpectraBridge

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {H' : Type v} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  [CompleteSpace H']

/-- Restriction of an ambient bounded operator to an invariant closed
subspace. -/
noncomputable def restrictToInvariant
    (T : H →L[ℂ] H) (K : Submodule ℂ H)
    (hK : ∀ x ∈ K, T x ∈ K) : K →L[ℂ] K :=
  T.codRestrict K (fun x => hK x x.property) ∘L K.subtypeL

@[simp] theorem restrictToInvariant_apply
    (T : H →L[ℂ] H) (K : Submodule ℂ H)
    (hK : ∀ x ∈ K, T x ∈ K) (x : K) :
    restrictToInvariant T K hK x = ⟨T x, hK x x.property⟩ := rfl

/-- The left projection preserves the trivial Halmos part. -/
theorem projection_left_invariant_halmosTrivialPart
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    ∀ x ∈ halmosTrivialPart U V, projection U x ∈ halmosTrivialPart U V :=
  projection_left_preserves_halmosTrivialPart U V

/-- The right projection preserves the trivial Halmos part. -/
theorem projection_right_invariant_halmosTrivialPart
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    ∀ x ∈ halmosTrivialPart U V, projection V x ∈ halmosTrivialPart U V :=
  projection_right_preserves_halmosTrivialPart U V

/-- Restricted left projection on the elementary Halmos summand. -/
noncomputable def trivialLeftProjection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosTrivialPart U V →L[ℂ] halmosTrivialPart U V :=
  restrictToInvariant (projection U) (halmosTrivialPart U V)
    (projection_left_invariant_halmosTrivialPart U V)

/-- Restricted right projection on the elementary Halmos summand. -/
noncomputable def trivialRightProjection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosTrivialPart U V →L[ℂ] halmosTrivialPart U V :=
  restrictToInvariant (projection V) (halmosTrivialPart U V)
    (projection_right_invariant_halmosTrivialPart U V)

/-- Restricted left projection on the generic Halmos summand. -/
noncomputable def genericLeftProjection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[ℂ] halmosGenericPart U V :=
  restrictToInvariant (projection U) (halmosGenericPart U V)
    (projection_left_reduces_halmosGenericPart U V).1

/-- Restricted right projection on the generic Halmos summand. -/
noncomputable def genericRightProjection
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    halmosGenericPart U V →L[ℂ] halmosGenericPart U V :=
  restrictToInvariant (projection V) (halmosGenericPart U V)
    (projection_right_reduces_halmosGenericPart U V).1

/-- Complete operator-level invariant data for a pair of projections.

The elementary equivalence records the four discrete Halmos multiplicities.
The generic equivalence records the unitary-equivalence class of the generic
pair of projections. -/
structure TwoProjectionOperatorEquivalence
    (U V : Submodule ℂ H) (U' V' : Submodule ℂ H')
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [U'.HasOrthogonalProjection] [V'.HasOrthogonalProjection] where
  trivialEquiv : halmosTrivialPart U V ≃ₗᵢ[ℂ] halmosTrivialPart U' V'
  genericEquiv : halmosGenericPart U V ≃ₗᵢ[ℂ] halmosGenericPart U' V'
  trivial_left :
    (trivialEquiv : halmosTrivialPart U V →L[ℂ] halmosTrivialPart U' V') ∘L
        trivialLeftProjection U V =
      trivialLeftProjection U' V' ∘L
        (trivialEquiv : halmosTrivialPart U V →L[ℂ] halmosTrivialPart U' V')
  trivial_right :
    (trivialEquiv : halmosTrivialPart U V →L[ℂ] halmosTrivialPart U' V') ∘L
        trivialRightProjection U V =
      trivialRightProjection U' V' ∘L
        (trivialEquiv : halmosTrivialPart U V →L[ℂ] halmosTrivialPart U' V')
  generic_left :
    (genericEquiv : halmosGenericPart U V →L[ℂ] halmosGenericPart U' V') ∘L
        genericLeftProjection U V =
      genericLeftProjection U' V' ∘L
        (genericEquiv : halmosGenericPart U V →L[ℂ] halmosGenericPart U' V')
  generic_right :
    (genericEquiv : halmosGenericPart U V →L[ℂ] halmosGenericPart U' V') ∘L
        genericRightProjection U V =
      genericRightProjection U' V' ∘L
        (genericEquiv : halmosGenericPart U V →L[ℂ] halmosGenericPart U' V')

namespace TwoProjectionOperatorEquivalence

variable {U V : Submodule ℂ H} {U' V' : Submodule ℂ H'}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
  [U'.HasOrthogonalProjection] [V'.HasOrthogonalProjection]

/-- Assemble the elementary and generic equivalences into an ambient unitary. -/
noncomputable def ambient
    (D : TwoProjectionOperatorEquivalence U V U' V') : H ≃ₗᵢ[ℂ] H' :=
  (orthogonalDecompositionEquiv (halmosTrivialPart U V)).trans
    ((LinearIsometryEquiv.prod D.trivialEquiv D.genericEquiv).withLp 2) |>.trans
      (orthogonalDecompositionEquiv (halmosTrivialPart U' V')).symm

private theorem ambient_apply_trivial
    (D : TwoProjectionOperatorEquivalence U V U' V')
    (x : halmosTrivialPart U V) :
    D.ambient (x : H) = (D.trivialEquiv x : H') := by
  simp [ambient, orthogonalDecompositionEquiv, orthogonalCoordinates,
    orthogonalCoordinatesInv]

private theorem ambient_apply_generic
    (D : TwoProjectionOperatorEquivalence U V U' V')
    (x : halmosGenericPart U V) :
    D.ambient (x : H) = (D.genericEquiv x : H') := by
  simp [ambient, orthogonalDecompositionEquiv, orthogonalCoordinates,
    orthogonalCoordinatesInv]

/-- The assembled ambient unitary intertwines the left projections. -/
theorem ambient_intertwines_left
    (D : TwoProjectionOperatorEquivalence U V U' V') :
    (D.ambient : H →L[ℂ] H') ∘L projection U =
      projection U' ∘L (D.ambient : H →L[ℂ] H') := by
  apply ContinuousLinearMap.ext
  intro x
  let T := halmosTrivialPart U V
  let G := halmosGenericPart U V
  have hsplit : x = T.starProjection x + G.starProjection x := by
    simpa [T, G] using (halmosTrivialPart U V).
      starProjection_add_starProjection_orthogonal x |>.symm
  rw [hsplit]
  simp only [map_add, ContinuousLinearMap.comp_apply]
  have ht : T.starProjection x ∈ T := T.starProjection_apply_mem x
  have hg : G.starProjection x ∈ G := G.starProjection_apply_mem x
  have hPt : projection U (T.starProjection x) ∈ T :=
    projection_left_invariant_halmosTrivialPart U V _ ht
  have hPg : projection U (G.starProjection x) ∈ G :=
    (projection_left_reduces_halmosGenericPart U V).1 _ hg
  rw [D.ambient_apply_trivial ⟨_, hPt⟩,
    D.ambient_apply_generic ⟨_, hPg⟩,
    D.ambient_apply_trivial ⟨_, ht⟩,
    D.ambient_apply_generic ⟨_, hg⟩]
  have htEq := DFunLike.congr_fun D.trivial_left ⟨T.starProjection x, ht⟩
  have hgEq := DFunLike.congr_fun D.generic_left ⟨G.starProjection x, hg⟩
  apply congrArg Subtype.val at htEq
  apply congrArg Subtype.val at hgEq
  simpa [trivialLeftProjection, genericLeftProjection,
    restrictToInvariant] using congrArg₂ (· + ·) htEq hgEq

/-- The assembled ambient unitary intertwines the right projections. -/
theorem ambient_intertwines_right
    (D : TwoProjectionOperatorEquivalence U V U' V') :
    (D.ambient : H →L[ℂ] H') ∘L projection V =
      projection V' ∘L (D.ambient : H →L[ℂ] H') := by
  apply ContinuousLinearMap.ext
  intro x
  let T := halmosTrivialPart U V
  let G := halmosGenericPart U V
  have hsplit : x = T.starProjection x + G.starProjection x := by
    simpa [T, G] using (halmosTrivialPart U V).
      starProjection_add_starProjection_orthogonal x |>.symm
  rw [hsplit]
  simp only [map_add, ContinuousLinearMap.comp_apply]
  have ht : T.starProjection x ∈ T := T.starProjection_apply_mem x
  have hg : G.starProjection x ∈ G := G.starProjection_apply_mem x
  have hPt : projection V (T.starProjection x) ∈ T :=
    projection_right_invariant_halmosTrivialPart U V _ ht
  have hPg : projection V (G.starProjection x) ∈ G :=
    (projection_right_reduces_halmosGenericPart U V).1 _ hg
  rw [D.ambient_apply_trivial ⟨_, hPt⟩,
    D.ambient_apply_generic ⟨_, hPg⟩,
    D.ambient_apply_trivial ⟨_, ht⟩,
    D.ambient_apply_generic ⟨_, hg⟩]
  have htEq := DFunLike.congr_fun D.trivial_right ⟨T.starProjection x, ht⟩
  have hgEq := DFunLike.congr_fun D.generic_right ⟨G.starProjection x, hg⟩
  apply congrArg Subtype.val at htEq
  apply congrArg Subtype.val at hgEq
  simpa [trivialRightProjection, genericRightProjection,
    restrictToInvariant] using congrArg₂ (· + ·) htEq hgEq

/-- The assembled unitary maps the first subspace onto the first subspace. -/
theorem map_left
    (D : TwoProjectionOperatorEquivalence U V U' V') :
    U.map D.ambient.toLinearMap = U' := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hpx : projection U x = x := U.starProjection_eq_self_iff.mpr hx
    have h := DFunLike.congr_fun D.ambient_intertwines_left x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hpx] at h
    exact U'.starProjection_eq_self_iff.mp h.symm
  · intro y hy
    let x := D.ambient.symm y
    refine ⟨x, ?_, D.ambient.apply_symm_apply y⟩
    have hpy : projection U' y = y := U'.starProjection_eq_self_iff.mpr hy
    have h := DFunLike.congr_fun D.ambient_intertwines_left x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      D.ambient.apply_symm_apply y, hpy] at h
    exact U.starProjection_eq_self_iff.mp (D.ambient.injective h)

/-- The assembled unitary maps the second subspace onto the second subspace. -/
theorem map_right
    (D : TwoProjectionOperatorEquivalence U V U' V') :
    V.map D.ambient.toLinearMap = V' := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hpx : projection V x = x := V.starProjection_eq_self_iff.mpr hx
    have h := DFunLike.congr_fun D.ambient_intertwines_right x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hpx] at h
    exact V'.starProjection_eq_self_iff.mp h.symm
  · intro y hy
    let x := D.ambient.symm y
    refine ⟨x, ?_, D.ambient.apply_symm_apply y⟩
    have hpy : projection V' y = y := V'.starProjection_eq_self_iff.mpr hy
    have h := DFunLike.congr_fun D.ambient_intertwines_right x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      D.ambient.apply_symm_apply y, hpy] at h
    exact V.starProjection_eq_self_iff.mp (D.ambient.injective h)

end TwoProjectionOperatorEquivalence

/-- Modern operator-level form of Davis--Kahan Theorem 3.1.

The paper's spectral-multiplicity statement follows once a separate theorem
identifies unitary equivalence of the generic self-adjoint cosine operators
with equality of their spectral multiplicity functions. -/
theorem twoProjection_operator_classification
    {U V : Submodule ℂ H} {U' V' : Submodule ℂ H'}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    [U'.HasOrthogonalProjection] [V'.HasOrthogonalProjection]
    (D : TwoProjectionOperatorEquivalence U V U' V') :
    ∃ W : H ≃ₗᵢ[ℂ] H',
      U.map W.toLinearMap = U' ∧ V.map W.toLinearMap = V' := by
  exact ⟨D.ambient, D.map_left, D.map_right⟩

end

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end ForMathlib
