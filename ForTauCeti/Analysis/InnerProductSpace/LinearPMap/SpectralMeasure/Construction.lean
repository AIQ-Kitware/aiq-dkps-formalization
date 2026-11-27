/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.PairShift
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Bounded

public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Cayley.Basic
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint

/-!
# Spectral projections and ranges of a self-adjoint partial operator

The spectral projections use Tau Ceti's real pushforward of the spectral
measure of the Cayley transform. The native intertwining and projection laws
supply invariance of the partial operator's domain and action.

These definitions and lemmas grew out of the DKPS spectral-measure
construction split in July 2026. The original construction followed the
classical Cayley route as in Rudin and Reed–Simon. See the contribution census
for its relationship to the native Tau Ceti construction and the former
Spectra dependency.
-/

public section

open scoped InnerProductSpace
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Restriction

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The spectral projection of an unbounded self-adjoint operator onto a Borel
set of the real line. Its body lets the native spectral restriction use the same range. -/
@[expose]
noncomputable def specProjection (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H :=
  (A.spectralPVM hA).proj B hB

/-- Rewrite form of `specProjection` against the projection-valued measure, for the consumers
that want the `ProjValMeasure` API (`norm_sq_proj_apply`, `inner_proj`) rather than the Borel
calculus underneath it. -/
theorem specProjection_def (B : Set ℝ) (hB : MeasurableSet B) :
    specProjection hA B hB = (A.spectralPVM hA).proj B hB := (rfl)

/-- A spectral projection is the calculus of the pulled-back indicator on the Cayley
spectrum. This form is used in the conjugation arguments. -/
theorem specProjection_eq_borelCalculus (B : Set ℝ) (hB : MeasurableSet B) :
    haveI := hA.isStarNormal_cayley
    specProjection hA B hB = A.cayley.borelCalculus
      (BoundedBorelFunction.indicator
        ((fun w : spectrum ℂ A.cayley => Complex.inverseCayleyCoord (w : ℂ)) ⁻¹' B)
        ((Complex.measurable_inverseCayleyCoord.comp measurable_subtypeVal) hB) 1) := by
  have := hA.isStarNormal_cayley
  rw [specProjection_def, hA.spectralPVM_proj, A.cayley.borelCalculus_indicator]

/-- Spectral projections preserve the domain. -/
theorem specProjection_mem_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    specProjection hA B hB (x : H) ∈ A.domain :=
  (hA.intertwines_spectralPVM_proj B hB).mem_domain x

/-- Spectral projections intertwine the operator. -/
theorem specProjection_apply_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    A ⟨specProjection hA B hB (x : H), specProjection_mem_domain hA B hB x⟩
      = specProjection hA B hB (A x) :=
  ((hA.intertwines_spectralPVM_proj B hB).apply_eq x).symm

/-- Spectral projections are idempotent. -/
theorem isIdempotentElem_specProjection (B : Set ℝ) (hB : MeasurableSet B) :
    IsIdempotentElem (specProjection hA B hB) :=
  (A.spectralPVM hA).proj_idem B hB

/-- Spectral projections are self-adjoint.  With idempotence this makes them *orthogonal*
projections, which is what gives `specRange` an orthogonal complement. -/
theorem isSelfAdjoint_specProjection (B : Set ℝ) (hB : MeasurableSet B) :
    IsSelfAdjoint (specProjection hA B hB) :=
  (A.spectralPVM hA).isSelfAdjoint_proj B hB

end Restriction

section Reduce

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B)

/-- The **spectral range** of `A` over a Borel set: the range of the spectral
projection, a closed, orthogonally complemented subspace. -/
@[expose]
noncomputable def specRange : Submodule ℂ H := (specProjection hA B hB).range

/-- A vector lies in the spectral range exactly when the spectral projection fixes it -- the usable
criterion, since the range is defined as an image. -/
theorem mem_specRange_iff (x : H) :
    x ∈ specRange hA B hB ↔ specProjection hA B hB x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    have h : specProjection hA B hB (specProjection hA B hB y) = specProjection hA B hB y := by
      have h2 := congrArg (fun T : H →L[ℂ] H => T y)
        (isIdempotentElem_specProjection hA B hB)
      simpa only [_root_.mul_apply_eq_comp] using h2
    exact h
  · intro hx
    exact ⟨x, hx⟩

/-- **Every spectral projection image lies in the spectral range.**  This is the membership a
consumer wants, and it is stated because the alternative is `⟨y, rfl⟩`, which proves the same
thing only by making `specRange` reduce to a `LinearMap.range` — the one call pattern that
kept the definition's body exposed across module boundaries. -/
theorem specProjection_mem_specRange (y : H) :
    specProjection hA B hB y ∈ specRange hA B hB :=
  (mem_specRange_iff hA B hB _).mpr <| by
    have h2 := congrArg (fun T : H →L[ℂ] H => T y)
      (isIdempotentElem_specProjection hA B hB)
    simpa only [_root_.mul_apply_eq_comp] using h2

/-- The spectral range is complete, being the range of an idempotent bounded operator and hence
closed in `H`. -/
noncomputable instance instCompleteSpace_specRange : CompleteSpace (specRange hA B hB) := by
  change CompleteSpace (specProjection hA B hB).range
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (isIdempotentElem_specProjection hA B hB)).completeSpace_coe

/-- The spectral range is orthogonally complemented, so `A` genuinely *reduces* to it rather than
merely restricting. -/
noncomputable instance instHasOrthogonalProjection_specRange :
    (specRange hA B hB).HasOrthogonalProjection := by
  change (specProjection hA B hB).range.HasOrthogonalProjection
  exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (isIdempotentElem_specProjection hA B hB)

/-- **The spectral projection is the orthogonal projection onto its range.**
This is intrinsic spectral-range structure, not double-angle machinery: it is
the bridge from the PVM projection to the submodule API used by every reducing
subspace consumer. -/
theorem specProjection_eq_starProjection_specRange :
    specProjection hA B hB = (specRange hA B hB).starProjection :=
  ((A.spectralPVM hA).starProjection_range_proj B hB).symm

/-- The image of a domain vector of the spectral range stays in the spectral
range. -/
theorem apply_mem_specRange {x : A.domain} (hx : (x : H) ∈ specRange hA B hB) :
    A x ∈ specRange hA B hB := by
  have hfix : specProjection hA B hB (x : H) = (x : H) := (mem_specRange_iff hA B hB _).mp hx
  have h := specProjection_apply_domain hA B hB x
  have hsub : (⟨specProjection hA B hB (x : H),
      specProjection_mem_domain hA B hB x⟩ : A.domain) = x := Subtype.ext hfix
  rw [hsub] at h
  exact (mem_specRange_iff hA B hB _).mpr h.symm

/-- Spectral projection on a complement set is the complementary orthogonal
projection. -/
theorem specProjection_compl :
    specProjection hA Bᶜ hB.compl =
      ContinuousLinearMap.id ℂ H - specProjection hA B hB := by
  simpa only [specProjection_def] using (A.spectralPVM hA).proj_compl B hB

/-- The spectral range of a complement set is the orthogonal complement of the
original spectral range. -/
theorem specRange_compl :
    specRange hA Bᶜ hB.compl = (specRange hA B hB)ᗮ := by
  apply Submodule.ext
  intro x
  rw [← Submodule.starProjection_eq_self_iff,
    ← Submodule.starProjection_eq_self_iff]
  rw [← specProjection_eq_starProjection_specRange,
    specProjection_compl,
    Submodule.starProjection_orthogonal,
    ← specProjection_eq_starProjection_specRange]

end Reduce

end LinearPMap
end TauCeti
