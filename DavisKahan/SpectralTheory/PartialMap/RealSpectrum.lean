/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import DavisKahan.BoundedOperator.Problem
import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# The real resolvent of a partial map, and the ambient spectrum

`TauCeti.LinearPMap.realResolventSet` is defined without importing the ambient
spectral theory, so it remains available over every `RCLike` scalar field.  This
file identifies its complex specialization with the ambient spectrum.  The
bridge is intentionally kept above both foundations to avoid an import cycle.
-/

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ### The donor and upstream resolvent representations

The paper-facing layer still uses the normed donor resolvent in a few places,
while Tau Ceti's accepted `LinearPMap` API uses Mathlib's continuous resolvent.
Their inverse records have the same three fields, so conversion is centralized
here for the remaining consumers. -/

omit [CompleteSpace E] in
/-- Membership in the donor and upstream resolvent sets is equivalent. -/
theorem mem_local_resolventSet_iff_root
    (A : E →ₗ.[ℂ] E) (z : ℂ) :
    z ∈ TauCeti.LinearPMap.resolventSet A ↔
      z ∈ _root_.LinearPMap.resolventSet A := by
  rw [TauCeti.LinearPMap.mem_resolventSet_iff,
    _root_.LinearPMap.mem_resolventSet_iff]
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R, {
      mem_domain := hR.mem_domain
      smul_sub_apply := hR.smul_sub_apply
      apply_smul_sub := hR.apply_smul_sub
    }⟩
  · rintro ⟨R, hR⟩
    exact ⟨R, {
      mem_domain := hR.mem_domain
      smul_sub_apply := hR.smul_sub_apply
      apply_smul_sub := hR.apply_smul_sub
    }⟩

omit [CompleteSpace E] in
/-- The donor and accepted partial-map spectra have the same membership. -/
theorem mem_spectrum_iff_root
    (A : E →ₗ.[ℂ] E) (z : ℂ) :
    z ∈ TauCeti.LinearPMap.spectrum A ↔
      z ∈ _root_.LinearPMap.spectrum A := by
  rw [TauCeti.LinearPMap.mem_spectrum_iff,
    _root_.LinearPMap.mem_spectrum_iff]
  exact not_congr (mem_local_resolventSet_iff_root A z)

variable {F : Type v}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The donor and accepted partial-map spectra have the same disjointness
relation. This keeps the remaining donor theorem boundary conversion in one
place while its consumers use Tau Ceti's spectrum. -/
theorem disjoint_spectrum_iff_root
    (A : E →ₗ.[ℂ] E) (B : F →ₗ.[ℂ] F) :
    Disjoint (TauCeti.LinearPMap.spectrum A) (TauCeti.LinearPMap.spectrum B) ↔
      Disjoint (_root_.LinearPMap.spectrum A) (_root_.LinearPMap.spectrum B) := by
  rw [Set.disjoint_left, Set.disjoint_left]
  constructor
  · intro h z hzA hzB
    exact h (mem_spectrum_iff_root A z |>.mpr hzA)
      (mem_spectrum_iff_root B z |>.mpr hzB)
  · intro h z hzA hzB
    exact h (mem_spectrum_iff_root A z |>.mp hzA)
      (mem_spectrum_iff_root B z |>.mp hzB)

omit [CompleteSpace E] in
/-- Membership in the closed-operator real resolvent is exactly membership of
the real scalar in the canonical resolvent set.

The two predicates invert opposite shifts — `realResolventSet` asks for a bounded
two-sided inverse of `A - lam`, while `TauCeti.LinearPMap.resolventSet` asks for one of
`lam • I - A` — so they are *not* definitionally equal, and this was a `rfl` only while the
resolvent core used the `A - z` convention.  They do describe the same set: the two shifts
differ by a sign, and negating a bounded two-sided inverse gives a bounded two-sided inverse
of the negated map.  That negation is the whole content of the proof. -/
theorem mem_realResolventSet_iff_mem_spectraResolvent
    (A : E →ₗ.[ℂ] E) (lam : ℝ) :
    lam ∈ TauCeti.LinearPMap.realResolventSet A ↔
      (lam : ℂ) ∈ TauCeti.LinearPMap.resolventSet A := by
  rw [TauCeti.LinearPMap.mem_realResolventSet_iff, TauCeti.LinearPMap.mem_resolventSet_iff]
  constructor
  · rintro ⟨R, hleft, hright⟩
    refine ⟨-R, fun y => neg_mem (hright y).choose, fun y => ?_, fun x => ?_⟩
    · have h := (hright y).choose_spec
      have hneg : A
            (⟨(-R) y, neg_mem (hright y).choose⟩ : A.domain)
          = -(A ⟨R y, (hright y).choose⟩) :=
        _root_.LinearPMap.map_neg A ⟨R y, (hright y).choose⟩
      rw [hneg]
      simp only [_root_.neg_apply]
      linear_combination (norm := module) h
    · have h := hleft x
      have harg : (lam : ℂ) • (x : E) - A x
          = -(A x - (lam : ℂ) • (x : E)) := by module
      simp only [_root_.neg_apply, harg, map_neg, neg_neg]
      exact h
  · rintro ⟨R, hR⟩
    refine ⟨-R, fun x => ?_, fun y => ?_⟩
    · -- the scalar is abstracted so that the `RCLike` coercion of `realResolventSet` and the
      -- `ℂ` coercion of `IsResolventAt`, which are defeq but not syntactically equal, unify
      have hstep : ∀ c : ℂ, R (c • (x : E) - A x) = (x : E) →
          (-R) (A x - c • (x : E)) = (x : E) := by
        intro c hc
        have harg : A x - c • (x : E)
            = -(c • (x : E) - A x) := by module
        rw [_root_.neg_apply, harg, map_neg, hc, neg_neg]
      exact hstep _ (hR.apply_smul_sub x)
    · refine ⟨neg_mem (hR.mem_domain y), ?_⟩
      have h := hR.smul_sub_apply y
      have hneg : A
            (⟨(-R) y, neg_mem (hR.mem_domain y)⟩ : A.domain)
          = -(A ⟨R y, hR.mem_domain y⟩) :=
        _root_.LinearPMap.map_neg A ⟨R y, hR.mem_domain y⟩
      rw [hneg]
      simp only [_root_.neg_apply]
      linear_combination (norm := module) h

omit [CompleteSpace E] in
/-- The generic closed-operator real spectrum agrees with the genuine spectrum
after specializing the scalar field to `ℂ`.

Complementation of `mem_realResolventSet_iff_mem_spectraResolvent`; like it, this was a
`rfl` only under the `A - z` convention. -/
theorem realSpectrum_eq_spectraSpectrum (A : E →ₗ.[ℂ] E) :
    TauCeti.LinearPMap.realSpectrum A
      = Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A := by
  ext lam
  rw [Set.mem_preimage, TauCeti.LinearPMap.mem_spectrum_iff,
    TauCeti.LinearPMap.mem_realSpectrum_iff,
    mem_realResolventSet_iff_mem_spectraResolvent A lam]

/-! ## The spectrum of a self-adjoint operator is real

Tau Ceti proves the more general `RCLike` statement that the spectrum lies on
the zero-imaginary axis. The paper-facing wrapper retains the donor spectrum
type used by its downstream theorem, translating its membership to the
canonical spectrum before applying that result. -/

/-- **A self-adjoint partial map has real spectrum.** -/
theorem spectrum_subset_real_of_isSelfAdjoint {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) :
    TauCeti.LinearPMap.spectrum A ⊆ Complex.ofReal '' Set.univ := by
  intro z hz
  have hzLocalNot : z ∉ TauCeti.LinearPMap.resolventSet A :=
    TauCeti.LinearPMap.mem_spectrum_iff.mp hz
  have hzRoot : z ∈ _root_.LinearPMap.spectrum A := by
    change z ∉ _root_.LinearPMap.resolventSet A
    intro hRoot
    obtain ⟨R, hR⟩ := _root_.LinearPMap.mem_resolventSet_iff.mp hRoot
    exact hzLocalNot <| TauCeti.LinearPMap.mem_resolventSet_iff.mpr ⟨R, {
      mem_domain := hR.mem_domain
      smul_sub_apply := hR.smul_sub_apply
      apply_smul_sub := hR.apply_smul_sub
    }⟩
  have him : z.im = 0 := hA.spectrum_subset_im_eq_zero hzRoot
  exact ⟨z.re, Set.mem_univ _, by simp [Complex.ext_iff, him]⟩

end DavisKahan
end TauCeti
