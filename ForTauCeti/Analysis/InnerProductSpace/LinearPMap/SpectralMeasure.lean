/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent

/-!
# The spectral measure of an unbounded self-adjoint operator

The Cayley transform `U = (A - i)(A + i)⁻¹` of a self-adjoint `A : H →ₗ.[ℂ] H`
is a bounded unitary, so it carries the bounded Borel functional calculus of
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/`.  Relabelling its
spectrum by the inverse Cayley map `w ↦ i(1+w)/(1-w)` turns that calculus into a
projection-valued measure on the Borel sets of `ℝ`: `spectralPVM hA`.

The inverse Cayley map blows up at `w = 1`, which can lie in `spectrum ℂ U`.
The relabelling therefore takes a junk value there, and the construction is only
faithful because the diagonal measures give `{1}` no mass —
`diagMeasure_cayley_preimage_one`.  The reason is short and lives entirely
inside the Borel calculus: `(1 - U)` annihilates the spectral projection of
`{1}` (the symbol `(1 - w) · 1_{{1}}(w)` is identically zero), while `1 - U` is
`2i` times the resolvent `(A + i)⁻¹` and hence injective.

## Provenance

*New*; see `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean`
for the provenance of the route, and `dev/tauceti/spectra-removal-plan.md` for
the comparison against Spectra's Herglotz/Poisson route that chose it.  The
target is the Spectra endpoint
`Spectra.QuantumMechanics.SpectralTheory.spectralPVM`.
-/

@[expose] public section

open scoped InnerProductSpace
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Cayley

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- `1 - U = 2i · R(-i)`: immediate from the definition of the Cayley
transform. -/
theorem one_sub_cayley_apply (ξ : H) :
    ((1 : H →L[ℂ] H) - cayley hA) ξ
      = (2 * Complex.I) • resolvent A (negI_mem_resolventSet hA) ξ := by
  simp [cayley]

/-- The resolvent at `-i` is injective — it inverts the bijection
`A + i : dom A → H`. -/
theorem injective_resolvent_negI :
    Function.Injective (resolvent A (negI_mem_resolventSet hA)) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  have hsub := sub_smul_resolvent (negI_mem_resolventSet hA) φ
  have hz : (⟨resolvent A (negI_mem_resolventSet hA) φ,
      resolvent_mem_domain (negI_mem_resolventSet hA) φ⟩ : A.domain) = 0 :=
    Subtype.ext (by simpa using hφ)
  rw [hz, _root_.LinearPMap.map_zero, hφ] at hsub
  simpa using hsub.symm

/-- Hence `1 - U` is injective. -/
theorem injective_one_sub_cayley :
    Function.Injective ((1 : H →L[ℂ] H) - cayley hA) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  rw [one_sub_cayley_apply] at hφ
  have h2 : (2 * Complex.I : ℂ) ≠ 0 := by simp
  have hR : resolvent A (negI_mem_resolventSet hA) φ = 0 := by
    rcases smul_eq_zero.mp hφ with h | h
    · exact absurd h h2
    · exact h
  exact injective_resolvent_negI hA (by simpa using hR)

/-- The **inverse Cayley map** `w ↦ i(1+w)/(1-w)`, as a real-valued relabelling
of the spectrum of the Cayley transform.  Its value at `w = 1` is junk; see
`diagMeasure_cayley_preimage_one`. -/
noncomputable def cayleyInv (w : _root_.spectrum ℂ (cayley hA)) : ℝ :=
  (Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ))).re

theorem measurable_cayleyInv : Measurable (cayleyInv hA) := by
  unfold cayleyInv
  fun_prop

/-- **The spectral measure of an unbounded self-adjoint operator.** -/
noncomputable def spectralPVM : TauCeti.ProjValMeasure H :=
  BorelCalculus.toProjValMeasure (isStarNormal_cayley hA) (measurable_cayleyInv hA)

/-- The Cayley singularity `{1}` is a null set for every diagonal measure. -/
theorem diagMeasure_cayley_preimage_one (ξ : H) :
    BorelCalculus.diagMeasure (isStarNormal_cayley hA) ξ
      ((Subtype.val : _root_.spectrum ℂ (cayley hA) → ℂ) ⁻¹' {1}) = 0 := by
  set U := cayley hA with hUdef
  set hU := isStarNormal_cayley hA with hUn
  set S : Set (_root_.spectrum ℂ U) := (Subtype.val : _root_.spectrum ℂ U → ℂ) ⁻¹' {1} with hSdef
  have hS : MeasurableSet S := measurable_subtype_coe (measurableSet_singleton 1)
  set ind : _root_.spectrum ℂ U → ℂ := S.indicator (fun _ => (1 : ℂ)) with hind
  have hindb : BorelCalculus.IsBddMeasurable ind :=
    BorelCalculus.isBddMeasurable_indicator (a := U) hS
  set X : C(_root_.spectrum ℂ U, ℂ) := (ContinuousMap.id ℂ).restrict (_root_.spectrum ℂ U) with hX
  set c : C(_root_.spectrum ℂ U, ℂ) := 1 - X with hc
  have hcb : BorelCalculus.IsBddMeasurable (fun w => c w) :=
    BorelCalculus.IsBddMeasurable.of_continuous c
  -- `borelCalculus` of the continuous symbol `1 - w` is `1 - U`
  have hcU : BorelCalculus.borelCalculus hU hcb = (1 : H →L[ℂ] H) - U := by
    rw [BorelCalculus.borelCalculus_of_continuous, hc, map_sub, map_one, cfcHom_id]
  -- the product symbol vanishes identically
  have hpt : ∀ w, c w * ind w = 0 := by
    intro w
    by_cases hw : w ∈ S
    · have hw1 : (w : ℂ) = 1 := hw
      have : c w = 0 := by
        simp only [hc, hX, ContinuousMap.sub_apply, ContinuousMap.one_apply,
          ContinuousMap.restrict_apply, ContinuousMap.id_apply, hw1, sub_self]
      rw [this, zero_mul]
    · rw [hind, Set.indicator_of_notMem hw, mul_zero]
  have hprodzero : BorelCalculus.borelCalculus hU (hcb.mul hindb) = 0 := by
    refine op_ext_of_inner_self fun η => ?_
    rw [BorelCalculus.inner_borelCalculus_self]
    simp only [hpt, integral_zero, _root_.zero_apply, inner_zero_right]
  -- so `(1 - U)` annihilates the spectral projection of `{1}`
  have hann : ∀ η : H, ((1 : H →L[ℂ] H) - U) (BorelCalculus.borelCalculus hU hindb η) = 0 := by
    intro η
    have hmul := BorelCalculus.borelCalculus_mul hU hcb hindb
    rw [hprodzero, hcU] at hmul
    have := congrArg (fun T : H →L[ℂ] H => T η) hmul.symm
    simpa using this
  have hPzero : BorelCalculus.borelCalculus hU hindb ξ = 0 :=
    injective_one_sub_cayley hA (by simpa using hann ξ)
  -- and the diagonal matrix element is the mass of `{1}`
  have hdiag := BorelCalculus.inner_borelCalculus_self hU hindb ξ
  rw [hPzero, inner_zero_right, hind,
    integral_indicator_const _ hS, Complex.real_smul, mul_one] at hdiag
  have : (BorelCalculus.diagMeasure hU ξ).real S = 0 := by
    exact_mod_cast hdiag.symm
  rw [MeasureTheory.measureReal_def] at this
  exact (ENNReal.toReal_eq_zero_iff _).mp this |>.resolve_right (measure_ne_top _ _)

end Cayley

end LinearPMap
end TauCeti
