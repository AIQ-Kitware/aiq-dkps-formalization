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

section ResolventFormula

/-- The Cayley denominator `(i - z) + (i + z) w` has no zero on the unit circle
when `z` is not real: a zero would force `‖z - i‖ = ‖z + i‖`. -/
theorem cayley_denom_ne_zero {z : ℂ} (hz : z.im ≠ 0) {w : ℂ} (hw : ‖w‖ = 1) :
    (Complex.I - z) + (Complex.I + z) * w ≠ 0 := by
  intro h
  have hkey : (Complex.I + z) * w = z - Complex.I := by linear_combination h
  have hn : ‖Complex.I + z‖ = ‖z - Complex.I‖ := by
    have h' := congrArg norm hkey
    rwa [norm_mul, hw, mul_one] at h'
  have h2 : Complex.normSq (Complex.I + z) = Complex.normSq (z - Complex.I) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hn]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.I_re, Complex.I_im] at h2
  exact hz (by nlinarith [h2])

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0)

/-- The coordinate function on the spectrum of the Cayley transform. -/
noncomputable def cayleyCoord : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
  (ContinuousMap.id ℂ).restrict (_root_.spectrum ℂ (cayley hA))

@[simp] theorem cayleyCoord_apply (w : _root_.spectrum ℂ (cayley hA)) :
    cayleyCoord hA w = (w : ℂ) := rfl

include hz in
theorem cayleyDenom_ne_zero (w : _root_.spectrum ℂ (cayley hA)) :
    (Complex.I - z) + (Complex.I + z) * (w : ℂ) ≠ 0 :=
  cayley_denom_ne_zero hz
    (spectrum.norm_eq_one_of_unitary (cayley_mem_unitary hA) w.2)

/-- The symbol of `1 - (z + i) R(-i)`, up to the factor `2i`. -/
noncomputable def cayleyDenomCM : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
  ⟨fun w => (Complex.I - z) + (Complex.I + z) * (w : ℂ), by fun_prop⟩

@[simp] theorem cayleyDenomCM_apply (w : _root_.spectrum ℂ (cayley hA)) :
    cayleyDenomCM hA (z := z) w = (Complex.I - z) + (Complex.I + z) * (w : ℂ) := rfl

/-- The **resolvent symbol** `g_z(w) = (1 - w) / ((i - z) + (i + z) w)`.  For
non-real `z` it is continuous on the whole spectrum of the Cayley transform:
its only pole is the Cayley image of `z`, which is off the unit circle. -/
noncomputable def resolventSymbol : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
  ⟨fun w => (1 - (w : ℂ)) / ((Complex.I - z) + (Complex.I + z) * (w : ℂ)),
    Continuous.div (by fun_prop) (by fun_prop) (cayleyDenom_ne_zero hA hz)⟩

@[simp] theorem resolventSymbol_apply (w : _root_.spectrum ℂ (cayley hA)) :
    resolventSymbol hA hz w
      = (1 - (w : ℂ)) / ((Complex.I - z) + (Complex.I + z) * (w : ℂ)) := rfl

/-- The reciprocal of the denominator symbol, scaled by `2i`. -/
noncomputable def cayleyDenomInvCM : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
  ⟨fun w => (2 * Complex.I) / ((Complex.I - z) + (Complex.I + z) * (w : ℂ)),
    Continuous.div (by fun_prop) (by fun_prop) (cayleyDenom_ne_zero hA hz)⟩

@[simp] theorem cayleyDenomInvCM_apply (w : _root_.spectrum ℂ (cayley hA)) :
    cayleyDenomInvCM hA hz w
      = (2 * Complex.I) / ((Complex.I - z) + (Complex.I + z) * (w : ℂ)) := rfl

theorem two_I_ne_zero : (2 * Complex.I : ℂ) ≠ 0 := by simp

/-- `R(-i)` is the functional calculus of `(1 - w)/(2i)`. -/
theorem resolvent_negI_eq_cfcHom :
    resolvent A (negI_mem_resolventSet hA)
      = cfcHom (isStarNormal_cayley hA) ((2 * Complex.I)⁻¹ • (1 - cayleyCoord hA)) := by
  rw [map_smul, map_sub, map_one, cayleyCoord, cfcHom_id]
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [_root_.smul_apply, one_sub_cayley_apply, smul_smul, inv_mul_cancel₀ two_I_ne_zero,
    one_smul]

/-- `1 - (z + i) R(-i)` is the functional calculus of `((i - z) + (i + z)w)/(2i)`. -/
theorem one_sub_smul_resolvent_eq_cfcHom :
    (1 : H →L[ℂ] H) - (z + Complex.I) • resolvent A (negI_mem_resolventSet hA)
      = cfcHom (isStarNormal_cayley hA) ((2 * Complex.I)⁻¹ • cayleyDenomCM hA (z := z)) := by
  have hsplit : cayleyDenomCM hA (z := z)
      = (Complex.I - z) • 1 + (Complex.I + z) • cayleyCoord hA := by
    ext w
    simp [cayleyDenomCM, smul_eq_mul]
  rw [hsplit, map_smul, map_add, map_smul, map_smul, map_one, cayleyCoord, cfcHom_id]
  refine ContinuousLinearMap.ext fun ξ => ?_
  have h2 : (2 * Complex.I : ℂ) ≠ 0 := two_I_ne_zero
  have hU : cayley hA ξ = ξ - (2 * Complex.I) • resolvent A (negI_mem_resolventSet hA) ξ := by
    have h := one_sub_cayley_apply hA ξ
    rw [_root_.sub_apply, one_apply_eq_self] at h
    linear_combination (norm := module) -h
  simp only [_root_.sub_apply, one_apply_eq_self, _root_.smul_apply, _root_.add_apply, hU]
  match_scalars <;> (field_simp; try ring)

include hz in
/-- **The resolvent is the continuous functional calculus of `g_z`.**  Proved
through the first resolvent identity, so no statement about `dom A` is
needed. -/
theorem resolvent_eq_cfcHom (hzr : z ∈ resolventSet A) :
    resolvent A hzr = cfcHom (isStarNormal_cayley hA) (resolventSymbol hA hz) := by
  set hni := negI_mem_resolventSet hA with hhni
  set hU := isStarNormal_cayley hA with hhU
  -- the two functional-calculus factors are mutually inverse
  have hprod : ((2 * Complex.I)⁻¹ • cayleyDenomCM hA (z := z)) * cayleyDenomInvCM hA hz
      = 1 := by
    ext w
    have hne := cayleyDenom_ne_zero hA hz w
    have h2 : (2 * Complex.I : ℂ) ≠ 0 := two_I_ne_zero
    simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, cayleyDenomCM_apply,
      cayleyDenomInvCM_apply, ContinuousMap.one_apply, smul_eq_mul]
    field_simp
  have hinv : cfcHom hU ((2 * Complex.I)⁻¹ • cayleyDenomCM hA (z := z))
      * cfcHom hU (cayleyDenomInvCM hA hz) = 1 := by
    rw [← map_mul, hprod, map_one]
  -- the first resolvent identity, in operator form
  have hVid : resolvent A hzr * ((1 : H →L[ℂ] H) - (z + Complex.I) • resolvent A hni)
      = resolvent A hni := by
    refine ContinuousLinearMap.ext fun φ => ?_
    have h := resolvent_sub_resolvent hzr hni φ
    have hz' : z - -Complex.I = z + Complex.I := by ring
    rw [hz'] at h
    simp only [_root_.mul_apply_eq_comp, _root_.sub_apply, one_apply_eq_self,
      _root_.smul_apply, map_sub, map_smul]
    linear_combination (norm := module) h
  -- combine
  have hR : resolvent A hzr
      = resolvent A hni * cfcHom hU (cayleyDenomInvCM hA hz) := by
    rw [← hVid, one_sub_smul_resolvent_eq_cfcHom hA (z := z), mul_assoc, hinv, mul_one]
  rw [hR, resolvent_negI_eq_cfcHom hA, ← map_mul]
  congr 1
  ext w
  have hne := cayleyDenom_ne_zero hA hz w
  simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, cayleyCoord_apply, cayleyDenomInvCM_apply,
    resolventSymbol_apply, smul_eq_mul]
  field_simp

end ResolventFormula

end LinearPMap
end TauCeti
