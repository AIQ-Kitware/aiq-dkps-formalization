/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent
public import ForTauCeti.Analysis.InnerProductSpace.OneParameterUnitaryGroup.Basic

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

/-- On the unit circle away from `1`, the inverse Cayley map is real. -/
theorem inverseCayley_im_eq_zero {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) :
    (Complex.I * (1 + w) / (1 - w)).im = 0 := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hd : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hmul : w * (starRingEnd ℂ) w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
    norm_num
  have hconj : (starRingEnd ℂ) w = w⁻¹ := by
    field_simp
    linear_combination hmul
  rw [← Complex.conj_eq_iff_im, map_div₀, map_mul, Complex.conj_I, map_add, map_one,
    map_sub, map_one, hconj]
  field_simp
  ring

include hz in
/-- **The resolvent formula** — the property that characterises the spectral
measure. -/
theorem spectralPVM_resolvent_formula (hzr : z ∈ resolventSet A) (ξ : H) :
    ⟪ξ, resolvent A hzr ξ⟫_ℂ
      = ∫ s, ((s : ℂ) - z)⁻¹ ∂((spectralPVM hA).diag ξ) := by
  set hU := isStarNormal_cayley hA with hhU
  have hlhs : ⟪ξ, resolvent A hzr ξ⟫_ℂ
      = ∫ w, resolventSymbol hA hz w ∂(BorelCalculus.diagMeasure hU ξ) := by
    rw [resolvent_eq_cfcHom hA hz hzr, BorelCalculus.integral_diagMeasure]
  have hdiag : (spectralPVM hA).diag ξ
      = Measure.map (cayleyInv hA) (BorelCalculus.diagMeasure hU ξ) := rfl
  have hne : ∀ s : ℝ, (s : ℂ) - z ≠ 0 := by
    intro s hc
    exact hz (by simpa using congrArg Complex.im (sub_eq_zero.mp hc).symm)
  have hcont : Continuous (fun s : ℝ => ((s : ℂ) - z)⁻¹) :=
    Continuous.inv₀ (by fun_prop) hne
  rw [hlhs, hdiag, integral_map (measurable_cayleyInv hA).aemeasurable
    hcont.aestronglyMeasurable]
  refine integral_congr_ae ?_
  have hnull := diagMeasure_cayley_preimage_one hA ξ
  have hae : ∀ᵐ w ∂(BorelCalculus.diagMeasure hU ξ),
      w ∉ ((Subtype.val : _root_.spectrum ℂ (cayley hA) → ℂ) ⁻¹' {1}) :=
    MeasureTheory.compl_mem_ae_iff.mpr hnull
  filter_upwards [hae] with w hw
  have hw1 : (w : ℂ) ≠ 1 := hw
  have hnorm : ‖(w : ℂ)‖ = 1 :=
    spectrum.norm_eq_one_of_unitary (cayley_mem_unitary hA) w.2
  have hd : (1 : ℂ) - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hden := cayleyDenom_ne_zero hA hz w
  have hcast : ((cayleyInv hA w : ℝ) : ℂ) = Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ)) :=
    Complex.ext rfl (by simpa using (inverseCayley_im_eq_zero hnorm hw1).symm)
  have key : Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ)) - z
      = ((Complex.I - z) + (Complex.I + z) * (w : ℂ)) / (1 - (w : ℂ)) := by
    field_simp
    ring
  rw [resolventSymbol_apply, hcast, key, inv_div]

end ResolventFormula

section Restriction

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The spectral projection of an unbounded self-adjoint operator onto a Borel
set of the real line. -/
noncomputable def specProjection (B : Set ℝ) (hB : MeasurableSet B) : H →L[ℂ] H :=
  (spectralPVM hA).proj B hB

/-- The resolvent at `-i` as an image of the Borel calculus of the Cayley
transform — the bridge that makes spectral projections commute with it. -/
theorem resolvent_negI_eq_borelCalculus
    (hs : BorelCalculus.IsBddMeasurable
      (fun w => ((2 * Complex.I)⁻¹ • (1 - cayleyCoord hA)) w)) :
    resolvent A (negI_mem_resolventSet hA)
      = BorelCalculus.borelCalculus (isStarNormal_cayley hA) hs := by
  rw [BorelCalculus.borelCalculus_of_continuous, resolvent_negI_eq_cfcHom hA]

/-- **Spectral projections commute with the resolvent.** -/
theorem specProjection_comm_resolvent (B : Set ℝ) (hB : MeasurableSet B) :
    specProjection hA B hB * resolvent A (negI_mem_resolventSet hA)
      = resolvent A (negI_mem_resolventSet hA) * specProjection hA B hB := by
  have hs : BorelCalculus.IsBddMeasurable
      (fun w => ((2 * Complex.I)⁻¹ • (1 - cayleyCoord hA)) w) :=
    BorelCalculus.IsBddMeasurable.of_continuous _
  rw [resolvent_negI_eq_borelCalculus hA hs, specProjection, spectralPVM,
    BorelCalculus.toProjValMeasure_proj, BorelCalculus.specProj]
  exact BorelCalculus.borelCalculus_comm _ _ _

/-- Pointwise form: `P (R φ) = R (P φ)`. -/
theorem specProjection_resolvent_apply (B : Set ℝ) (hB : MeasurableSet B) (φ : H) :
    specProjection hA B hB (resolvent A (negI_mem_resolventSet hA) φ)
      = resolvent A (negI_mem_resolventSet hA) (specProjection hA B hB φ) := by
  have h := congrArg (fun T : H →L[ℂ] H => T φ) (specProjection_comm_resolvent hA B hB)
  simpa only [_root_.mul_apply_eq_comp] using h

/-- Every vector of the domain is a resolvent image. -/
theorem exists_resolvent_eq_of_mem_domain (x : A.domain) :
    resolvent A (negI_mem_resolventSet hA) (A x - (-Complex.I) • (x : H)) = (x : H) :=
  resolvent_apply_sub_smul (negI_mem_resolventSet hA) x

/-- **Spectral projections preserve the domain.** -/
theorem specProjection_mem_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    specProjection hA B hB (x : H) ∈ A.domain := by
  have hx := exists_resolvent_eq_of_mem_domain hA x
  rw [← hx, specProjection_resolvent_apply]
  exact resolvent_mem_domain (negI_mem_resolventSet hA) _

/-- **Spectral projections intertwine the operator.** -/
theorem specProjection_apply_domain (B : Set ℝ) (hB : MeasurableSet B) (x : A.domain) :
    A ⟨specProjection hA B hB (x : H), specProjection_mem_domain hA B hB x⟩
      = specProjection hA B hB (A x) := by
  set hni := negI_mem_resolventSet hA with hhni
  set P := specProjection hA B hB with hP
  set φ : H := A x - (-Complex.I) • (x : H) with hφ
  have hx : resolvent A hni φ = (x : H) := exists_resolvent_eq_of_mem_domain hA x
  -- `P x` is the resolvent image of `P φ`
  have hPx : resolvent A hni (P φ) = P (x : H) := by
    rw [← hx, specProjection_resolvent_apply]
  have hsolve := sub_smul_resolvent hni (P φ)
  have hcongr : (⟨resolvent A hni (P φ), resolvent_mem_domain hni (P φ)⟩ : A.domain)
      = ⟨P (x : H), specProjection_mem_domain hA B hB x⟩ := Subtype.ext hPx
  rw [hcongr, hPx] at hsolve
  -- and `P φ = P (A x) + i • P x`
  have hPφ : P φ = P (A x) - (-Complex.I) • P (x : H) := by
    rw [hφ, map_sub, map_smul]
  rw [hPφ] at hsolve
  linear_combination (norm := module) hsolve

/-- Spectral projections commute with the resolvent at **every** non-real
point, not just at `-i`. -/
theorem specProjection_comm_resolvent' {z : ℂ} (hz : z.im ≠ 0) (hzr : z ∈ resolventSet A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    specProjection hA B hB * resolvent A hzr
      = resolvent A hzr * specProjection hA B hB := by
  have hs : BorelCalculus.IsBddMeasurable (fun w => resolventSymbol hA hz w) :=
    BorelCalculus.IsBddMeasurable.of_continuous _
  have hR : resolvent A hzr = BorelCalculus.borelCalculus (isStarNormal_cayley hA) hs := by
    rw [BorelCalculus.borelCalculus_of_continuous, resolvent_eq_cfcHom hA hz hzr]
  rw [hR, specProjection, spectralPVM, BorelCalculus.toProjValMeasure_proj,
    BorelCalculus.specProj]
  exact BorelCalculus.borelCalculus_comm _ _ _

theorem specProjection_resolvent_apply' {z : ℂ} (hz : z.im ≠ 0) (hzr : z ∈ resolventSet A)
    (B : Set ℝ) (hB : MeasurableSet B) (φ : H) :
    specProjection hA B hB (resolvent A hzr φ)
      = resolvent A hzr (specProjection hA B hB φ) := by
  have h := congrArg (fun T : H →L[ℂ] H => T φ)
    (specProjection_comm_resolvent' hA hz hzr B hB)
  simpa only [_root_.mul_apply_eq_comp] using h

theorem isIdempotentElem_specProjection (B : Set ℝ) (hB : MeasurableSet B) :
    IsIdempotentElem (specProjection hA B hB) :=
  (spectralPVM hA).proj_idem B hB

theorem isSelfAdjoint_specProjection (B : Set ℝ) (hB : MeasurableSet B) :
    IsSelfAdjoint (specProjection hA B hB) :=
  (spectralPVM hA).isSelfAdjoint_proj B hB

end Restriction

section Reduce

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B)

/-- The **spectral range** of `A` over a Borel set: the range of the spectral
projection, a closed, orthogonally complemented subspace. -/
noncomputable def specRange : Submodule ℂ H := (specProjection hA B hB).range

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

noncomputable instance instCompleteSpace_specRange : CompleteSpace (specRange hA B hB) := by
  change CompleteSpace (specProjection hA B hB).range
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (isIdempotentElem_specProjection hA B hB)).completeSpace_coe

noncomputable instance instHasOrthogonalProjection_specRange :
    (specRange hA B hB).HasOrthogonalProjection := by
  change (specProjection hA B hB).range.HasOrthogonalProjection
  exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (isIdempotentElem_specProjection hA B hB)

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

/-- **The restriction of a self-adjoint operator to one of its spectral
ranges.** -/
noncomputable def specRestrict : specRange hA B hB →ₗ.[ℂ] specRange hA B hB where
  domain := A.domain.comap (specRange hA B hB).subtype
  toFun :=
    { toFun := fun x =>
        ⟨A ⟨((x : specRange hA B hB) : H), x.2⟩,
          apply_mem_specRange hA B hB (x : specRange hA B hB).2⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change (A ⟨_, (x + y).2⟩ : H) = ((A ⟨_, x.2⟩ : H) + (A ⟨_, y.2⟩ : H))
        rw [← _root_.LinearPMap.map_add]
        exact congrArg _ (Subtype.ext rfl)
      map_smul' := fun c x => by
        apply Subtype.ext
        change (A ⟨_, (c • x).2⟩ : H) = (c • (A ⟨_, x.2⟩ : H))
        rw [← _root_.LinearPMap.map_smul]
        exact congrArg _ (Subtype.ext rfl) }

@[simp] theorem specRestrict_domain :
    (specRestrict hA B hB).domain = A.domain.comap (specRange hA B hB).subtype := rfl

@[simp] theorem specRestrict_apply (x : (specRestrict hA B hB).domain) :
    ((specRestrict hA B hB x : specRange hA B hB) : H)
      = A ⟨((x : specRange hA B hB) : H), x.2⟩ := rfl

theorem isFormalAdjoint_specRestrict :
    (specRestrict hA B hB).IsFormalAdjoint (specRestrict hA B hB) := by
  intro x y
  have hsym : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  have := hsym ⟨((x : specRange hA B hB) : H), x.2⟩ ⟨((y : specRange hA B hB) : H), y.2⟩
  simpa only [Submodule.coe_inner, specRestrict_apply] using this

/-- Every vector of the spectral range is a resolvent image *inside* the
range. -/
theorem exists_specRestrict_resolvent {z : ℂ} (hz : z.im ≠ 0) (hzr : z ∈ resolventSet A)
    (φ : specRange hA B hB) :
    ∃ ψ : (specRestrict hA B hB).domain,
      (specRestrict hA B hB ψ : specRange hA B hB) - z • (ψ : specRange hA B hB) = φ := by
  set x : H := resolvent A hzr (φ : H) with hx
  have hxK : x ∈ specRange hA B hB := by
    rw [mem_specRange_iff, hx, specProjection_resolvent_apply' hA hz hzr]
    congr 1
    exact (mem_specRange_iff hA B hB _).mp φ.2
  have hxdom : x ∈ A.domain := resolvent_mem_domain hzr (φ : H)
  refine ⟨⟨⟨x, hxK⟩, hxdom⟩, ?_⟩
  apply Subtype.ext
  have h := sub_smul_resolvent hzr (φ : H)
  simpa only [Submodule.coe_sub, Submodule.coe_smul, specRestrict_apply] using h

theorem dense_specRestrict_domain :
    Dense (((specRestrict hA B hB).domain : Submodule ℂ (specRange hA B hB)) :
      Set (specRange hA B hB)) := by
  rw [Metric.dense_iff]
  rintro φ ε hε
  obtain ⟨y, hy, hyd⟩ := Metric.dense_iff.mp hA.dense_domain (φ : H) ε hε
  have hyK : specProjection hA B hB y ∈ specRange hA B hB := ⟨y, rfl⟩
  have hydom : specProjection hA B hB y ∈ A.domain :=
    specProjection_mem_domain hA B hB ⟨y, hyd⟩
  refine ⟨⟨specProjection hA B hB y, hyK⟩, ?_, hydom⟩
  have hfix : specProjection hA B hB (φ : H) = (φ : H) :=
    (mem_specRange_iff hA B hB _).mp φ.2
  have hnorm : ‖specProjection hA B hB y - (φ : H)‖ ≤ ‖y - (φ : H)‖ := by
    conv_lhs => rw [← hfix]
    rw [← map_sub]
    exact (spectralPVM hA).norm_proj_apply_le B hB _
  have hdist : dist (⟨specProjection hA B hB y, hyK⟩ : specRange hA B hB) φ
      = ‖specProjection hA B hB y - (φ : H)‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
  rw [Metric.mem_ball, hdist]
  have hy' : ‖y - (φ : H)‖ < ε := by
    rw [← dist_eq_norm]; exact hy
  linarith

/-- **The restriction of a self-adjoint operator to a spectral range is
self-adjoint.**  Symmetry is inherited; the two surjectivities come from the
resolvent, which preserves the range because it commutes with the projection. -/
theorem isSelfAdjoint_specRestrict : IsSelfAdjoint (specRestrict hA B hB) := by
  refine TauCeti.OneParameterUnitaryGroup.isSelfAdjoint_of_surjective_addSub _
    (isFormalAdjoint_specRestrict hA B hB) (dense_specRestrict_domain hA B hB) ?_ ?_
  · intro φ
    obtain ⟨ψ, hψ⟩ := exists_specRestrict_resolvent hA B hB (z := -Complex.I) (by simp)
      (negI_mem_resolventSet hA) φ
    exact ⟨ψ, by simpa using hψ⟩
  · intro φ
    obtain ⟨ψ, hψ⟩ := exists_specRestrict_resolvent hA B hB (z := Complex.I) (by simp)
      (I_mem_resolventSet hA) φ
    exact ⟨ψ, hψ⟩

end Reduce

section BoundedSet

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- Off the Cayley singularity, `κ(w) + i = 2i/(1 - w)`. -/
theorem cayleyInv_add_I {w : _root_.spectrum ℂ (cayley hA)} (hw1 : (w : ℂ) ≠ 1) :
    ((cayleyInv hA w : ℝ) : ℂ) + Complex.I = (2 * Complex.I) / (1 - (w : ℂ)) := by
  have hnorm : ‖(w : ℂ)‖ = 1 :=
    spectrum.norm_eq_one_of_unitary (cayley_mem_unitary hA) w.2
  have hd : (1 : ℂ) - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hcast : ((cayleyInv hA w : ℝ) : ℂ) = Complex.I * (1 + (w : ℂ)) / (1 - (w : ℂ)) :=
    Complex.ext rfl (by simpa using (inverseCayley_im_eq_zero hnorm hw1).symm)
  rw [hcast]
  field_simp
  ring

variable (B : Set ℝ) (hB : MeasurableSet B)

/-- The symbol `(κ - c) · 1_B` of the shifted bounded truncation. -/
noncomputable def truncSymbol (c : ℝ) : _root_.spectrum ℂ (cayley hA) → ℂ :=
  fun w => ((cayleyInv hA w : ℂ) - (c : ℂ)) *
    (cayleyInv hA ⁻¹' B).indicator (fun _ => (1 : ℂ)) w

theorem norm_truncSymbol_le {c r : ℝ} (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r)
    (w : _root_.spectrum ℂ (cayley hA)) : ‖truncSymbol hA B c w‖ ≤ r := by
  by_cases hw : w ∈ cayleyInv hA ⁻¹' B
  · have hκB : cayleyInv hA w ∈ B := hw
    have h2 : (cayleyInv hA ⁻¹' B).indicator (fun _ => (1 : ℂ)) w = 1 := by simp [hw]
    rw [truncSymbol]
    simp only [h2, mul_one]
    rw [show ((cayleyInv hA w : ℂ) - (c : ℂ)) = ((cayleyInv hA w - c : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    exact hcr _ hκB
  · have h2 : (cayleyInv hA ⁻¹' B).indicator (fun _ => (1 : ℂ)) w = 0 := by simp [hw]
    rw [truncSymbol]
    simp only [h2, mul_zero, norm_zero]
    exact hr

include hB in
theorem isBddMeasurable_truncSymbol {c r : ℝ} (hr : 0 ≤ r)
    (hcr : ∀ s ∈ B, |s - c| ≤ r) :
    BorelCalculus.IsBddMeasurable (truncSymbol hA B c) := by
  have hmeasκ : Measurable fun w => ((cayleyInv hA w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (measurable_cayleyInv hA)
  have hSm : MeasurableSet (cayleyInv hA ⁻¹' B) := measurable_cayleyInv hA hB
  exact ⟨(hmeasκ.sub measurable_const).mul (measurable_const.indicator hSm), r, hr,
    norm_truncSymbol_le hA B hr hcr⟩

/-- **Bounded spectral sets.**  If the spectral parameter stays within `r` of `c`
on `B`, then the spectral projection lands in `dom A` and `A - c` is bounded by
`r` there.  Both facts come from one identity: `(A + i) E_A(B)` is the Borel
calculus of `(κ + i) 1_B`, because the resolvent's symbol `(1-w)/(2i)` is the
pointwise inverse of `κ + i` away from the Cayley singularity. -/
theorem specProjection_apply_sub_smul {M c r : ℝ}
    (hbnd : ∀ s ∈ B, |s| ≤ M) (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) (y : H) :
    ∃ hy : specProjection hA B hB y ∈ A.domain,
      A ⟨specProjection hA B hB y, hy⟩ - (c : ℂ) • specProjection hA B hB y
        = BorelCalculus.borelCalculus (isStarNormal_cayley hA)
            (isBddMeasurable_truncSymbol hA B hB hr hcr) y := by
  classical
  set hU := isStarNormal_cayley hA with hhU
  set hni := negI_mem_resolventSet hA with hhni
  set κ := cayleyInv hA with hκ
  set S : Set (_root_.spectrum ℂ (cayley hA)) := κ ⁻¹' B with hS
  have hSm : MeasurableSet S := measurable_cayleyInv hA hB
  set ind : _root_.spectrum ℂ (cayley hA) → ℂ := S.indicator (fun _ => 1) with hind
  have hindb : BorelCalculus.IsBddMeasurable ind :=
    BorelCalculus.isBddMeasurable_indicator (a := cayley hA) hSm
  have hmeasκ : Measurable fun w => ((κ w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (measurable_cayleyInv hA)
  set q : _root_.spectrum ℂ (cayley hA) → ℂ :=
    fun w => ((κ w : ℂ) + Complex.I) * ind w with hq
  set pf : _root_.spectrum ℂ (cayley hA) → ℂ :=
    fun w => ((κ w : ℂ) - (c : ℂ)) * ind w with hpf
  have hqb : BorelCalculus.IsBddMeasurable q := by
    refine ⟨(hmeasκ.add measurable_const).mul hindb.measurable, max 0 M + 1,
      by positivity, fun w => ?_⟩
    by_cases hw : w ∈ S
    · have hκB : κ w ∈ B := hw
      have h1 : ‖((κ w : ℂ) + Complex.I)‖ ≤ max 0 M + 1 := by
        refine le_trans (norm_add_le _ _) ?_
        rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
        have := hbnd _ hκB
        have := le_max_right 0 M
        linarith
      have h2 : ind w = 1 := by simp [hind, hw]
      rw [hq]; simp only [h2, mul_one]; exact h1
    · have h2 : ind w = 0 := by simp [hind, hw]
      rw [hq]; simp only [h2, mul_zero, norm_zero]; positivity
  have hpb : BorelCalculus.IsBddMeasurable pf := by
    refine ⟨(hmeasκ.sub measurable_const).mul hindb.measurable, r, hr, fun w => ?_⟩
    by_cases hw : w ∈ S
    · have hκB : κ w ∈ B := hw
      have h2 : ind w = 1 := by simp [hind, hw]
      rw [hpf]; simp only [h2, mul_one]
      rw [show ((κ w : ℂ) - (c : ℂ)) = ((κ w - c : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact hcr _ hκB
    · have h2 : ind w = 0 := by simp [hind, hw]
      rw [hpf]; simp only [h2, mul_zero, norm_zero]; exact hr
  -- the resolvent as a Borel-calculus image
  set gsym : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
    (2 * Complex.I)⁻¹ • (1 - cayleyCoord hA) with hgsym
  have hgb : BorelCalculus.IsBddMeasurable (fun w => gsym w) :=
    BorelCalculus.IsBddMeasurable.of_continuous gsym
  have hRg : resolvent A hni = BorelCalculus.borelCalculus hU hgb :=
    resolvent_negI_eq_borelCalculus hA hgb
  -- the product symbol is the indicator, off the Cayley singularity
  have hprod : BorelCalculus.borelCalculus hU (hgb.mul hqb)
      = BorelCalculus.borelCalculus hU hindb := by
    refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η => ?_
    have hae : ∀ᵐ w ∂(BorelCalculus.diagMeasure hU η),
        w ∉ ((Subtype.val : _root_.spectrum ℂ (cayley hA) → ℂ) ⁻¹' {1}) :=
      MeasureTheory.compl_mem_ae_iff.mpr (diagMeasure_cayley_preimage_one hA η)
    filter_upwards [hae] with w hw
    have hw1 : (w : ℂ) ≠ 1 := hw
    have hd : (1 : ℂ) - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
    have hgval : gsym w = (2 * Complex.I)⁻¹ * (1 - (w : ℂ)) := rfl
    have hκval : ((κ w : ℝ) : ℂ) + Complex.I = (2 * Complex.I) / (1 - (w : ℂ)) :=
      cayleyInv_add_I hA hw1
    change gsym w * q w = ind w
    have hqw : q w = ((κ w : ℂ) + Complex.I) * ind w := rfl
    rw [hgval, hqw, hκval]
    field_simp
  -- the shifted symbol is the difference of the two Borel-calculus images
  have hpfb : ∀ w, ‖pf w‖ ≤ r := by
    intro w
    by_cases hw : w ∈ S
    · have hκB : κ w ∈ B := hw
      have h2 : ind w = 1 := by simp [hind, hw]
      rw [hpf]; simp only [h2, mul_one]
      rw [show ((κ w : ℂ) - (c : ℂ)) = ((κ w - c : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact hcr _ hκB
    · have h2 : ind w = 0 := by simp [hind, hw]
      rw [hpf]; simp only [h2, mul_zero, norm_zero]; exact hr
  set hsm := hindb.const_smul (-(Complex.I + (c : ℂ))) with hhsm
  have heq : BorelCalculus.borelCalculus hU hpb
      = BorelCalculus.borelCalculus hU (hqb.add hsm) := by
    refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η =>
      Filter.Eventually.of_forall fun w => ?_
    change pf w = q w + -(Complex.I + (c : ℂ)) * ind w
    rw [hpf, hq]; ring
  -- hence `(A + i) E(B)` is the Borel calculus of `(κ + i) 1_B`
  set T := BorelCalculus.borelCalculus hU hqb with hT
  have hPy : resolvent A hni (T y) = specProjection hA B hB y := by
    have h := congrArg (fun L : H →L[ℂ] H => L y)
      ((BorelCalculus.borelCalculus_mul hU hgb hqb).symm.trans hprod)
    simp only [_root_.mul_apply_eq_comp] at h
    rw [hRg]
    exact h
  have hy : specProjection hA B hB y ∈ A.domain := by
    rw [← hPy]; exact resolvent_mem_domain hni (T y)
  refine ⟨hy, ?_⟩
  -- solve for `A` on the range
  have hsolve := sub_smul_resolvent hni (T y)
  have hcongr : (⟨resolvent A hni (T y), resolvent_mem_domain hni (T y)⟩ : A.domain)
      = ⟨specProjection hA B hB y, hy⟩ := Subtype.ext hPy
  rw [hcongr, hPy] at hsolve
  have hval : BorelCalculus.borelCalculus hU hpb y
      = T y - (Complex.I + (c : ℂ)) • specProjection hA B hB y := by
    rw [heq, BorelCalculus.borelCalculus_add hU hqb hsm,
      BorelCalculus.borelCalculus_const_smul hU (-(Complex.I + (c : ℂ))) hindb]
    simp only [_root_.add_apply, _root_.smul_apply, hT]
    rw [neg_smul, ← sub_eq_add_neg]
    rfl
  have hgoal : A ⟨specProjection hA B hB y, hy⟩ - (c : ℂ) • specProjection hA B hB y
      = BorelCalculus.borelCalculus hU hpb y := by
    rw [hval]
    linear_combination (norm := module) hsolve
  exact hgoal

/-- A bounded spectral range lies inside the operator domain. -/
theorem mem_domain_of_mem_specRange_of_bounded {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M)
    {x : H} (hx : x ∈ specRange hA B hB) : x ∈ A.domain := by
  have hfix : specProjection hA B hB x = x := (mem_specRange_iff hA B hB x).mp hx
  obtain ⟨hy, -⟩ := specProjection_apply_sub_smul hA B hB hbnd
    (c := 0) (r := max 0 M) (le_max_left 0 M)
    (fun s hs => by simpa using le_trans (hbnd s hs) (le_max_right 0 M)) x
  rwa [hfix] at hy

/-- On a spectral range over a set within `r` of `c`, the operator differs from
`c` by at most `r` in norm. -/
theorem norm_sub_smul_le_of_mem_specRange {M c r : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M)
    (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) {x : H} (hx : x ∈ specRange hA B hB)
    (hmem : x ∈ A.domain) :
    ‖A ⟨x, hmem⟩ - (c : ℂ) • x‖ ≤ r * ‖x‖ := by
  have hfix : specProjection hA B hB x = x := (mem_specRange_iff hA B hB x).mp hx
  obtain ⟨hy, hb⟩ := specProjection_apply_sub_smul hA B hB hbnd hr hcr x
  have hsub : (⟨specProjection hA B hB x, hy⟩ : A.domain) = ⟨x, hmem⟩ := Subtype.ext hfix
  rw [hsub, hfix] at hb
  rw [hb]
  exact BorelCalculus.norm_borelCalculus_apply_le _ _ hr
    (norm_truncSymbol_le hA B hr hcr) x

/-- **The interval cutoffs converge strongly to the identity.** -/
theorem tendsto_specProjection_Icc (x : H) :
    Filter.Tendsto
      (fun τ : ℝ => specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x)
      Filter.atTop (nhds x) := by
  classical
  set hU := isStarNormal_cayley hA with hhU
  set μ := BorelCalculus.diagMeasure hU x with hμ
  set κ := cayleyInv hA with hκ
  set F : ℝ → _root_.spectrum ℂ (cayley hA) → ℝ :=
    fun τ => (κ ⁻¹' Set.Icc (-τ) τ).indicator (fun _ => (1 : ℝ)) with hF
  -- the diagonal masses are the indicator integrals
  have hd : ∀ τ : ℝ, (((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal
      = ∫ w, F τ w ∂μ := by
    intro τ
    have hSm : MeasurableSet (κ ⁻¹' Set.Icc (-τ) τ) :=
      measurable_cayleyInv hA measurableSet_Icc
    rw [show ((spectralPVM hA).diag x) = Measure.map κ μ from rfl,
      Measure.map_apply (measurable_cayleyInv hA) measurableSet_Icc, hF,
      integral_indicator_const _ hSm, smul_eq_mul, mul_one,
      MeasureTheory.measureReal_def]
  -- dominated convergence
  have hlim : Filter.Tendsto (fun τ : ℝ => ∫ w, F τ w ∂μ) Filter.atTop
      (nhds (∫ _w, (1 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
      (Filter.Eventually.of_forall fun τ =>
        (measurable_const.indicator
          (measurable_cayleyInv hA measurableSet_Icc)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun τ => Filter.Eventually.of_forall fun w => ?_)
      (integrable_const _)
      (Filter.Eventually.of_forall fun w => ?_)
    · by_cases hw : w ∈ κ ⁻¹' Set.Icc (-τ) τ <;> simp [hF, hw]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop |κ w|] with τ hτ
      have hmem : w ∈ κ ⁻¹' Set.Icc (-τ) τ :=
        ⟨by linarith [neg_abs_le (κ w)], by linarith [le_abs_self (κ w)]⟩
      simp [hF, hmem]
  have htot : ∫ _w, (1 : ℝ) ∂μ = ‖x‖ ^ 2 := by
    rw [integral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def, hμ,
      BorelCalculus.diagMeasure_univ_toReal]
  -- the squared distance is the missing mass
  have hsq : ∀ τ : ℝ,
      ‖specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x - x‖ ^ 2
        = ‖x‖ ^ 2 - (((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal := by
    intro τ
    have hnormP : ‖specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x‖ ^ 2
        = (((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal :=
      (spectralPVM hA).norm_sq_proj_apply _ _ x
    have hinner : ⟪x, specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x⟫_ℂ
        = ((((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal : ℂ) :=
      (spectralPVM hA).inner_proj _ _ x
    have hre : RCLike.re (⟪specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x, x⟫_ℂ)
        = (((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal := by
      rw [← inner_conj_symm, hinner]
      simp
    rw [norm_sub_sq (𝕜 := ℂ), hnormP, hre]
    ring
  -- conclude
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  have hsq' : Filter.Tendsto
      (fun τ : ℝ => ‖specProjection hA (Set.Icc (-τ) τ) measurableSet_Icc x - x‖ ^ 2)
      Filter.atTop (nhds 0) := by
    have hconv : Filter.Tendsto
        (fun τ : ℝ => ‖x‖ ^ 2 - (((spectralPVM hA).diag x) (Set.Icc (-τ) τ)).toReal)
        Filter.atTop (nhds (‖x‖ ^ 2 - ‖x‖ ^ 2)) := by
      refine Filter.Tendsto.sub tendsto_const_nhds ?_
      simpa only [hd, htot] using hlim
    simpa only [hsq, sub_self] using hconv
  have hfin := (Real.continuous_sqrt.tendsto 0).comp hsq'
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hfin

/-- **Form bounds on a spectral range.**  If `B ⊆ [β, α]` then the quadratic
form of `A` on the spectral range of `B` is confined to `[β, α]`. -/
theorem re_inner_apply_bounds_of_subset_Icc {β α : ℝ} (hBsub : B ⊆ Set.Icc β α)
    {y : H} (hyK : y ∈ specRange hA B hB) (hy : y ∈ A.domain) :
    β * ‖y‖ ^ 2 ≤ (⟪A ⟨y, hy⟩, y⟫_ℂ).re ∧ (⟪A ⟨y, hy⟩, y⟫_ℂ).re ≤ α * ‖y‖ ^ 2 := by
  rcases le_or_gt β α with hβα | hβα
  · have hM : ∀ s ∈ B, |s| ≤ max |β| |α| := fun s hs => by
      obtain ⟨h1, h2⟩ := hBsub hs
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h3 := neg_abs_le β
        have h4 := le_max_left |β| |α|
        linarith
      · have h3 := le_abs_self α
        have h4 := le_max_right |β| |α|
        linarith
    have hr : (0 : ℝ) ≤ (α - β) / 2 := by linarith
    have hcr : ∀ s ∈ B, |s - (β + α) / 2| ≤ (α - β) / 2 := fun s hs => by
      obtain ⟨h1, h2⟩ := hBsub hs
      rw [abs_le]
      constructor <;> linarith
    have hbound := norm_sub_smul_le_of_mem_specRange hA B hB hM hr hcr hyK hy
    have hyy : (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have hexp : (⟪A ⟨y, hy⟩ - (((β + α) / 2 : ℝ) : ℂ) • y, y⟫_ℂ).re
        = (⟪A ⟨y, hy⟩, y⟫_ℂ).re - (β + α) / 2 * ‖y‖ ^ 2 := by
      rw [inner_sub_left, inner_smul_left, Complex.sub_re, Complex.conj_ofReal,
        Complex.re_ofReal_mul, hyy]
    have hcs : |(⟪A ⟨y, hy⟩ - (((β + α) / 2 : ℝ) : ℂ) • y, y⟫_ℂ).re|
        ≤ (α - β) / 2 * ‖y‖ ^ 2 := by
      calc |(⟪A ⟨y, hy⟩ - (((β + α) / 2 : ℝ) : ℂ) • y, y⟫_ℂ).re|
          ≤ ‖⟪A ⟨y, hy⟩ - (((β + α) / 2 : ℝ) : ℂ) • y, y⟫_ℂ‖ := Complex.abs_re_le_norm _
        _ ≤ ‖A ⟨y, hy⟩ - (((β + α) / 2 : ℝ) : ℂ) • y‖ * ‖y‖ := norm_inner_le_norm _ _
        _ ≤ ((α - β) / 2 * ‖y‖) * ‖y‖ := by gcongr
        _ = (α - β) / 2 * ‖y‖ ^ 2 := by ring
    rw [hexp, abs_le] at hcs
    constructor <;> nlinarith [hcs.1, hcs.2]
  · -- `Set.Icc β α` is empty, hence so is `B`, hence the spectral range is trivial
    have hIcc : Set.Icc β α = (∅ : Set ℝ) := Set.Icc_eq_empty (not_le.mpr hβα)
    have hBempty : B = (∅ : Set ℝ) := Set.eq_empty_of_subset_empty (hIcc ▸ hBsub)
    have hfix : specProjection hA B hB y = y := (mem_specRange_iff hA B hB y).mp hyK
    have hzero : ‖y‖ ^ 2 = 0 := by
      conv_lhs => rw [← hfix]
      rw [show specProjection hA B hB y = (spectralPVM hA).proj B hB y from rfl,
        (spectralPVM hA).norm_sq_proj_apply, hBempty, measure_empty, ENNReal.toReal_zero]
    have hy0 : y = 0 := norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero)
    subst hy0
    have h0 : (⟨(0 : H), hy⟩ : A.domain) = 0 := Subtype.ext rfl
    rw [h0, _root_.LinearPMap.map_zero]
    simp

/-- **The bounded truncation of `A` to a bounded spectral set** — the Borel
calculus of `κ · 1_B`.  It agrees with `A` on the spectral range. -/
noncomputable def truncation {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) : H →L[ℂ] H :=
  BorelCalculus.borelCalculus (isStarNormal_cayley hA)
    (isBddMeasurable_truncSymbol hA B hB (c := 0) (r := max 0 M) (le_max_left 0 M)
      (fun s hs => by simpa using le_trans (hbnd s hs) (le_max_right 0 M)))

theorem truncation_eq_on_specProjection {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ∃ hy : specProjection hA B hB y ∈ A.domain,
      A ⟨specProjection hA B hB y, hy⟩ = truncation hA B hB hbnd y := by
  obtain ⟨hy, hb⟩ := specProjection_apply_sub_smul hA B hB hbnd (c := 0)
    (r := max 0 M) (le_max_left 0 M)
    (fun s hs => by simpa using le_trans (hbnd s hs) (le_max_right 0 M)) y
  exact ⟨hy, by simpa [truncation] using hb⟩

theorem norm_truncation_apply_le {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) (y : H) :
    ‖truncation hA B hB hbnd y‖ ≤ max 0 M * ‖y‖ :=
  BorelCalculus.norm_borelCalculus_apply_le _ _ (le_max_left 0 M)
    (norm_truncSymbol_le hA B (c := 0) (r := max 0 M) (le_max_left 0 M)
      (fun s hs => by simpa using le_trans (hbnd s hs) (le_max_right 0 M))) y

/-- The truncation is self-adjoint: its symbol is real. -/
theorem isSelfAdjoint_truncation {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M) :
    IsSelfAdjoint (truncation hA B hB hbnd) := by
  have hs := isBddMeasurable_truncSymbol hA B hB (c := 0) (r := max 0 M) (le_max_left 0 M)
    (fun s hs => by simpa using le_trans (hbnd s hs) (le_max_right 0 M))
  have hconj : BorelCalculus.borelCalculus (isStarNormal_cayley hA) hs.conj
      = BorelCalculus.borelCalculus (isStarNormal_cayley hA) hs := by
    refine BorelCalculus.borelCalculus_congr_ae _ _ _ fun η =>
      Filter.Eventually.of_forall fun w => ?_
    change (starRingEnd ℂ) (truncSymbol hA B 0 w) = truncSymbol hA B 0 w
    rw [truncSymbol]
    by_cases hw : w ∈ cayleyInv hA ⁻¹' B <;> simp [hw, Complex.conj_ofReal]
  have hkey : ContinuousLinearMap.adjoint
      (BorelCalculus.borelCalculus (isStarNormal_cayley hA) hs)
      = BorelCalculus.borelCalculus (isStarNormal_cayley hA) hs := by
    rw [← BorelCalculus.borelCalculus_conj (isStarNormal_cayley hA) hs, hconj]
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint]
  exact hkey

/-- The truncation commutes with every spectral projection. -/
theorem truncation_comm_specProjection {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M)
    (C : Set ℝ) (hC : MeasurableSet C) :
    truncation hA B hB hbnd * specProjection hA C hC
      = specProjection hA C hC * truncation hA B hB hbnd := by
  rw [truncation, specProjection, spectralPVM, BorelCalculus.toProjValMeasure_proj,
    BorelCalculus.specProj]
  exact BorelCalculus.borelCalculus_comm _ _ _

end BoundedSet

section ResolventGap

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B)

/-- **A spectral gap gives a resolvent point of the restriction.**  If `B` keeps
its distance `ε` from `lam`, then `lam` is in the resolvent set of the
restriction of `A` to the spectral range of `B`; the inverse is the Borel
calculus of `(κ - lam)⁻¹ 1_B`. -/
theorem mem_resolventSet_specRestrict_of_gap {lam ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ s ∈ B, ε ≤ |s - lam|) :
    (lam : ℂ) ∈ resolventSet (specRestrict hA B hB) := by
  classical
  set hU := isStarNormal_cayley hA with hhU
  set hni := negI_mem_resolventSet hA with hhni
  set κ := cayleyInv hA with hκ
  set S : Set (_root_.spectrum ℂ (cayley hA)) := κ ⁻¹' B with hS
  have hSm : MeasurableSet S := measurable_cayleyInv hA hB
  set ind : _root_.spectrum ℂ (cayley hA) → ℂ := S.indicator (fun _ => (1 : ℂ)) with hind
  have hindb : BorelCalculus.IsBddMeasurable ind :=
    BorelCalculus.isBddMeasurable_indicator (a := cayley hA) hSm
  have hmeasκ : Measurable fun w => ((κ w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.measurable.comp (measurable_cayleyInv hA)
  have hindone : ∀ w ∈ S, ind w = 1 := fun w hw => by simp [hind, hw]
  have hindnil : ∀ w, w ∉ S → ind w = 0 := fun w hw => by simp [hind, hw]
  -- the gap, transported to the spectrum
  have hgapS : ∀ w ∈ S, ε ≤ ‖((κ w : ℂ) - (lam : ℂ))‖ := by
    intro w hw
    have hκB : κ w ∈ B := hw
    rw [show ((κ w : ℂ) - (lam : ℂ)) = ((κ w - lam : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact hgap _ hκB
  have hne : ∀ w ∈ S, ((κ w : ℂ) - (lam : ℂ)) ≠ 0 := by
    intro w hw hzero
    have := hgapS w hw
    rw [hzero, norm_zero] at this
    linarith
  -- the inverting symbol and its `(κ + i)`-companion
  set f : _root_.spectrum ℂ (cayley hA) → ℂ :=
    fun w => ((κ w : ℂ) - (lam : ℂ))⁻¹ * ind w with hf
  set hsym : _root_.spectrum ℂ (cayley hA) → ℂ :=
    fun w => ((κ w : ℂ) + Complex.I) * f w with hhsym
  have hfmeas : Measurable f :=
    ((hmeasκ.sub measurable_const).inv).mul hindb.measurable
  have hfb : BorelCalculus.IsBddMeasurable f := by
    refine ⟨hfmeas, ε⁻¹, by positivity, fun w => ?_⟩
    by_cases hw : w ∈ S
    · rw [hf]
      simp only [hindone w hw, mul_one, norm_inv]
      simpa only [one_div] using one_div_le_one_div_of_le hε (hgapS w hw)
    · rw [hf]
      simp only [hindnil w hw, mul_zero, norm_zero]
      positivity
  have hhb : BorelCalculus.IsBddMeasurable hsym := by
    refine ⟨(hmeasκ.add measurable_const).mul hfmeas, 1 + (|lam| + 1) / ε,
      by positivity, fun w => ?_⟩
    by_cases hw : w ∈ S
    · have hgw := hgapS w hw
      have hpos : 0 < ‖((κ w : ℂ) - (lam : ℂ))‖ := lt_of_lt_of_le hε hgw
      have hb1 : ‖((κ w : ℂ) + Complex.I)‖
          ≤ ‖((κ w : ℂ) - (lam : ℂ))‖ + (|lam| + 1) := by
        have hsplit : ((κ w : ℂ) + Complex.I)
            = ((κ w : ℂ) - (lam : ℂ)) + ((lam : ℂ) + Complex.I) := by ring
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        gcongr
        refine le_trans (norm_add_le _ _) ?_
        rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
      have hfw : ‖f w‖ = (‖((κ w : ℂ) - (lam : ℂ))‖)⁻¹ := by
        rw [hf]
        simp only [hindone w hw, mul_one, norm_inv]
      have hinv : (‖((κ w : ℂ) - (lam : ℂ))‖)⁻¹ ≤ ε⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hε hgw
      rw [hhsym, norm_mul, hfw]
      have hstep : ‖((κ w : ℂ) + Complex.I)‖ * (‖((κ w : ℂ) - (lam : ℂ))‖)⁻¹
          ≤ (‖((κ w : ℂ) - (lam : ℂ))‖ + (|lam| + 1))
              * (‖((κ w : ℂ) - (lam : ℂ))‖)⁻¹ := by
        gcongr
      have hexp : (‖((κ w : ℂ) - (lam : ℂ))‖ + (|lam| + 1))
          * (‖((κ w : ℂ) - (lam : ℂ))‖)⁻¹
          = 1 + (|lam| + 1) * (‖((κ w : ℂ) - (lam : ℂ))‖)⁻¹ := by
        rw [add_mul, mul_inv_cancel₀ (ne_of_gt hpos)]
      have hlast : (|lam| + 1) * (‖((κ w : ℂ) - (lam : ℂ))‖)⁻¹
          ≤ (|lam| + 1) / ε := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      linarith
    · have hfz : f w = 0 := by rw [hf]; simp [hindnil w hw]
      change ‖((κ w : ℂ) + Complex.I) * f w‖ ≤ 1 + (|lam| + 1) / ε
      rw [hfz, mul_zero, norm_zero]
      positivity
  -- the resolvent as a Borel-calculus image, and `g = (κ + i)⁻¹` almost everywhere
  set gsym : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
    (2 * Complex.I)⁻¹ • (1 - cayleyCoord hA) with hgsym
  have hgb : BorelCalculus.IsBddMeasurable (fun w => gsym w) :=
    BorelCalculus.IsBddMeasurable.of_continuous gsym
  have hRg : resolvent A hni = BorelCalculus.borelCalculus hU hgb :=
    resolvent_negI_eq_borelCalculus hA hgb
  have hgae : ∀ η : H, ∀ᵐ w ∂(BorelCalculus.diagMeasure hU η),
      gsym w * ((κ w : ℂ) + Complex.I) = 1 := by
    intro η
    have hae := MeasureTheory.compl_mem_ae_iff.mpr (diagMeasure_cayley_preimage_one hA η)
    filter_upwards [hae] with w hw
    have hw1 : (w : ℂ) ≠ 1 := hw
    have hd : (1 : ℂ) - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
    have hgval : gsym w = (2 * Complex.I)⁻¹ * (1 - (w : ℂ)) := rfl
    rw [hgval, cayleyInv_add_I hA hw1]
    field_simp
  -- `R(-i) ∘ T_hsym = T_f`
  have hcomp : BorelCalculus.borelCalculus hU (hgb.mul hhb)
      = BorelCalculus.borelCalculus hU hfb := by
    refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η => ?_
    filter_upwards [hgae η] with w hw
    change gsym w * (((κ w : ℂ) + Complex.I) * f w) = f w
    rw [← mul_assoc, hw, one_mul]
  set Rop := BorelCalculus.borelCalculus hU hfb with hRop
  have hRopdom : ∀ φ : H,
      Rop φ = resolvent A hni (BorelCalculus.borelCalculus hU hhb φ) := by
    intro φ
    have hx := congrArg (fun L : H →L[ℂ] H => L φ)
      ((BorelCalculus.borelCalculus_mul hU hgb hhb).symm.trans hcomp)
    simp only [_root_.mul_apply_eq_comp] at hx
    rw [hRg]
    exact hx.symm
  have hmemdom : ∀ φ : H, Rop φ ∈ A.domain := by
    intro φ
    rw [hRopdom φ]
    exact resolvent_mem_domain hni _
  have hAeq : ∀ φ : H, A ⟨Rop φ, hmemdom φ⟩
      = BorelCalculus.borelCalculus hU hhb φ - Complex.I • Rop φ := by
    intro φ
    have hsolve := sub_smul_resolvent hni (BorelCalculus.borelCalculus hU hhb φ)
    have hcongr : (⟨resolvent A hni (BorelCalculus.borelCalculus hU hhb φ),
        resolvent_mem_domain hni _⟩ : A.domain) = ⟨Rop φ, hmemdom φ⟩ :=
      Subtype.ext (hRopdom φ).symm
    rw [hcongr, ← hRopdom φ] at hsolve
    linear_combination (norm := module) hsolve
  -- `(A - lam) T_f = E(B)`
  set hsm2 := hfb.const_smul (-(Complex.I + (lam : ℂ))) with hhsm2
  have hidsym : BorelCalculus.borelCalculus hU hindb
      = BorelCalculus.borelCalculus hU (hhb.add hsm2) := by
    refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η =>
      Filter.Eventually.of_forall fun w => ?_
    change ind w
      = ((κ w : ℂ) + Complex.I) * f w + -(Complex.I + (lam : ℂ)) * f w
    by_cases hw : w ∈ S
    · have hfw : f w = ((κ w : ℂ) - (lam : ℂ))⁻¹ := by
        rw [hf]; simp [hindone w hw]
      rw [hindone w hw, hfw]
      field_simp [hne w hw]
      ring
    · have hfz : f w = 0 := by rw [hf]; simp [hindnil w hw]
      rw [hindnil w hw, hfz]
      ring
  have hright : ∀ φ : H, A ⟨Rop φ, hmemdom φ⟩ - (lam : ℂ) • Rop φ
      = BorelCalculus.borelCalculus hU hindb φ := by
    intro φ
    rw [hAeq φ, hidsym, BorelCalculus.borelCalculus_add hU hhb hsm2,
      BorelCalculus.borelCalculus_const_smul hU (-(Complex.I + (lam : ℂ))) hfb]
    simp only [_root_.add_apply, _root_.smul_apply, ← hRop]
    module
  -- `T_f` lands in the spectral range
  have hindf : BorelCalculus.borelCalculus hU (hindb.mul hfb)
      = BorelCalculus.borelCalculus hU hfb := by
    refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η =>
      Filter.Eventually.of_forall fun w => ?_
    change ind w * f w = f w
    by_cases hw : w ∈ S
    · rw [hindone w hw, one_mul]
    · have hfz : f w = 0 := by rw [hf]; simp [hindnil w hw]
      rw [hfz, mul_zero]
  have hKmap : ∀ φ : H, Rop φ ∈ specRange hA B hB := by
    intro φ
    have hx := congrArg (fun L : H →L[ℂ] H => L φ)
      ((BorelCalculus.borelCalculus_mul hU hindb hfb).symm.trans hindf)
    simp only [_root_.mul_apply_eq_comp] at hx
    exact ⟨Rop φ, hx⟩
  -- the left inverse
  have hkne : ∀ w : _root_.spectrum ℂ (cayley hA), ((κ w : ℂ) + Complex.I) ≠ 0 := by
    intro w h0
    have him := congrArg Complex.im h0
    simp at him
  have hlefts : BorelCalculus.borelCalculus hU
        (hfb.add ((hfb.mul hgb).const_smul (-(Complex.I + (lam : ℂ)))))
      = BorelCalculus.borelCalculus hU (hindb.mul hgb) := by
    refine BorelCalculus.borelCalculus_congr_ae hU _ _ fun η => ?_
    filter_upwards [hgae η] with w hw
    have hgval : gsym w = ((κ w : ℂ) + Complex.I)⁻¹ := by
      field_simp [hkne w]
      linear_combination hw
    by_cases hwS : w ∈ S
    · have hfw : f w = ((κ w : ℂ) - (lam : ℂ))⁻¹ := by
        rw [hf]; simp [hindone w hwS]
      rw [hindone w hwS, hfw, hgval, one_mul]
      field_simp [hne w hwS, hkne w]
      ring
    · have hfz : f w = 0 := by rw [hf]; simp [hindnil w hwS]
      rw [hindnil w hwS, hfz]
      ring
  have hlefts' : Rop + (-(Complex.I + (lam : ℂ)))
        • (Rop * BorelCalculus.borelCalculus hU hgb)
      = BorelCalculus.borelCalculus hU hindb * BorelCalculus.borelCalculus hU hgb := by
    rw [← BorelCalculus.borelCalculus_mul hU hfb hgb,
      ← BorelCalculus.borelCalculus_const_smul hU (-(Complex.I + (lam : ℂ))) (hfb.mul hgb),
      hRop, ← BorelCalculus.borelCalculus_add hU hfb ((hfb.mul hgb).const_smul _),
      ← BorelCalculus.borelCalculus_mul hU hindb hgb]
    exact hlefts
  refine ⟨Rop.restrict (fun x _ => hKmap x), ?_, ?_⟩
  · intro ψ
    apply Subtype.ext
    have hyK : ((ψ : specRange hA B hB) : H) ∈ specRange hA B hB :=
      (ψ : specRange hA B hB).2
    have hydom : ((ψ : specRange hA B hB) : H) ∈ A.domain := ψ.2
    change Rop (A ⟨((ψ : specRange hA B hB) : H), hydom⟩
        - (lam : ℂ) • ((ψ : specRange hA B hB) : H)) = ((ψ : specRange hA B hB) : H)
    set y : H := ((ψ : specRange hA B hB) : H) with hy
    set φ₀ : H := A ⟨y, hydom⟩ - (-Complex.I) • y with hφ₀
    have hy0 : resolvent A hni φ₀ = y := resolvent_apply_sub_smul hni ⟨y, hydom⟩
    have hsplit : A ⟨y, hydom⟩ - (lam : ℂ) • y = φ₀ - (Complex.I + (lam : ℂ)) • y := by
      rw [hφ₀]; module
    have hPy : BorelCalculus.borelCalculus hU hindb y = y :=
      (mem_specRange_iff hA B hB y).mp hyK
    have hfin := congrArg (fun L : H →L[ℂ] H => L φ₀) hlefts'
    simp only [_root_.add_apply, _root_.smul_apply, _root_.mul_apply_eq_comp] at hfin
    rw [← hRg, hy0, hPy] at hfin
    rw [hsplit, map_sub, map_smul]
    linear_combination (norm := module) hfin
  · intro φ
    refine ⟨hmemdom ((φ : specRange hA B hB) : H), ?_⟩
    apply Subtype.ext
    change A ⟨Rop ((φ : specRange hA B hB) : H),
        hmemdom ((φ : specRange hA B hB) : H)⟩
        - (lam : ℂ) • Rop ((φ : specRange hA B hB) : H)
        = ((φ : specRange hA B hB) : H)
    rw [hright]
    exact (mem_specRange_iff hA B hB _).mp φ.2

end ResolventGap

end LinearPMap
end TauCeti
