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
# The spectral measure of an unbounded self-adjoint operator: construction

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

This module carries the construction and the reduction it supports:

* `spectralPVM`, with the Cayley relabelling and the `{1}`-null lemma;
* the resolvent formula `spectralPVM_resolvent_formula`, which identifies the
  resolvent of `A` with the Borel calculus of the relabelled symbol;
* `specProjection`, the spectral projection of a Borel set, and its commutation
  and idempotence lemmas;
* `specRange` and `specRestrict`, the reduction of `A` to a spectral subspace,
  culminating in `isSelfAdjoint_specRestrict`.

What is *quantitative* about a bounded spectral set — the truncation operator and
the resolvent-gap estimate — is in the root module
`…LinearPMap.SpectralMeasure`, which imports this one.

## Sources

The Cayley transform route to the spectral measure of an unbounded self-adjoint
operator is classical: `U = (A - i)(A + i)⁻¹` is unitary, so it carries the bounded
Borel calculus, and relabelling its spectrum by the inverse Cayley map gives a
projection-valued measure on `ℝ`.  It follows the standard textbook treatment
(Rudin, *Functional Analysis*, and Reed--Simon, *Methods of Modern Mathematical
Physics I*) rather than any one source's proof.  `dev/tauceti/spectra-removal-plan.md`
records the comparison against the Spectra library's Herglotz/Poisson route, whose
endpoint `Spectra.QuantumMechanics.SpectralTheory.spectralPVM` this replaces.

The `{1}`-null argument (`diagMeasure_cayley_preimage_one`) is not taken from a
source: it is short and lives entirely inside the Borel calculus.

## Provenance

*Split, not restated.*  This module was the first four sections of
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure.lean` until
2026-07-29, when lane SPLIT-1K divided that 1243-line file at its
`end Reduce` / `section BoundedSet` seam, Tau Ceti's stated limit for a new file
being 1000 lines (`ForTauCeti/README.md` §4).  **No statement, signature, proof,
attribute or declaration name changed.**

The material itself is *new*; see
`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean` for the
provenance of the route, and `dev/tauceti/spectra-removal-plan.md` for the
comparison against Spectra's Herglotz/Poisson route that chose it.  The target is
the Spectra endpoint `Spectra.QuantumMechanics.SpectralTheory.spectralPVM`.
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

/-- The inverse Cayley relabelling is measurable.  Measurability, not continuity, is all that is
available and all that is needed: the map is genuinely singular at `w = 1`. -/
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

/-- The Cayley coordinate is the spectral point itself, coerced. -/
@[simp] theorem cayleyCoord_apply (w : _root_.spectrum ℂ (cayley hA)) :
    cayleyCoord hA w = (w : ℂ) := rfl

include hz in
/-- The resolvent symbol's denominator never vanishes on the spectrum of the Cayley transform,
because that spectrum lies on the unit circle and `z` is non-real.  This is what makes the symbol
continuous rather than merely measurable. -/
theorem cayleyDenom_ne_zero (w : _root_.spectrum ℂ (cayley hA)) :
    (Complex.I - z) + (Complex.I + z) * (w : ℂ) ≠ 0 :=
  cayley_denom_ne_zero hz
    (spectrum.norm_eq_one_of_unitary (cayley_mem_unitary hA) w.2)

/-- The symbol of `1 - (z + i) R(-i)`, up to the factor `2i`. -/
noncomputable def cayleyDenomCM : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
  ⟨fun w => (Complex.I - z) + (Complex.I + z) * (w : ℂ), by fun_prop⟩

/-- The resolvent symbol's denominator, unfolded. -/
@[simp] theorem cayleyDenomCM_apply (w : _root_.spectrum ℂ (cayley hA)) :
    cayleyDenomCM hA (z := z) w = (Complex.I - z) + (Complex.I + z) * (w : ℂ) := rfl

/-- The **resolvent symbol** `g_z(w) = (1 - w) / ((i - z) + (i + z) w)`.  For
non-real `z` it is continuous on the whole spectrum of the Cayley transform:
its only pole is the Cayley image of `z`, which is off the unit circle. -/
noncomputable def resolventSymbol : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
  ⟨fun w => (1 - (w : ℂ)) / ((Complex.I - z) + (Complex.I + z) * (w : ℂ)),
    Continuous.div (by fun_prop) (by fun_prop) (cayleyDenom_ne_zero hA hz)⟩

/-- The resolvent symbol, unfolded. -/
@[simp] theorem resolventSymbol_apply (w : _root_.spectrum ℂ (cayley hA)) :
    resolventSymbol hA hz w
      = (1 - (w : ℂ)) / ((Complex.I - z) + (Complex.I + z) * (w : ℂ)) := rfl

/-- The reciprocal of the denominator symbol, scaled by `2i`. -/
noncomputable def cayleyDenomInvCM : C(_root_.spectrum ℂ (cayley hA), ℂ) :=
  ⟨fun w => (2 * Complex.I) / ((Complex.I - z) + (Complex.I + z) * (w : ℂ)),
    Continuous.div (by fun_prop) (by fun_prop) (cayleyDenom_ne_zero hA hz)⟩

/-- The inverted denominator, unfolded. -/
@[simp] theorem cayleyDenomInvCM_apply (w : _root_.spectrum ℂ (cayley hA)) :
    cayleyDenomInvCM hA hz w
      = (2 * Complex.I) / ((Complex.I - z) + (Complex.I + z) * (w : ℂ)) := rfl

/-- `2i ≠ 0`, needed to divide by it when inverting the Cayley symbol. -/
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

/-- Spectral projections commute with the resolvent, pointwise.  The operator-level statement is
`specProjection_comm_resolvent'`; this is the form applied to a vector, which is what the
reducing-subspace arguments use. -/
theorem specProjection_resolvent_apply' {z : ℂ} (hz : z.im ≠ 0) (hzr : z ∈ resolventSet A)
    (B : Set ℝ) (hB : MeasurableSet B) (φ : H) :
    specProjection hA B hB (resolvent A hzr φ)
      = resolvent A hzr (specProjection hA B hB φ) := by
  have h := congrArg (fun T : H →L[ℂ] H => T φ)
    (specProjection_comm_resolvent' hA hz hzr B hB)
  simpa only [_root_.mul_apply_eq_comp] using h

/-- Spectral projections are idempotent. -/
theorem isIdempotentElem_specProjection (B : Set ℝ) (hB : MeasurableSet B) :
    IsIdempotentElem (specProjection hA B hB) :=
  (spectralPVM hA).proj_idem B hB

/-- Spectral projections are self-adjoint.  With idempotence this makes them *orthogonal*
projections, which is what gives `specRange` an orthogonal complement. -/
theorem isSelfAdjoint_specProjection (B : Set ℝ) (hB : MeasurableSet B) :
    IsSelfAdjoint (specProjection hA B hB) :=
  (spectralPVM hA).isSelfAdjoint_proj B hB

end Restriction

section Reduce

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B)

/-- The **spectral range** of `A` over a Borel set: the range of the spectral
projection, a closed, orthogonally complemented subspace. -/
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

/-- The domain of the spectral restriction, unfolded. -/
@[simp] theorem specRestrict_domain :
    (specRestrict hA B hB).domain = A.domain.comap (specRange hA B hB).subtype := rfl

/-- The spectral restriction acts as `A` on the underlying vector. -/
@[simp] theorem specRestrict_apply (x : (specRestrict hA B hB).domain) :
    ((specRestrict hA B hB x : specRange hA B hB) : H)
      = A ⟨((x : specRange hA B hB) : H), x.2⟩ := rfl

/-- The restriction of `A` to a spectral range is symmetric on its domain, inherited from
self-adjointness of `A`. -/
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

/-- The restricted domain is dense in the spectral range.  This is the non-obvious half of the
reduction: density of `A.domain` in `H` does not automatically survive intersecting with a
subspace, and the proof goes through the projection rather than by restriction. -/
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

end LinearPMap
end TauCeti
