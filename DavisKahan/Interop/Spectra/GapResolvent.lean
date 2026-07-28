/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.Interop.Spectra.ClosedOperator
import DavisKahan.Sylvester.ShiftedInverseGauge
import Spectra.SpectralTheory.Spectrum
import Spectra.SpectralTheory.Algebra

/-!
# Norm-bounded gap resolvents from the Spectra spectral theorem

The unbounded Davis--Kahan development phrases spectral exteriority through the
proof-carrying predicate `TwoSidedShiftedInverseBound A c s`: a bounded
two-sided inverse of `A - c` with norm at most `s⁻¹`.  This module discharges
that predicate from a genuine spectral hypothesis — the Spectra resolvent-set
spectrum of the operator avoids the open interval `(c - s, c + s)` — using the
spectral theorem for unbounded self-adjoint operators from the Spectra library.

The first group of results is written in the Spectra idiom (group level, then
self-adjoint level). It is **ours**, not Spectra's, and it lives in the
`SpectraBridge` namespace like every other module under `DavisKahan/Interop/Spectra/`:

> Until 2026-07-28 these three theorems were declared into
> `namespace Spectra.QuantumMechanics.SpectralTheory`, on the reasoning that they
> were destined for upstreaming into `Spectra/SpectralTheory/`. That destination
> changed — `vendor/Spectra` is being retired from the build
> (`dev/tauceti/spectra-removal-plan.md`), so these are Tau Ceti candidates, not
> Spectra contributions. Leaving them in the donor's namespace would have made
> them indistinguishable from donor material once the imports are gone, and the
> attribution ledger would have credited Spectra for our theorems. Statements and
> proofs are unchanged; only the enclosing namespace moved.

* `spectralProjection_eq_zero_of_forall_mem_resolventSet`: a measurable set
  every point of which lies in the resolvent set carries no spectral mass, by
  second countability and the scalar Borel measures.
* `exists_norm_le_two_sided_shifted_inverse_of_spectralProjection_Ioo_eq_zero`:
  the quantitative refinement of
  `mem_resolventSet_of_spectralProjection_Ioo_eq_zero` — a spectral gap of
  radius `s` around `c` produces a two-sided bounded inverse of norm at most
  `s⁻¹`, through the truncated symbol `(l - c)⁻¹` and the sharp calculus norm
  bound.
* `exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap`: the same
  statement from the spectrum-avoidance hypothesis, for a self-adjoint
  `LinearPMap`.

The second section converts the result to the Davis--Kahan closed-operator
wrapper, discharging `TwoSidedShiftedInverseBound` (and hence the hypotheses of
`sinTheta_unbounded_opNorm` and the unbounded Sylvester estimates) from genuine
spectra.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
open Spectra.Borel
open Spectra.OneParameterUnitaryGroup
open Spectra.Resolvent
open Spectra.YosidaHille
-- Was implicit while the results below sat inside `Spectra.QuantumMechanics.SpectralTheory`;
-- now that they are in our own namespace the donor names have to be opened explicitly.
open Spectra.QuantumMechanics.SpectralTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

-- Fully qualified: the short name resolved only while this block sat inside
-- `namespace Spectra.QuantumMechanics`.  `open Spectra.OneParameterUnitaryGroup`
-- above opens that namespace's *members*, not the type of the same name.
variable (U_grp : Spectra.OneParameterUnitaryGroup (H := H))

/-- **Pointwise resolvent membership kills the spectral mass of a set.**  If
every point of a measurable set `B` lies in the resolvent set of the
generator, then the spectral projection of `B` vanishes: each point owns a
projection-free interval, and the scalar Borel measures are second-countably
locally null on `B`. -/
theorem spectralProjection_eq_zero_of_forall_mem_resolventSet
    {B : Set ℝ} (hB : MeasurableSet B)
    (h : ∀ lam ∈ B, (lam : ℂ) ∈ resolventSet (generator U_grp)) :
    spectralProjection U_grp B hB = 0 := by
  have hM : ∀ φ : H, borelMeasure U_grp φ B = 0 := by
    intro φ
    refine measure_null_of_locally_null B fun lam hlam => ?_
    obtain ⟨ε, hε, hproj⟩ :=
      spectralProjection_Ioo_eq_zero_of_mem_resolventSet U_grp (h lam hlam)
    refine ⟨Set.Ioo (lam - ε) (lam + ε),
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ?_), ?_⟩
    · exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    · refine (spectralProjection_eq_zero_iff_measure_zero U_grp _
        measurableSet_Ioo φ).mp ?_
      rw [hproj]
      rfl
  ext φ
  rw [zero_apply]
  exact (spectralProjection_eq_zero_iff_measure_zero U_grp B hB φ).mpr (hM φ)

/-- **Quantitative spectral-gap resolvent, group level.**  If the spectral
projection of `(c - s, c + s)` vanishes, then `generator U_grp - c` has a
two-sided bounded inverse of norm at most `s⁻¹`, namely the bounded calculus
of the truncated symbol `(l - c)⁻¹`. -/
theorem exists_norm_le_two_sided_shifted_inverse_of_spectralProjection_Ioo_eq_zero
    {c s : ℝ} (hs : 0 < s)
    (hgap : spectralProjection U_grp (Set.Ioo (c - s) (c + s))
      measurableSet_Ioo = 0) :
    ∃ R : H →L[ℂ] H, ‖R‖ ≤ s⁻¹ ∧
      (∀ ψ : (generator U_grp).domain,
        R ((generator U_grp) ψ - (c : ℂ) • (ψ : H)) = (ψ : H)) ∧
      ∀ φ : H, ∃ hmem : R φ ∈ (generator U_grp).domain,
        (generator U_grp) ⟨R φ, hmem⟩ - (c : ℂ) • R φ = φ := by
  classical
  have hCmeas : MeasurableSet (Set.Ioo (c - s) (c + s))ᶜ :=
    measurableSet_Ioo.compl
  -- on the complement, `|l - c| ≥ s`
  have hball : ∀ l ∈ (Set.Ioo (c - s) (c + s))ᶜ, s ≤ |l - c| := by
    intro l hl
    rw [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, not_lt] at hl
    rcases hl with h | h
    · rw [abs_of_nonpos (by linarith : l - c ≤ 0)]; linarith
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ l - c)]; linarith
  -- the bounded truncated symbol
  set g' : ℝ → ℂ :=
    (Set.Ioo (c - s) (c + s))ᶜ.indicator (fun l => ((l : ℂ) - (c : ℂ))⁻¹)
    with hg'def
  have hg'meas : Measurable g' := by
    rw [hg'def]
    exact ((Complex.measurable_ofReal.sub measurable_const).inv).indicator
      hCmeas
  have hg'le : ∀ l, ‖g' l‖ ≤ s⁻¹ := by
    intro l
    by_cases hl : l ∈ (Set.Ioo (c - s) (c + s))ᶜ
    · rw [hg'def, Set.indicator_of_mem hl, norm_inv, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      simpa only [one_div] using one_div_le_one_div_of_le hs (hball l hl)
    · rw [hg'def, Set.indicator_of_notMem hl, norm_zero]; positivity
  have hg'bdd : ∃ C, ∀ l, ‖g' l‖ ≤ C := ⟨s⁻¹, hg'le⟩
  -- the product `(l - c)·g'(l) = 1_{gapᶜ}(l)`
  have hprod : ∀ l : ℝ, ((l : ℂ) - (c : ℂ)) * g' l
      = (Set.Ioo (c - s) (c + s))ᶜ.indicator (fun _ => (1 : ℂ)) l := by
    intro l
    by_cases hl : l ∈ (Set.Ioo (c - s) (c + s))ᶜ
    · have hne : (l : ℂ) - (c : ℂ) ≠ 0 := by
        rw [sub_ne_zero, Ne, Complex.ofReal_inj]
        intro heq
        have hb := hball l hl; rw [heq, sub_self, abs_zero] at hb; linarith
      rw [hg'def, Set.indicator_of_mem hl, Set.indicator_of_mem hl,
        mul_inv_cancel₀ hne]
    · rw [hg'def, Set.indicator_of_notMem hl, Set.indicator_of_notMem hl,
        mul_zero]
  -- boundedness of `l·g'`
  have hlg'meas : Measurable fun l : ℝ => (l : ℂ) * g' l :=
    Complex.measurable_ofReal.mul hg'meas
  have hlg'bdd : ∃ C, ∀ ω : ℝ, ‖(ω : ℂ) * g' ω‖ ≤ C := by
    refine ⟨1 + |c| * s⁻¹, fun ω => ?_⟩
    by_cases hω : ω ∈ (Set.Ioo (c - s) (c + s))ᶜ
    · rw [hg'def, Set.indicator_of_mem hω, norm_mul, norm_inv,
        show ‖(ω : ℂ)‖ = |ω| from by rw [Complex.norm_real, Real.norm_eq_abs],
        show ‖(ω : ℂ) - (c : ℂ)‖ = |ω - c| from by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]]
      have hb : s ≤ |ω - c| := hball ω hω
      have hb0 : (0:ℝ) < |ω - c| := lt_of_lt_of_le hs hb
      have htri : |ω| ≤ |ω - c| + |c| := by
        rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
        calc ‖ω‖ = ‖(ω - c) + c‖ := by congr 1; ring
          _ ≤ ‖ω - c‖ + ‖c‖ := norm_add_le _ _
      calc |ω| * |ω - c|⁻¹
          ≤ (|ω - c| + |c|) * |ω - c|⁻¹ :=
            mul_le_mul_of_nonneg_right htri (inv_nonneg.mpr hb0.le)
        _ = 1 + |c| * |ω - c|⁻¹ := by rw [add_mul, mul_inv_cancel₀ hb0.ne']
        _ ≤ 1 + |c| * s⁻¹ := by
            have hinv : |ω - c|⁻¹ ≤ s⁻¹ := by
              simpa only [one_div] using one_div_le_one_div_of_le hs hb
            have := mul_le_mul_of_nonneg_left hinv (abs_nonneg c)
            linarith
    · rw [hg'def, Set.indicator_of_notMem hω, mul_zero, norm_zero]; positivity
  -- `(l - c)·g'` as a single symbol equals `1_{gapᶜ}`
  have hsymeq : (fun l : ℝ => (l : ℂ) * g' l - (c : ℂ) * g' l)
      = (Set.Ioo (c - s) (c + s))ᶜ.indicator (fun _ => (1 : ℂ)) := by
    funext l; rw [← hprod l]; ring
  have hcg'meas : Measurable fun l : ℝ => (c : ℂ) * g' l :=
    measurable_const.mul hg'meas
  have hcg'bdd : ∃ C, ∀ ω : ℝ, ‖(c : ℂ) * g' ω‖ ≤ C := by
    obtain ⟨C, hC⟩ := hg'bdd
    exact ⟨‖(c : ℂ)‖ * C, fun ω => by rw [norm_mul]; gcongr; exact hC ω⟩
  have hsubm : Measurable fun l : ℝ => (l : ℂ) * g' l - (c : ℂ) * g' l :=
    hlg'meas.sub hcg'meas
  have hsubb : ∃ C, ∀ ω : ℝ, ‖(ω : ℂ) * g' ω - (c : ℂ) * g' ω‖ ≤ C := by
    refine ⟨1, fun ω => ?_⟩
    rw [show (ω : ℂ) * g' ω - (c : ℂ) * g' ω
        = ((ω : ℂ) - (c : ℂ)) * g' ω from by ring, hprod ω]
    by_cases hω : ω ∈ (Set.Ioo (c - s) (c + s))ᶜ
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  -- `E(gapᶜ) = id`
  have hcompl_id : spectralProjection U_grp (Set.Ioo (c - s) (c + s))ᶜ
      measurableSet_Ioo.compl = ContinuousLinearMap.id ℂ H := by
    rw [spectralProjection_compl U_grp (Set.Ioo (c - s) (c + s))
      measurableSet_Ioo, hgap, sub_zero]
  -- the operator identity `Φ(l·g') - Φ(c·g') = E(gapᶜ) = id`
  have hop : spectralCalculus U_grp (fun l : ℝ => (l : ℂ) * g' l)
        hlg'meas hlg'bdd
      - spectralCalculus U_grp (fun l : ℝ => (c : ℂ) * g' l)
        hcg'meas hcg'bdd
      = ContinuousLinearMap.id ℂ H := by
    rw [← spectralCalculus_sub U_grp _ _ hlg'meas hlg'bdd hcg'meas hcg'bdd
        hsubm hsubb,
      spectralCalculus_congr U_grp hsymeq hsubm hsubb
        (measurable_const.indicator hCmeas) (indicator_one_bdd _)]
    exact hcompl_id
  -- the key value identity, used for both inverses
  have hmem : ∀ φ : H,
      spectralCalculus U_grp g' hg'meas hg'bdd φ ∈ (generator U_grp).domain :=
    fun φ => spectralCalculus_mem_generatorDomain U_grp g' hg'meas hg'bdd
      hlg'meas hlg'bdd φ
  have hval : ∀ φ : H,
      generator U_grp ⟨spectralCalculus U_grp g' hg'meas hg'bdd φ, hmem φ⟩
        - (c : ℂ) • spectralCalculus U_grp g' hg'meas hg'bdd φ = φ := by
    intro φ
    rw [generator_spectralCalculus U_grp g' hg'meas hg'bdd hlg'meas hlg'bdd φ,
      show (c : ℂ) • spectralCalculus U_grp g' hg'meas hg'bdd φ
          = spectralCalculus U_grp (fun l : ℝ => (c : ℂ) * g' l)
            hcg'meas hcg'bdd φ from by
        rw [spectralCalculus_smul U_grp (c : ℂ) g' hg'meas hg'bdd
          hcg'meas hcg'bdd, smul_apply],
      ← sub_apply, hop, ContinuousLinearMap.id_apply]
  refine ⟨spectralCalculus U_grp g' hg'meas hg'bdd,
    norm_spectralCalculus_le U_grp g' hg'meas hg'bdd hg'le, ?_,
    fun φ => ⟨hmem φ, hval φ⟩⟩
  intro ψ
  rw [map_sub, ContinuousLinearMap.map_smul,
    ← generator_spectralCalculus_comm U_grp g' hg'meas hg'bdd ψ]
  exact hval (ψ : H)

/-- **Quantitative spectral-gap resolvent for a self-adjoint operator.**  If
the spectrum of a self-adjoint `A` avoids the open interval `(c - s, c + s)`,
then `A - c` has a two-sided bounded inverse of norm at most `s⁻¹`. -/
theorem exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {c s : ℝ} (hs : 0 < s)
    (hgap : ∀ lam ∈ Set.Ioo (c - s) (c + s),
      lam ∉ Spectra.Resolvent.spectrum A) :
    ∃ R : H →L[ℂ] H, ‖R‖ ≤ s⁻¹ ∧
      (∀ ψ : A.domain, R (A ψ - (c : ℂ) • (ψ : H)) = (ψ : H)) ∧
      ∀ φ : H, ∃ hmem : R φ ∈ A.domain,
        A ⟨R φ, hmem⟩ - (c : ℂ) • R φ = φ := by
  have hres : ∀ lam ∈ Set.Ioo (c - s) (c + s),
      (lam : ℂ) ∈ resolventSet (generator (genToGroup hA)) := by
    intro lam hlam
    have h1 : ¬ ((lam : ℂ) ∉ Spectra.Resolvent.resolventSet A) :=
      hgap lam hlam
    rw [generator_genToGroup hA]
    exact not_not.mp h1
  have hproj : spectralProjection (genToGroup hA)
      (Set.Ioo (c - s) (c + s)) measurableSet_Ioo = 0 :=
    spectralProjection_eq_zero_of_forall_mem_resolventSet (genToGroup hA)
      measurableSet_Ioo hres
  have h :=
    exists_norm_le_two_sided_shifted_inverse_of_spectralProjection_Ioo_eq_zero
      (genToGroup hA) hs hproj
  rwa [generator_genToGroup hA] at h

/-- **Genuine spectra discharge the shifted-inverse hypothesis.**  For a DK
closed operator whose canonical `LinearPMap` view is self-adjoint and whose
Spectra resolvent-set spectrum avoids `(c - s, c + s)`, the proof-carrying
predicate `TwoSidedShiftedInverseBound A c s` holds.  This connects the
honest unbounded Davis--Kahan hypotheses to the unbounded spectral theorem. -/
theorem twoSidedShiftedInverseBound_of_spectrum_gap
    {A : DKClosedOperator (H := H)}
    (hA : IsSelfAdjoint A.toLinearPMap) {c s : ℝ} (hs : 0 < s)
    (hgap : ∀ lam ∈ Set.Ioo (c - s) (c + s),
      lam ∉ Spectra.Resolvent.spectrum A.toLinearPMap) :
    TauCeti.DavisKahan.Experimental.ExactSinTheta.TwoSidedShiftedInverseBound
      A c s := by
  obtain ⟨R, hnorm, hleft, hright⟩ :=
    exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap hA hs hgap
  exact ⟨R, fun z => (hright z).choose,
    fun x => hleft x, fun z => (hright z).choose_spec, hnorm⟩


end SpectraBridge
end Experimental
end DavisKahan
end TauCeti