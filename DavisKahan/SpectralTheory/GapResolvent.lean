/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 5
-/
import DavisKahan.SpectralTheory.PartialMap.Basic
import DavisKahan.Sylvester.ShiftedInverseGauge
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.RealLowerBound

open TauCeti.DavisKahan.Sylvester

/-!
# Norm-bounded gap resolvents

The unbounded Davis--Kahan development phrases spectral exteriority through the
proof-carrying predicate `TwoSidedShiftedInverseBound A c s`: a bounded
two-sided inverse of `A - c` with norm at most `s⁻¹`.  This module discharges
that predicate from a genuine spectral hypothesis — the spectrum of the operator
avoids the open interval `(c - s, c + s)`.

## History: this was the largest Spectra dependency in the tree

Until 2026-07-28 the bound was obtained from `vendor/Spectra` through the full
spectral-theorem stack: Stone's theorem (`genToGroup`) to manufacture a unitary
group from the self-adjoint operator, that group's projection-valued measure,
the bounded Borel functional calculus, the truncated symbol `(l - c)⁻¹`, and the
sharp calculus norm bound.  Two substantial intermediate theorems lived here to
support it — `spectralProjection_eq_zero_of_forall_mem_resolventSet` and
`exists_norm_le_two_sided_shifted_inverse_of_spectralProjection_Ioo_eq_zero`.

**None of that is necessary.**  The bound is a C⋆-algebra fact about the
*bounded* operator `R = (A - c)⁻¹`:

* resolvent spectral mapping puts `spectrum R \ {0}` inside
  `(· - c)⁻¹ '' spectrum A` — elementary algebra with domain bookkeeping;
* the spectral gap therefore bounds `spectrum R` by `s⁻¹`;
* and for a **self-adjoint** element the norm *is* the spectral radius, which is
  Mathlib's `IsSelfAdjoint.spectralRadius_eq_nnnorm`.

The replacement lives in
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/{Resolvent,ResolventBound,SelfAdjointResolvent}.lean`
and is Spectra-free.  The two intermediate theorems were deleted rather than
kept: they were scaffolding for the PVM route, nothing outside this file used
them, and retaining them would have kept the whole projection-valued-measure
layer on the critical path of the completed Spectra removal.  They
remain in the history at `a58913e`.

This module is Spectra-free, and as the note here used to predict, it has been
relocated now that `Interop/Spectra/` is gone: it is spectral theory, and it sits
with the rest of it.
-/

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace TauCeti
namespace DavisKahan


/-- **A spectral gap gives a norm-bounded two-sided inverse.**  If the spectrum
of a self-adjoint `A` avoids `(c - s, c + s)`, then `A - c` has a bounded
two-sided inverse of norm at most `s⁻¹`. -/
theorem exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {c s : ℝ} (hs : 0 < s)
    (hgap : ∀ lam ∈ Set.Ioo (c - s) (c + s),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum A) :
    ∃ R : H →L[ℂ] H, ‖R‖ ≤ s⁻¹ ∧
      (∀ ψ : A.domain, R (A ψ - (c : ℂ) • (ψ : H)) = (ψ : H)) ∧
      ∀ φ : H, ∃ hmem : R φ ∈ A.domain,
        A ⟨R φ, hmem⟩ - (c : ℂ) • R φ = φ := by
  -- The upstream theorem inverts `c • I - A`; the Davis--Kahan statement is about `A - c`,
  -- so the witness is the negated resolvent.  The norm bound is unaffected.
  obtain ⟨R, hnorm, hleft, hright⟩ :=
    TauCeti.LinearPMap.exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap hA hs hgap
  refine ⟨-R, by simpa using hnorm, fun ψ => ?_, fun φ => ?_⟩
  · have h := hleft ψ
    have harg : A ψ - (c : ℂ) • (ψ : H) = -((c : ℂ) • (ψ : H) - A ψ) := by module
    rw [_root_.neg_apply, harg, map_neg, h, neg_neg]
  · obtain ⟨hmem, hsolve⟩ := hright φ
    refine ⟨neg_mem hmem, ?_⟩
    have hneg : A (⟨(-R) φ, neg_mem hmem⟩ : A.domain) = -(A ⟨R φ, hmem⟩) :=
      _root_.LinearPMap.map_neg A ⟨R φ, hmem⟩
    rw [hneg]
    simp only [_root_.neg_apply]
    linear_combination (norm := module) hsolve

/-- **Genuine spectra discharge the shifted-inverse hypothesis.**  For a DK
closed operator whose canonical `LinearPMap` view is self-adjoint and whose
spectrum avoids `(c - s, c + s)`, the proof-carrying predicate
`TwoSidedShiftedInverseBound A c s` holds.  This connects the honest unbounded
Davis--Kahan hypotheses to the spectral theory. -/
theorem twoSidedShiftedInverseBound_of_spectrum_gap
    {A : H →ₗ.[ℂ] H}
    (hA : IsSelfAdjoint A) {c s : ℝ} (hs : 0 < s)
    (hgap : ∀ lam ∈ Set.Ioo (c - s) (c + s),
      (lam : ℂ) ∉ TauCeti.LinearPMap.spectrum A) :
    TauCeti.DavisKahan.Sylvester.TwoSidedShiftedInverseBound
      A c s := by
  obtain ⟨R, hnorm, hleft, hright⟩ :=
    exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap hA hs hgap
  exact ⟨R, fun z => (hright z).choose,
    fun x => hleft x, fun z => (hright z).choose_spec, hnorm⟩

/-- **The bounded shifted inverse from coercivity against a reflection.**

This is the theorem GOAL.md section 6.2 asks for, in the form Theorem 8.1
consumes.  The bounded Section 8 argument reaches invertibility of `J (A - c)`
through `TauCeti.isUnit_of_coercive`, which needs `A` everywhere defined; that is
what blocks lifting `isQuarterAcute_of_orderedFormGap` to an unbounded ambient
operator.

No new Lax--Milgram is needed.  Coercivity against an isometry already forces the
norm lower bound `δ ‖x‖ ≤ ‖A x - c x‖`; the triangle inequality spreads it across
the whole interval `(c - δ, c + δ)` with constant `δ - |lam - c|`; each point is
then a resolvent point by `mem_resolventSet_of_lower_bound`; and the existing gap
resolvent supplies the two-sided bounded inverse of norm at most `δ⁻¹`.

`J` is only required to preserve norms, so a reflection qualifies. -/
theorem twoSidedShiftedInverseBound_of_coercive_comp
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    {J : H →L[ℂ] H} (hJ : ∀ y : H, ‖J y‖ = ‖y‖)
    {c δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ x : A.domain,
      δ * ‖(x : H)‖ ^ 2 ≤ (⟪J (A x - (c : ℂ) • (x : H)), (x : H)⟫_ℂ).re) :
    TauCeti.DavisKahan.Sylvester.TwoSidedShiftedInverseBound A c δ := by
  refine twoSidedShiftedInverseBound_of_spectrum_gap hA hδ ?_
  intro lam hlam
  have hbase := TauCeti.LinearPMap.norm_sub_smul_ge_of_coercive_comp hJ hcoer
  obtain ⟨h1, h2⟩ := hlam
  have hpos : 0 < δ - |lam - c| := by
    rcases abs_cases (lam - c) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
  have hnorm : ∀ x : A.domain,
      (δ - |lam - c|) * ‖(x : H)‖ ≤ ‖A x - ((lam : ℝ) : ℂ) • (x : H)‖ := by
    intro x
    have hsplit : A x - ((lam : ℝ) : ℂ) • (x : H)
        = (A x - ((c : ℝ) : ℂ) • (x : H)) + (((c - lam : ℝ)) : ℂ) • (x : H) := by
      push_cast
      module
    have htri : ‖A x - ((c : ℝ) : ℂ) • (x : H)‖ - ‖(((c - lam : ℝ)) : ℂ) • (x : H)‖
        ≤ ‖A x - ((lam : ℝ) : ℂ) • (x : H)‖ := by
      rw [hsplit]
      simpa using
        norm_sub_norm_le (A x - ((c : ℝ) : ℂ) • (x : H)) (-((((c - lam : ℝ)) : ℂ) • (x : H)))
    have hsm : ‖(((c - lam : ℝ)) : ℂ) • (x : H)‖ = |c - lam| * ‖(x : H)‖ := by
      rw [norm_smul]
      congr 1
      exact Complex.norm_real (c - lam)
    have habs : |c - lam| = |lam - c| := abs_sub_comm c lam
    have hb := hbase x
    rw [hsm, habs] at htri
    nlinarith [norm_nonneg ((x : H))]
  have hres := TauCeti.LinearPMap.mem_resolventSet_of_lower_bound hA
    (Complex.conj_ofReal lam) hpos hnorm
  simpa [TauCeti.LinearPMap.spectrum] using hres

end DavisKahan
end TauCeti
