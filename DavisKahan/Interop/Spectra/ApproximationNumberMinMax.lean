/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMaxUpper

/-!
# Infinite-dimensional Courant--Fischer localization for approximation numbers

For a bounded operator between complex Hilbert spaces, the `n`th approximation
number is already detected on finite-dimensional source subspaces.

The core threshold theorem says that every strict lower bound for `a_n(T)` is
realized, with margin, as a uniform lower modulus on an `(n+1)`-dimensional
subspace. The exact localization is expressed as an `IsLUB` statement for the
set of approximation numbers of these finite restrictions.  Approximation
numbers are real-valued, so the least-upper-bound formulation is the
conditionally-complete one for `ℝ`; the family is nonempty and bounded above by
the ambient approximation number.

## This module no longer bridges to Spectra

Until 2026-07-28 the threshold theorem
`exists_linearIndependent_lowerBound_of_lt_approximationNumber` was proved here from
`vendor/Spectra`'s projection-valued measures, one-parameter unitary groups and resolvent
form — about 175 lines — and that proof was the reason four `Spectra` imports sat at the top
of this file.  It is now a one-line consequence of
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`, which proves the
same statement from Mathlib's **continuous** functional calculus alone: the spectral
projection for `[0, s]` is replaced by the kernel of `(|T| - s)₊`, and
`ForTauCeti/Analysis/InnerProductSpace/SpectralCutoff.lean` supplies the two bounds that
kernel and its complement satisfy.

So nothing in this file mentions Spectra any more, and its remaining content — restriction
monotonicity, the finite-restriction family, its `IsLUB` characterisation and the
epsilon-form equivalence — is ordinary approximation-number theory.  **It should be moved
out of `DavisKahan/Interop/Spectra/` and staged**, most naturally as
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/FiniteRestriction.lean`.  That was
not done in the same change because the `SpectraBridge` namespace is referenced by name
across the approximation-number and sine-theta layers, and a rename is a separate,
mechanical, wide-reaching edit that deserves its own lane.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

open Module (finrank)

noncomputable section

universe v vF

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Restriction to a subspace cannot increase an approximation number. -/
theorem approximationNumber_comp_subtypeL_le
    (T : E →L[ℂ] F) (n : ℕ) (V : Submodule ℂ E) :
    (T ∘L V.subtypeL).approximationNumber n ≤ T.approximationNumber n := by
  have h := T.approximationNumber_comp_le_mul_norm V.subtypeL n
  have hsub : ‖V.subtypeL‖ ≤ (1 : ℝ) := V.norm_subtypeL_le
  calc
    (T ∘L V.subtypeL).approximationNumber n
        ≤ T.approximationNumber n * ‖V.subtypeL‖ := h
    _ ≤ T.approximationNumber n * 1 :=
      mul_le_mul_of_nonneg_left hsub (T.approximationNumber_nonneg n)
    _ = T.approximationNumber n := by rw [mul_one]

/-- Approximation numbers obtained by restricting `T` to spans of `n+1`
vectors. Linearly dependent families are harmless: they merely contribute
smaller-dimensional restrictions. -/
def finiteRestrictionApproximationNumbers
    (T : E →L[ℂ] F) (n : ℕ) : Set ℝ :=
  Set.range fun v : Fin (n + 1) → E =>
    (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n

/-- The ambient approximation number is an upper bound for all finite
restrictions. -/
theorem finiteRestrictionApproximationNumbers_upperBound
    (T : E →L[ℂ] F) (n : ℕ) :
    T.approximationNumber n ∈
      upperBounds (finiteRestrictionApproximationNumbers T n) := by
  rintro _ ⟨v, rfl⟩
  exact approximationNumber_comp_subtypeL_le T n
    (Submodule.span ℂ (Set.range v))

/-- Spectral-threshold form of the infinite-dimensional Courant--Fischer
principle. Every strict nonnegative lower bound for `a_n(T)` can be improved to
a uniform lower modulus on an `(n+1)`-dimensional subspace. -/
theorem exists_linearIndependent_lowerBound_of_lt_approximationNumber
    (T : E →L[ℂ] F) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < T.approximationNumber n) :
    ∃ s : ℝ, r < s ∧
      ∃ v : Fin (n + 1) → E, LinearIndependent ℂ v ∧
        ∀ x ∈ Submodule.span ℂ (Set.range v),
          s * ‖x‖ ≤ ‖T x‖ :=
  T.exists_linearIndependent_lowerBound_of_lt_approximationNumber n hr0 hr

/-- Every strict lower threshold for the ambient approximation number is
exceeded by an approximation number of an `(n+1)`-generated restriction. -/
theorem exists_finiteRestrictionApproximationNumber_gt_of_lt
    (T : E →L[ℂ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < T.approximationNumber n) :
    ∃ v : Fin (n + 1) → E,
      r < (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n := by
  obtain ⟨s, hrs, v, hv, hV⟩ :=
    exists_linearIndependent_lowerBound_of_lt_approximationNumber T n hr0 hr
  have hs0 : 0 ≤ s := hr0.trans hrs.le
  let V : Submodule ℂ E := Submodule.span ℂ (Set.range v)
  let b : Module.Basis (Fin (n + 1)) ℂ V := Module.Basis.span hv
  let w : Fin (n + 1) → V := fun i => b i
  have hw : LinearIndependent ℂ w := by
    simpa only [w] using b.linearIndependent
  have hsNN : s ≤ (T ∘L V.subtypeL).approximationNumber n := by
    apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
      (T ∘L V.subtypeL) n w hw
    intro x _ hxNorm
    have hxV : ((x : V) : E) ∈ V := x.property
    have hxNormE : ‖((x : V) : E)‖ = 1 := by
      simpa using hxNorm
    change s ≤ ‖T ((x : V) : E)‖
    calc
      s = s * ‖((x : V) : E)‖ := by rw [hxNormE, mul_one]
      _ ≤ ‖T ((x : V) : E)‖ := hV ((x : V) : E) hxV
  refine ⟨v, ?_⟩
  simpa only [V] using hrs.trans_le hsNN

/-- Exact finite-dimensional localization: the ambient approximation number is
the least upper bound of the approximation numbers of the restrictions to
spans of `n+1` vectors. -/
theorem approximationNumber_isLUB_finiteRestrictions
    (T : E →L[ℂ] F) (n : ℕ) :
    IsLUB (finiteRestrictionApproximationNumbers T n)
      (T.approximationNumber n) := by
  refine ⟨finiteRestrictionApproximationNumbers_upperBound T n, ?_⟩
  intro b hb
  -- Every upper bound of a nonempty family of nonnegative reals is nonnegative.
  have hb0 : 0 ≤ b :=
    (ContinuousLinearMap.approximationNumber_nonneg _ n).trans
      (hb ⟨fun _ => 0, rfl⟩)
  by_contra hnot
  have hlt : b < T.approximationNumber n := lt_of_not_ge hnot
  obtain ⟨v, hv⟩ :=
    exists_finiteRestrictionApproximationNumber_gt_of_lt T n hb0 hlt
  have hle := hb (show
    (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n ∈
      finiteRestrictionApproximationNumbers T n from ⟨v, rfl⟩)
  exact (not_le_of_gt hv) hle

/-- Epsilon-form generalized Courant--Fischer characterization. -/
theorem lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
    (T : E →L[ℂ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    r < T.approximationNumber n ↔
      ∃ s : ℝ, r < s ∧
        ∃ v : Fin (n + 1) → E, LinearIndependent ℂ v ∧
          ∀ x ∈ Submodule.span ℂ (Set.range v),
            s * ‖x‖ ≤ ‖T x‖ := by
  constructor
  · exact exists_linearIndependent_lowerBound_of_lt_approximationNumber T n hr0
  · rintro ⟨s, hrs, v, hv, hV⟩
    have hs0 : 0 ≤ s := hr0.trans hrs.le
    have hsNN : s ≤ T.approximationNumber n := by
      apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
        T n v hv
      intro x hxV hxNorm
      change s ≤ ‖T x‖
      calc
        s = s * ‖x‖ := by rw [hxNorm, mul_one]
        _ ≤ ‖T x‖ := hV x hxV
    exact hrs.trans_le hsNN

end

end SpectraBridge
end Experimental
end DavisKahan
end TauCeti