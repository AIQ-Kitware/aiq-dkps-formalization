/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.InnerProductSpace.SeparatedIntertwiner
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralSupport
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.ResolventOpen
import Mathlib.Topology.UrysohnsLemma

/-!
# Rosenblum: an intertwiner of disjoint spectra vanishes

If `X : F →L[ℂ] E` intertwines two self-adjoint operators `A` and `B` whose
spectra are disjoint, then `X = 0`.

## Why this does not need a Borel functional calculus

The obvious route is to upgrade `SeparatedIntertwiner`'s continuous-symbol
intertwining to Borel symbols, then take `E_A(S) = 0` and `E_B(S) = 1` for a
Borel set `S` separating the spectra.  That upgrade is a monotone-class argument
through the diagonal measures and it is the expensive part.

It is avoidable.  The obstruction to a *continuous* separator is a single point:
both Cayley spectra contain `1` as soon as both operators are unbounded, so no
continuous symbol can be `0` on one and `1` on the other.  But `1` is a null
point for every diagonal measure (`diagMeasure_cayley_preimage_one`), so a
*sequence* of continuous symbols that vanish near `1` and separate elsewhere is
enough:

* `separator` — continuous on `ℝ`, `0` on `σ(A) ∩ ℝ`, `1` on `σ(B) ∩ ℝ`, valued
  in `[0,1]`.  Exists by Urysohn because both spectra are closed
  (`isClosed_realSpectrum`) and disjoint;
* `cayleySymbol n` — that separator pulled back along the inverse Cayley map and
  damped by `min 1 (n ‖w - 1‖)`, which is continuous **including at `1`**
  because the damping factor squeezes it to `0` there.

Then `cayleySymbol n → 0` a.e. for `A`'s diagonal measures and `→ 1` a.e. for
`B`'s — "a.e." being exactly `SpectralSupport`'s statement that the diagonal
measures live on the spectrum — and two dominated-convergence limits finish it:

* `‖cfcHom_A (g n) (X ξ)‖ → 0`;
* `‖cfcHom_B (g n) ξ - ξ‖ → 0`, so `‖X (cfcHom_B (g n) ξ)‖ → ‖X ξ‖`.

The intertwining says those two sequences are equal, so `‖X ξ‖ = 0`.

Only *diagonal* matrix elements appear, so `integral_diagMeasure` is the whole
measure-theoretic interface; no polarisation and no `pair` form is needed.

## Provenance

The theorem selection is Spectra's
(`Spectra.QuantumMechanics.SpectralTheory.generatorIntertwiner_eq_zero_of_disjoint_spectrum`);
the continuous-symbol half is
`ForTauCeti/Analysis/InnerProductSpace/SeparatedIntertwiner.lean`; the route past
the Cayley singularity is new.
-/

open scoped InnerProductSpace
open Filter Topology MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Separator

/-- The scalar inverse Cayley map on all of `ℂ`, with junk value at `1`. -/
noncomputable def cayleyCoordFun (w : ℂ) : ℝ := (Complex.I * (1 + w) / (1 - w)).re

theorem continuousOn_cayleyCoordFun : ContinuousOn cayleyCoordFun {w : ℂ | w ≠ 1} := by
  refine Complex.continuous_re.comp_continuousOn ?_
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro w hw
  exact sub_ne_zero.mpr (Ne.symm hw)

/-- The damping factor `min 1 (n ‖w - 1‖)`: continuous, valued in `[0,1]`,
zero at `w = 1`, and tending to `1` at every `w ≠ 1`. -/
noncomputable def damp (n : ℕ) (w : ℂ) : ℝ := min 1 ((n : ℝ) * ‖w - 1‖)

theorem continuous_damp (n : ℕ) : Continuous (damp n) := by
  unfold damp; fun_prop

theorem damp_nonneg (n : ℕ) (w : ℂ) : 0 ≤ damp n w :=
  le_min zero_le_one (by positivity)

theorem damp_le_one (n : ℕ) (w : ℂ) : damp n w ≤ 1 := min_le_left _ _

theorem damp_le (n : ℕ) (w : ℂ) : damp n w ≤ (n : ℝ) * ‖w - 1‖ := min_le_right _ _

theorem tendsto_damp {w : ℂ} (hw : w ≠ 1) :
    Tendsto (fun n : ℕ => damp n w) atTop (nhds 1) := by
  have hpos : 0 < ‖w - 1‖ := by
    simpa [sub_eq_zero] using norm_pos_iff.mpr (sub_ne_zero.mpr hw)
  have hev : ∀ᶠ n : ℕ in atTop, damp n w = 1 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖w - 1‖)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hle : (1 : ℝ) ≤ (n : ℝ) * ‖w - 1‖ := by
      have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      have : 1 / ‖w - 1‖ < (n : ℝ) := lt_of_lt_of_le hN hNn
      calc (1 : ℝ) = (1 / ‖w - 1‖) * ‖w - 1‖ := by field_simp
        _ ≤ (n : ℝ) * ‖w - 1‖ := by nlinarith
    exact min_eq_left hle
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

end Separator

section Rosenblum

variable {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)

/-- A continuous separator of the two real spectra: `0` on `A`'s, `1` on `B`'s,
valued in `[0,1]`.  Urysohn, using that both are closed and disjoint. -/
theorem exists_spectralSeparator (hdisj : Disjoint (spectrum A) (spectrum B)) :
    ∃ f : C(ℝ, ℝ), Set.EqOn f 0 (Complex.ofReal ⁻¹' spectrum A) ∧
      Set.EqOn f 1 (Complex.ofReal ⁻¹' spectrum B) ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by
  refine exists_continuous_zero_one_of_isClosed (isClosed_realSpectrum A)
    (isClosed_realSpectrum B) ?_
  refine Set.disjoint_left.mpr fun lam hlamA hlamB => ?_
  exact Set.disjoint_left.mp hdisj hlamA hlamB

end Rosenblum

end LinearPMap
end TauCeti
