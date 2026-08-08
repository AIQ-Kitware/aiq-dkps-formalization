/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Frontier.Section8

/-!
# Davis--Kahan 1970, Theorem 8.2: the printed perturbation-norm branch selection

This module proves the branch-selection half of Theorem 8.2 from the printed
hypotheses alone.  Nothing quantitative is supplied by the caller: no contour,
no continuation witness, no projection-Lipschitz constant, no half-gap bridge.

## The printed hypotheses

Exactly the `sin 2Θ` configuration plus what Theorem 8.2 adds:

* `A` self-adjoint, `H` self-adjoint, `P` reduces `A`, `Q` reduces `A + H`;
* `spectrum(Λ₀) ⊆ [β, α]` and `spectrum(Λ₁)` outside `(β - δ, α + δ)`
  (`Λⱼ` = the blocks of `A + H` along `Q`, `Qᗮ`) -- the `sin 2Θ` hypotheses;
* `spectrum(A₀) ⊆ [β - δ/2, α + δ/2]` -- the extra printed placement;
* `‖H‖ < δ / 2` -- the printed perturbation alternative.

## The printed proof

`B σ := A + H - σ • H`, so `B 0 = A + H` and `B 1 = A`; the path runs *from*
the perturbed operator back to the unperturbed one.  `R σ` is the spectral
subspace of `B σ` for the fixed central band `(β - δ/2, α + δ/2)`, obtained
as a Riesz projection along one fixed circle, hence norm-continuous.

`f σ := directedGap (R σ) Q` is continuous, `f 0 = 0`, and the `sin 2Θ`
theorem compares `Q` (which carries the full gap `δ`) with `R σ`:

```
√2 · f σ ≤ ‖sin 2Θ(Q, R σ)‖ ≤ 2 σ ‖H‖ / δ ≤ 2 ‖H‖ / δ < 1   whenever f σ ≤ √2/2
```

so `f σ ≤ √2/2` forces `f σ < √2/2`, *strictly and uniformly in `σ`*.  With
`f 0 = 0` and the intermediate value theorem, `f σ < √2/2` for every `σ`.  At
`σ = 1` the printed placement of `A₀` gives `P ≤ R 1`, and the conclusion
transfers to the source pair.

## What the printed conclusion is, precisely

The printed conclusion is `Θ < π/4`.  Read with the *symmetric* projector gap
`‖P_P - P_Q‖` it is **false** as stated: on a one-dimensional space take
`A = 0`, perturbation `0`, `P = ⊥`, `Q = ⊤`, `β = α = 0`, `δ = 1`.  Every
printed hypothesis holds (`spectrum(Λ₁)` and `spectrum(A₀)` are empty), yet
`‖P_P - P_Q‖ = 1`.  The pair `(P, Q)` is not acute there, so the paper's `Θ`
-- built from the direct rotation, which needs acuteness -- is not defined,
and the implicit equal-dimension convention of Section 1 is what excludes it.

The formalisation therefore concludes with the *directed* quarter-angle bound
`directedGap P Q < √2/2`: every unit vector of `P H` makes an angle strictly
less than `π/4` with `Q H`.  That is exactly what the printed argument
delivers (`P = P Q(1)` controls only how `P H` sits inside `R 1`), it is the
statement the later reductions consume, and it coincides with the printed
`Θ < π/4` whenever the pair is acute.

## Placement

`DavisKahan/Frontier/Section8.lean` already owns the Section 8 analytic
bridges and imports every prerequisite (the Riesz circle, the bounded
spectral projections, the `sin 2Θ` theorem, the canonical gap circle).  This
is its sibling so that the source-facing wrapper layer stays unchanged.
-/

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Frontier
namespace Section8

open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Experimental.Foundation
open RieszCircle

universe u

/-! ## 1. Two scalar facts about `√2 / 2` -/

theorem sqrt_two_div_two_sq : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem sqrt_two_div_two_pos : (0 : ℝ) < Real.sqrt 2 / 2 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- On the closed quarter branch the cosine is at least `√2 / 2`. -/
theorem sqrt_two_div_two_le_sqrt_one_sub_sq {g : ℝ} (hg : g ≤ Real.sqrt 2 / 2)
    (hg0 : 0 ≤ g) : Real.sqrt 2 / 2 ≤ Real.sqrt (1 - g ^ 2) := by
  have hsq : (Real.sqrt 2 / 2) ^ 2 ≤ 1 - g ^ 2 := by
    rw [sqrt_two_div_two_sq]
    nlinarith [sqrt_two_div_two_sq, sq_nonneg g]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq sqrt_two_div_two_pos.le] at h

/-! ## 2. The `sin 2Θ` lower bound on the close branch

The `sin 2Θ` theorem bounds `‖sin 2Θ‖` from above; the bootstrap needs the
reverse comparison with the gap.  Away from the quarter turn,
`‖sin 2Θ‖ ≥ 2 cos Θ · sin Θ` pointwise on the source subspace, and the
existing acute coercivity of the directed cosine supplies `cos Θ`. -/

section Bridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The directed sine lands in the source subspace, for *every* vector: it
kills the orthogonal complement and preserves the source. -/
theorem sinAngleOperatorDirectedC_apply_mem_source (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (x : E) :
    sinAngleOperatorDirectedC U V x ∈ U := by
  have hsplit : x = U.starProjection x + Uᗮ.starProjection x := by
    rw [Submodule.starProjection_orthogonal_apply]; abel
  rw [hsplit, map_add,
    sinAngleOperatorDirectedC_apply_eq_zero_of_mem_orthogonal U V
      (Uᗮ.starProjection_apply_mem x), add_zero]
  exact sinAngleOperatorDirectedC_apply_mem U V (U.starProjection_apply_mem x)

/-- **The double-angle sine dominates `2 cos Θ sin Θ`.**

`‖sin 2Θ(U,V)‖ ≥ 2 √(1 - directedGap²) · directedGap`.  Pointwise: the
directed sine maps into `U`, where the directed cosine is coercive with
constant `√(1 - directedGap²)`, so `‖cos Θ (sin Θ x)‖ ≥ √(1-g²) ‖sin Θ x‖`;
taking the supremum over `x` turns `‖sin Θ‖ = g` into the claim. -/
theorem two_mul_sqrt_mul_directedGap_le_norm_sinTwoAngleOperatorC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    2 * Real.sqrt (1 - directedGap U V ^ 2) * directedGap U V ≤
      ‖sinTwoAngleOperatorC U V‖ := by
  set g : ℝ := directedGap U V with hgdef
  set c0 : ℝ := Real.sqrt (1 - g ^ 2) with hc0
  set S : E →L[ℂ] E := sinAngleOperatorDirectedC U V with hS
  set C : E →L[ℂ] E := cosAngleOperatorC U V with hC
  have hSnorm : ‖S‖ = g := norm_sinAngleOperatorDirectedC U V
  have hc0nonneg : 0 ≤ c0 := Real.sqrt_nonneg _
  have hM : ‖sinTwoAngleOperatorC U V‖ = 2 * ‖C * S‖ := by
    have hcomm : Commute S C :=
      commute_sinAngleOperatorDirectedC_cosAngleOperatorC U V
    rw [sinTwoAngleOperatorC, norm_smul, hcomm.eq]
    norm_num
  rcases eq_or_lt_of_le hc0nonneg with h0 | hpos
  · rw [← h0]
    simp only [mul_zero, zero_mul]
    positivity
  · have hpt : ∀ x : E, c0 * ‖S x‖ ≤ ‖(C * S) x‖ := fun x =>
      norm_cosAngleOperatorC_apply_ge U V
        (sinAngleOperatorDirectedC_apply_mem_source U V x)
    have hSle : ‖S‖ ≤ ‖C * S‖ / c0 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
      have h1 := hpt x
      have h2 : ‖(C * S) x‖ ≤ ‖C * S‖ * ‖x‖ := (C * S).le_opNorm x
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      nlinarith [norm_nonneg (S x), norm_nonneg x]
    rw [hM, hSnorm] at *
    rw [le_div_iff₀ hpos] at hSle
    nlinarith [hSle]

/-- The two spellings of the double-angle sine agree in norm, with the roles
of the two subspaces exchanged: the `DoubleAngle` operator
`sin 2Θ(U,V) = 2 P_{Uᗮ} P_V P_U` has the norm of the `Geometry` operator
`sin 2Θ_C(V,U)`. -/
theorem norm_sinTwoAngleOperator_eq_norm_sinTwoAngleOperatorC_swap
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sinTwoAngleOperator U V‖ = ‖sinTwoAngleOperatorC V U‖ := by
  rw [norm_sinTwoAngleOperatorC V U, sinTwoAngleOperator, norm_smul]
  norm_num

/-- **The bootstrap comparison.**  On the closed quarter branch the
double-angle sine dominates `√2` times the directed gap. -/
theorem sqrt_two_mul_directedGap_le_norm_sinTwoAngleOperator
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hclose : directedGap V U ≤ Real.sqrt 2 / 2) :
    Real.sqrt 2 * directedGap V U ≤ ‖sinTwoAngleOperator U V‖ := by
  have hg0 : 0 ≤ directedGap V U := norm_nonneg _
  have hcos := sqrt_two_div_two_le_sqrt_one_sub_sq hclose hg0
  calc Real.sqrt 2 * directedGap V U
      = 2 * (Real.sqrt 2 / 2) * directedGap V U := by ring
    _ ≤ 2 * Real.sqrt (1 - directedGap V U ^ 2) * directedGap V U := by
        have h2 : (0 : ℝ) ≤ 2 := by norm_num
        nlinarith [hcos, hg0]
    _ ≤ ‖sinTwoAngleOperatorC V U‖ :=
        two_mul_sqrt_mul_directedGap_le_norm_sinTwoAngleOperatorC V U
    _ = ‖sinTwoAngleOperator U V‖ :=
        (norm_sinTwoAngleOperator_eq_norm_sinTwoAngleOperatorC_swap U V).symm

end Bridge

/-! ## 3. Two operator helpers

Both are ambient statements about a bounded self-adjoint operator; neither
mentions a restriction, which keeps the subspace bookkeeping out of the
analytic steps. -/

section Helpers

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The numerical radius controls the norm.**  For a self-adjoint operator a
two-sided form bound is a norm bound, with no loss.  This is Mathlib's
Rayleigh-quotient description of the norm of a symmetric operator. -/
theorem opNorm_le_of_abs_re_inner_le {S : H →L[ℂ] H} (hS : IsSelfAdjointOperator S)
    {M : ℝ} (hM : 0 ≤ M)
    (hform : ∀ x : H, |RCLike.re ⟪S x, x⟫_ℂ| ≤ M * ‖x‖ ^ 2) : ‖S‖ ≤ M := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient S hS]
  refine ciSup_le fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [ContinuousLinearMap.rayleighQuotient] using hM
  · have hx2 : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    have h := hform x
    rw [ContinuousLinearMap.rayleighQuotient, abs_div,
      abs_of_nonneg hx2.le, div_le_iff₀ hx2]
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    exact h

/-- **Neumann perturbation of the resolvent set.**  If every point of the real
spectrum of a self-adjoint `T` is at distance at least `m` from `z`, then `z`
survives in the resolvent set of `T + K` for every perturbation of norm below
`m`.  No self-adjointness of `K` is needed. -/
theorem notMem_spectrum_add_of_realSpectrum_dist
    {T K : H →L[ℂ] H} (hT : IsSelfAdjointOperator T) {z : ℂ} {m : ℝ} (hm : 0 < m)
    (hsep : ∀ lam ∈ realSpectrum T, m ≤ ‖z - (lam : ℂ)‖) (hK : ‖K‖ < m) :
    z ∉ spectrum ℂ (T + K) := by
  obtain ⟨hres, hbound⟩ :=
    complex_inResolventSet_and_norm_resolvent_le_inv_distance T hT z m hm hsep
  have hznot : z ∉ spectrum ℂ T := not_mem_spectrum_of_inResolventSet T hres
  have hunit : IsUnit (z • (1 : H →L[ℂ] H) - T) := by
    have h := spectrum.notMem_iff.mp hznot
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hinvnorm : ‖Ring.inverse (z • (1 : H →L[ℂ] H) - T)‖ ≤ m⁻¹ := by
    rw [norm_ringInverse_pencil_eq_norm_resolventOperator T hres]
    exact hbound
  have hval : ((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) =
      Ring.inverse (z • (1 : H →L[ℂ] H) - T) :=
    (Ring.inverse_unit hunit.unit).symm.trans
      (congrArg Ring.inverse hunit.unit_spec)
  intro hmem
  have hnotunit : ¬ IsUnit (z • (1 : H →L[ℂ] H) - (T + K)) := by
    intro hu
    exact (spectrum.notMem_iff.mpr
      (by rwa [Algebra.algebraMap_eq_smul_one])) hmem
  have hnontriv : Nontrivial (H →L[ℂ] H) := by
    rcases subsingleton_or_nontrivial (H →L[ℂ] H) with hsub | hn
    · exact absurd (by
        rw [Subsingleton.elim (z • (1 : H →L[ℂ] H) - (T + K)) (1 : H →L[ℂ] H)]
        exact isUnit_one) hnotunit
    · exact hn
  have hpos : (0 : ℝ) < ‖((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖ :=
    Units.norm_pos _
  have hm_le : m ≤ ‖((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖⁻¹ := by
    rw [← inv_inv m]
    gcongr
    rw [hval]; exact hinvnorm
  have hlt : ‖(-K : H →L[ℂ] H)‖ < ‖((hunit.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)‖⁻¹ := by
    rw [norm_neg]; exact lt_of_lt_of_le hK hm_le
  have hu := (hunit.unit.add (-K) hlt).isUnit
  rw [Units.val_add, hunit.unit_spec] at hu
  refine hnotunit ?_
  have hrw : z • (1 : H →L[ℂ] H) - T + -K = z • (1 : H →L[ℂ] H) - (T + K) := by
    abel
  rwa [hrw] at hu

end Helpers

/-! ## 4. The central band and its spectral projection

The band is `(l - d/2, r + d/2)`, the inside of the canonical gap circle for
the configuration `[l, r]` with gaps of width `d` on both sides.  When the
real spectrum misses both open gaps, the indicator of the band is continuous
*on the spectrum*, so the band spectral projection is a continuous functional
calculus, exactly as in the one-sided `SpectralGapFormBounds`. -/

section Band

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The exterior of a two-sided gap configuration. -/
def gapExterior (l r d : ℝ) : Set ℝ := {x : ℝ | x ≤ l - d ∨ r + d ≤ x}

/-- The central band strictly inside the canonical gap circle. -/
def centralBand (l r d : ℝ) : Set ℝ := Set.Ioo (l - d / 2) (r + d / 2)

theorem measurableSet_centralBand (l r d : ℝ) :
    MeasurableSet (centralBand l r d) := measurableSet_Ioo

/-- The two-sided cutoff: the product of an upper and a lower one-sided
cutoff, written as a minimum since both take values in `[0,1]`. -/
def bandCutoff (l r d t : ℝ) : ℝ :=
  min (spectralGapCutoff r d t) (1 - spectralGapCutoff (l - d) d t)

theorem spectralGapCutoff_nonneg (a d t : ℝ) : 0 ≤ spectralGapCutoff a d t :=
  le_max_left _ _

theorem spectralGapCutoff_le_one (a d t : ℝ) : spectralGapCutoff a d t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem continuous_bandCutoff (l r d : ℝ) : Continuous (bandCutoff l r d) :=
  (continuous_spectralGapCutoff r d).min
    (continuous_const.sub (continuous_spectralGapCutoff (l - d) d))

theorem bandCutoff_nonneg (l r d t : ℝ) : 0 ≤ bandCutoff l r d t :=
  le_min (spectralGapCutoff_nonneg _ _ _)
    (by linarith [spectralGapCutoff_le_one (l - d) d t])

theorem bandCutoff_le_one (l r d t : ℝ) : bandCutoff l r d t ≤ 1 :=
  (min_le_left _ _).trans (spectralGapCutoff_le_one _ _ _)

theorem bandCutoff_eq_one {l r d t : ℝ} (hd : 0 < d) (ht : t ∈ Set.Icc l r) :
    bandCutoff l r d t = 1 := by
  have h1 : spectralGapCutoff r d t = 1 := spectralGapCutoff_eq_one hd ht.2
  have h2 : spectralGapCutoff (l - d) d t = 0 :=
    spectralGapCutoff_eq_zero hd (by linarith [ht.1])
  rw [bandCutoff, h1, h2]
  norm_num

theorem bandCutoff_eq_zero {l r d t : ℝ} (hd : 0 < d) (ht : t ∈ gapExterior l r d) :
    bandCutoff l r d t = 0 := by
  rcases ht with hlow | hhigh
  · have h2 : spectralGapCutoff (l - d) d t = 1 :=
      spectralGapCutoff_eq_one hd hlow
    rw [bandCutoff, h2, sub_self]
    exact min_eq_right (spectralGapCutoff_nonneg _ _ _)
  · have h1 : spectralGapCutoff r d t = 0 :=
      spectralGapCutoff_eq_zero hd hhigh
    rw [bandCutoff, h1]
    exact min_eq_left (by linarith [spectralGapCutoff_le_one (l - d) d t])

/-- The two-sided cutoff pulled back to the spectrum along the real part. -/
def bandSymbol (B : H →L[ℂ] H) (l r d : ℝ) : C(spectrum ℂ B, ℝ) :=
  ⟨fun w => bandCutoff l r d (TauCeti.BorelCalculus.reCoord w),
    (continuous_bandCutoff l r d).comp
      (Complex.continuous_re.comp continuous_subtype_val)⟩

omit [CompleteSpace H] in
@[simp] theorem bandSymbol_apply (B : H →L[ℂ] H) (l r d : ℝ) (w : spectrum ℂ B) :
    bandSymbol B l r d w = bandCutoff l r d (TauCeti.BorelCalculus.reCoord w) := rfl

variable (B : H →L[ℂ] H) (hB : IsSelfAdjointOperator B)

/-- **With a two-sided gap, the band spectral projection is a continuous
functional calculus.**  The two-sided cutoff agrees with the indicator of the
band at every point of the spectrum. -/
theorem boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom
    {l r d : ℝ} (hd : 0 < d)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d) :
    boundedSelfAdjointSpectralProjection B hB (centralBand l r d)
        (measurableSet_centralBand l r d) =
      cfcHom ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB).isStarNormal
        (TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d)) := by
  have h := boundedSelfAdjointSpectralProjection_eq_cfcL_of_agrees B hB
    (centralBand l r d) (measurableSet_centralBand l r d)
    (TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d)) ?_
  · rw [h]; rfl
  · intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    rcases hmem with hin | hout
    · have hband : w ∈ TauCeti.BorelCalculus.reCoord (T := B) ⁻¹' centralBand l r d := by
        refine ⟨by linarith [hin.1], by linarith [hin.2]⟩
      rw [Set.indicator_of_mem hband]
      simp only [TauCeti.BorelCalculus.ofRealLM_apply, bandSymbol_apply,
        bandCutoff_eq_one hd hin]
      norm_num
    · have hband : w ∉ TauCeti.BorelCalculus.reCoord (T := B) ⁻¹' centralBand l r d := by
        intro hmem'
        rcases hout with hlow | hhigh
        · exact absurd hmem'.1 (by simp; linarith)
        · exact absurd hmem'.2 (by simp; linarith)
      rw [Set.indicator_of_notMem hband]
      simp only [TauCeti.BorelCalculus.ofRealLM_apply, bandSymbol_apply,
        bandCutoff_eq_zero hd hout]
      norm_num

/-- The spectral subspace of the central band. -/
def centralBandSubspace {l r d : ℝ} : Submodule ℂ H :=
  boundedSelfAdjointSpectralSubspace B hB (centralBand l r d)
    (measurableSet_centralBand l r d)

instance centralBandSubspace_hasOrthogonalProjection {l r d : ℝ} :
    (centralBandSubspace B hB (l := l) (r := r) (d := d)).HasOrthogonalProjection :=
  boundedSelfAdjointSpectralSubspace_hasOrthogonalProjection B hB _ _

theorem centralBandSubspace_reduces {l r d : ℝ} :
    Reduces B (centralBandSubspace B hB (l := l) (r := r) (d := d)) :=
  boundedSelfAdjointSpectralSubspace_reduces B hB _ _

theorem starProjection_centralBandSubspace {l r d : ℝ} :
    (centralBandSubspace B hB (l := l) (r := r) (d := d)).starProjection =
      boundedSelfAdjointSpectralProjection B hB (centralBand l r d)
        (measurableSet_centralBand l r d) :=
  (boundedSelfAdjointSpectralProjection_eq_starProjection B hB _ _).symm

/-- **Sharp upper form bound on the band spectral subspace.** -/
theorem re_inner_le_of_mem_centralBandSubspace
    {l r d : ℝ} (hd : 0 < d)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {x : H} (hx : x ∈ centralBandSubspace B hB (l := l) (r := r) (d := d)) :
    RCLike.re ⟪B x, x⟫_ℂ ≤ r * ‖x‖ ^ 2 := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  set Epr : H →L[ℂ] H :=
    boundedSelfAdjointSpectralProjection B hB (centralBand l r d)
      (measurableSet_centralBand l r d) with hEdef
  have hEx : Epr x = x := by
    rw [hEdef, boundedSelfAdjointSpectralProjection_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  set g : C(spectrum ℂ B, ℝ) :=
    ⟨fun w => (r - TauCeti.BorelCalculus.reCoord w) *
        bandCutoff l r d (TauCeti.BorelCalculus.reCoord w),
      ((continuous_const.sub
        (Complex.continuous_re.comp continuous_subtype_val)).mul
        ((continuous_bandCutoff l r d).comp
          (Complex.continuous_re.comp continuous_subtype_val)))⟩ with hgdef
  have hgnonneg : ∀ w : spectrum ℂ B, 0 ≤ g w := by
    intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    show 0 ≤ (r - TauCeti.BorelCalculus.reCoord w) *
      bandCutoff l r d (TauCeti.BorelCalculus.reCoord w)
    rcases hmem with hin | hout
    · rw [bandCutoff_eq_one hd hin, mul_one]
      linarith [hin.2]
    · rw [bandCutoff_eq_zero hd hout, mul_zero]
  have hpos := TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg
    (a := B) hBsa.isStarNormal hgnonneg x
  have hsymbol :
      TauCeti.BorelCalculus.ofRealLM g =
        ((r : ℝ) : ℂ) • TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d) -
          ((ContinuousMap.id ℂ).restrict (spectrum ℂ B)) *
            TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d) := by
    ext w
    have hre := coe_reCoord B hB w
    -- Rewrite `g` through its value equation, not `hgdef`: rewriting to the bundled
    -- structure literal leaves a `ContinuousMap.mk` that `ContinuousMap.coe_mk` no longer
    -- reduces, and `push_cast` then cannot reach the real arithmetic inside it.
    have hgapp : ∀ v : spectrum ℂ B, g v =
        (r - TauCeti.BorelCalculus.reCoord v) *
          bandCutoff l r d (TauCeti.BorelCalculus.reCoord v) := fun _ => rfl
    simp only [TauCeti.BorelCalculus.ofRealLM_apply, hgapp,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.restrict_apply, ContinuousMap.id_apply, smul_eq_mul,
      bandSymbol_apply]
    rw [← hre]
    push_cast
    ring
  rw [hsymbol, map_sub, map_smul, map_mul, cfcHom_id,
    ← boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom B hB hd hgap] at hpos
  change 0 ≤ RCLike.re ⟪x, (((r : ℝ) : ℂ) • Epr - B * Epr) x⟫_ℂ at hpos
  have happly : (((r : ℝ) : ℂ) • Epr - B * Epr) x = ((r : ℝ) : ℂ) • x - B x := by
    simp only [_root_.sub_apply, _root_.smul_apply, mul_apply_eq_comp, hEx]
  rw [happly, inner_sub_right, map_sub, inner_smul_right] at hpos
  have hxx : RCLike.re (((r : ℝ) : ℂ) * ⟪x, x⟫_ℂ) = r * ‖x‖ ^ 2 := by
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  have hswap : RCLike.re ⟪x, B x⟫_ℂ = RCLike.re ⟪B x, x⟫_ℂ := inner_re_symm x (B x)
  rw [hxx, hswap] at hpos
  linarith

/-- **Sharp lower form bound on the band spectral subspace.** -/
theorem le_re_inner_of_mem_centralBandSubspace
    {l r d : ℝ} (hd : 0 < d)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {x : H} (hx : x ∈ centralBandSubspace B hB (l := l) (r := r) (d := d)) :
    l * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_ℂ := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  set Epr : H →L[ℂ] H :=
    boundedSelfAdjointSpectralProjection B hB (centralBand l r d)
      (measurableSet_centralBand l r d) with hEdef
  have hEx : Epr x = x := by
    rw [hEdef, boundedSelfAdjointSpectralProjection_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.mpr hx
  set g : C(spectrum ℂ B, ℝ) :=
    ⟨fun w => (TauCeti.BorelCalculus.reCoord w - l) *
        bandCutoff l r d (TauCeti.BorelCalculus.reCoord w),
      (((Complex.continuous_re.comp continuous_subtype_val).sub
        continuous_const).mul
        ((continuous_bandCutoff l r d).comp
          (Complex.continuous_re.comp continuous_subtype_val)))⟩ with hgdef
  have hgnonneg : ∀ w : spectrum ℂ B, 0 ≤ g w := by
    intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    show 0 ≤ (TauCeti.BorelCalculus.reCoord w - l) *
      bandCutoff l r d (TauCeti.BorelCalculus.reCoord w)
    rcases hmem with hin | hout
    · rw [bandCutoff_eq_one hd hin, mul_one]
      linarith [hin.1]
    · rw [bandCutoff_eq_zero hd hout, mul_zero]
  have hpos := TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg
    (a := B) hBsa.isStarNormal hgnonneg x
  have hsymbol :
      TauCeti.BorelCalculus.ofRealLM g =
        ((ContinuousMap.id ℂ).restrict (spectrum ℂ B)) *
            TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d) -
          ((l : ℝ) : ℂ) • TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d) := by
    ext w
    have hre := coe_reCoord B hB w
    -- Rewrite `g` through its value equation, not `hgdef`: rewriting to the bundled
    -- structure literal leaves a `ContinuousMap.mk` that `ContinuousMap.coe_mk` no longer
    -- reduces, and `push_cast` then cannot reach the real arithmetic inside it.
    have hgapp : ∀ v : spectrum ℂ B, g v =
        (TauCeti.BorelCalculus.reCoord v - l) *
          bandCutoff l r d (TauCeti.BorelCalculus.reCoord v) := fun _ => rfl
    simp only [TauCeti.BorelCalculus.ofRealLM_apply, hgapp,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.restrict_apply, ContinuousMap.id_apply, smul_eq_mul,
      bandSymbol_apply]
    rw [← hre]
    push_cast
    ring
  rw [hsymbol, map_sub, map_smul, map_mul, cfcHom_id,
    ← boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom B hB hd hgap] at hpos
  change 0 ≤ RCLike.re ⟪x, (B * Epr - ((l : ℝ) : ℂ) • Epr) x⟫_ℂ at hpos
  have happly : (B * Epr - ((l : ℝ) : ℂ) • Epr) x = B x - ((l : ℝ) : ℂ) • x := by
    simp only [_root_.sub_apply, _root_.smul_apply, mul_apply_eq_comp, hEx]
  rw [happly, inner_sub_right, map_sub, inner_smul_right] at hpos
  have hxx : RCLike.re (((l : ℝ) : ℂ) * ⟪x, x⟫_ℂ) = l * ‖x‖ ^ 2 := by
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  have hswap : RCLike.re ⟪x, B x⟫_ℂ = RCLike.re ⟪B x, x⟫_ℂ := inner_re_symm x (B x)
  rw [hxx, hswap] at hpos
  linarith

/-- The centre and the half-width of the configuration `[l, r]`. -/
def gapCenter (l r : ℝ) : ℝ := (l + r) / 2

/-- The shifted operator `B - centre`. -/
def shiftedOperator (l r : ℝ) : H →L[ℂ] H :=
  B - ((gapCenter l r : ℝ) : ℂ) • (1 : H →L[ℂ] H)

omit [CompleteSpace H] in
theorem shiftedOperator_apply (l r : ℝ) (x : H) :
    shiftedOperator B l r x = B x - ((gapCenter l r : ℝ) : ℂ) • x := by
  simp [shiftedOperator]

omit [CompleteSpace H] hB in
theorem inner_shiftedOperator_symm (hB' : IsSelfAdjointOperator B) (l r : ℝ) (u v : H) :
    ⟪u, shiftedOperator B l r v⟫_ℂ = ⟪shiftedOperator B l r u, v⟫_ℂ := by
  have h : ⟪B u, v⟫_ℂ = ⟪u, B v⟫_ℂ := hB' u v
  rw [shiftedOperator_apply, shiftedOperator_apply, inner_sub_right, inner_sub_left,
    inner_smul_right, inner_smul_left, Complex.conj_ofReal, h]

/-- **The complement of the band spectral subspace is bounded away from the
band.**  For `x` orthogonal to the band subspace,
`‖(B - centre) x‖ ≥ ((r - l)/2 + d) ‖x‖`: the symbol
`((t - c)² - K²)(1 - χ)` is nonnegative on the spectrum, because `1 - χ`
vanishes on `[l, r]` while `|t - c| ≥ K` on the exterior. -/
theorem norm_shiftedOperator_ge_of_mem_centralBandSubspace_orthogonal
    {l r d : ℝ} (hd : 0 < d) (hlr : l ≤ r)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {x : H} (hx : x ∈ (centralBandSubspace B hB (l := l) (r := r) (d := d))ᗮ) :
    ((r - l) / 2 + d) * ‖x‖ ≤ ‖shiftedOperator B l r x‖ := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  set c : ℝ := gapCenter l r with hc
  set K : ℝ := (r - l) / 2 + d with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  set Epr : H →L[ℂ] H :=
    boundedSelfAdjointSpectralProjection B hB (centralBand l r d)
      (measurableSet_centralBand l r d) with hEdef
  have hEx : Epr x = 0 := by
    rw [hEdef, boundedSelfAdjointSpectralProjection_eq_starProjection]
    exact (Submodule.starProjection_apply_eq_zero_iff _).mpr hx
  set g : C(spectrum ℂ B, ℝ) :=
    ⟨fun w => ((TauCeti.BorelCalculus.reCoord w - c) ^ 2 - K ^ 2) *
        (1 - bandCutoff l r d (TauCeti.BorelCalculus.reCoord w)),
      ((((Complex.continuous_re.comp continuous_subtype_val).sub
          continuous_const).pow 2).sub continuous_const).mul
        (continuous_const.sub
          ((continuous_bandCutoff l r d).comp
            (Complex.continuous_re.comp continuous_subtype_val)))⟩ with hgdef
  have hgnonneg : ∀ w : spectrum ℂ B, 0 ≤ g w := by
    intro w
    have hmem := hgap (reCoord_mem_realSpectrum B hB w)
    show 0 ≤ ((TauCeti.BorelCalculus.reCoord w - c) ^ 2 - K ^ 2) *
      (1 - bandCutoff l r d (TauCeti.BorelCalculus.reCoord w))
    rcases hmem with hin | hout
    · rw [bandCutoff_eq_one hd hin, sub_self, mul_zero]
    · rw [bandCutoff_eq_zero hd hout, sub_zero, mul_one]
      set t : ℝ := TauCeti.BorelCalculus.reCoord w with ht
      rcases hout with hlow | hhigh
      · have h1 : c - t ≥ K := by rw [hc, hK, gapCenter]; linarith
        nlinarith [hKpos]
      · have h1 : t - c ≥ K := by rw [hc, hK, gapCenter]; linarith
        nlinarith [hKpos]
  have hpos := TauCeti.BorelCalculus.inner_cfcHom_ofReal_nonneg
    (a := B) hBsa.isStarNormal hgnonneg x
  have hsymbol :
      TauCeti.BorelCalculus.ofRealLM g =
        ((((ContinuousMap.id ℂ).restrict (spectrum ℂ B) - ((c : ℝ) : ℂ) • 1) *
            ((ContinuousMap.id ℂ).restrict (spectrum ℂ B) - ((c : ℝ) : ℂ) • 1)) -
              ((K ^ 2 : ℝ) : ℂ) • 1) *
          (1 - TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d)) := by
    ext w
    have hre := coe_reCoord B hB w
    -- Rewrite `g` through its value equation, not `hgdef`: rewriting to the bundled
    -- structure literal leaves a `ContinuousMap.mk` that `ContinuousMap.coe_mk` no longer
    -- reduces, and `push_cast` then cannot reach the real arithmetic inside it.
    have hgapp : ∀ v : spectrum ℂ B, g v =
        ((TauCeti.BorelCalculus.reCoord v - c) ^ 2 - K ^ 2) *
          (1 - bandCutoff l r d (TauCeti.BorelCalculus.reCoord v)) := fun _ => rfl
    simp only [TauCeti.BorelCalculus.ofRealLM_apply, hgapp,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.one_apply, ContinuousMap.restrict_apply,
      ContinuousMap.id_apply, smul_eq_mul, bandSymbol_apply]
    rw [← hre]
    push_cast
    ring
  rw [hsymbol, map_mul, map_sub, map_sub, map_mul, map_sub, map_smul, map_smul,
    map_one, cfcHom_id,
    ← boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom B hB hd hgap] at hpos
  change 0 ≤ RCLike.re ⟪x,
    (((B - ((c : ℝ) : ℂ) • 1) * (B - ((c : ℝ) : ℂ) • 1) -
      ((K ^ 2 : ℝ) : ℂ) • 1) * (1 - Epr)) x⟫_ℂ at hpos
  set S : H →L[ℂ] H := shiftedOperator B l r with hSdef
  have hSeq : B - ((c : ℝ) : ℂ) • (1 : H →L[ℂ] H) = S := by
    rw [hSdef, shiftedOperator, hc]
  have happly : (((B - ((c : ℝ) : ℂ) • 1) * (B - ((c : ℝ) : ℂ) • 1) -
      ((K ^ 2 : ℝ) : ℂ) • 1) * (1 - Epr)) x = S (S x) - ((K ^ 2 : ℝ) : ℂ) • x := by
    simp only [mul_apply_eq_comp, _root_.sub_apply, _root_.smul_apply,
      one_apply_eq_self, hEx, sub_zero, hSeq]
  rw [happly, inner_sub_right, map_sub, inner_smul_right] at hpos
  have hquad : RCLike.re ⟪x, S (S x)⟫_ℂ = ‖S x‖ ^ 2 := by
    rw [hSdef, inner_shiftedOperator_symm B hB l r x (shiftedOperator B l r x)]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hxx : RCLike.re (((K ^ 2 : ℝ) : ℂ) * ⟪x, x⟫_ℂ) = K ^ 2 * ‖x‖ ^ 2 := by
    have hre : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  rw [hquad, hxx] at hpos
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [norm_nonneg (S x), norm_nonneg x, hKpos]

/-! ### The same two bounds for an arbitrary reducing subspace

The spectral hypotheses of the source theorem are `SpectrumIn` statements about
`Q`, `Qᗮ` and `P`, not statements about band spectral subspaces.  These two
lemmas convert them into the same shifted-operator bounds. -/

omit [CompleteSpace H] hB in
/-- The real part of the shifted quadratic form. -/
theorem re_inner_shiftedOperator (l r : ℝ) (y : H) :
    RCLike.re ⟪shiftedOperator B l r y, y⟫_ℂ =
      RCLike.re ⟪B y, y⟫_ℂ - gapCenter l r * ‖y‖ ^ 2 := by
  have hc : RCLike.re ((((gapCenter l r) : ℝ) : ℂ) * ⟪y, y⟫_ℂ) =
      gapCenter l r * ‖y‖ ^ 2 := by
    have hre : (⟪y, y⟫_ℂ).re = ‖y‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) y
    rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, hre]
    ring
  rw [shiftedOperator_apply, inner_sub_left, inner_smul_left,
    Complex.conj_ofReal, map_sub, hc]

include hB in
/-- **A reducing subspace with spectrum in `[l, r]` is a contraction after the
shift.**  The two-sided form bound of the restricted spectrum becomes a norm
bound by the Rayleigh description of the norm of a symmetric operator; the
ambient carrier is `(B - c) P_U`, so no restriction appears. -/
theorem norm_shiftedOperator_le_of_spectrumIn_Icc
    {U : Submodule ℂ H} [U.HasOrthogonalProjection] {l r : ℝ} (hlr : l ≤ r)
    (hU : Reduces B U) (hspec : SpectrumIn B U (Set.Icc l r))
    {x : H} (hx : x ∈ U) :
    ‖shiftedOperator B l r x‖ ≤ ((r - l) / 2) * ‖x‖ := by
  set S : H →L[ℂ] H := shiftedOperator B l r with hSdef
  set Pu : H →L[ℂ] H := U.starProjection with hPu
  have hrl : (0 : ℝ) ≤ (r - l) / 2 := by linarith
  have hcomm : Pu ∘L B = B ∘L Pu :=
    ContinuousLinearMap.starProjection_comp_comm_of_reduces B U hU
  have hScomm : ∀ y : H, Pu (S y) = S (Pu y) := by
    intro y
    have h := congrArg (fun T : H →L[ℂ] H => T y) hcomm
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [hSdef, shiftedOperator_apply, shiftedOperator_apply, map_sub, h,
      ContinuousLinearMap.map_smul]
  have hUform : ∀ y ∈ U, |RCLike.re ⟪S y, y⟫_ℂ| ≤ ((r - l) / 2) * ‖y‖ ^ 2 := by
    intro y hy
    have hup : RCLike.re ⟪y, B y⟫_ℂ ≤ r * ‖y‖ ^ 2 :=
      re_inner_le_of_spectrumIn_Iic hB (hspec.mono Set.Icc_subset_Iic_self) hy
    have hlo : l * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, B y⟫_ℂ :=
      le_re_inner_of_spectrumIn_Ici hB (hspec.mono Set.Icc_subset_Ici_self) hy
    have hswap : RCLike.re ⟪B y, y⟫_ℂ = RCLike.re ⟪y, B y⟫_ℂ :=
      (inner_re_symm y (B y)).symm
    rw [hSdef, re_inner_shiftedOperator B l r y, hswap, abs_le, gapCenter]
    constructor <;> linarith
  have hmemS : ∀ y : H, S (Pu y) ∈ U := by
    intro y
    rw [← hScomm]
    exact U.starProjection_apply_mem _
  have hsym : IsSelfAdjointOperator (S ∘L Pu) := by
    intro u v
    show ⟪S (Pu u), v⟫_ℂ = ⟪u, S (Pu v)⟫_ℂ
    have h1 : ⟪S (Pu u), v⟫_ℂ = ⟪Pu u, S v⟫_ℂ :=
      (inner_shiftedOperator_symm B hB l r (Pu u) v).symm
    have h2 : ⟪Pu u, S v⟫_ℂ = ⟪u, Pu (S v)⟫_ℂ := by
      rw [hPu]
      exact Submodule.inner_starProjection_left_eq_right U u (S v)
    rw [h1, h2, hScomm v]
  have hbound : ‖S ∘L Pu‖ ≤ (r - l) / 2 := by
    refine opNorm_le_of_abs_re_inner_le hsym hrl fun y => ?_
    have hzero : ⟪S (Pu y), Uᗮ.starProjection y⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal U (Uᗮ.starProjection y)).mp
        (Uᗮ.starProjection_apply_mem y) (S (Pu y)) (hmemS y)
    have hsplit : Pu y + Uᗮ.starProjection y = y := by
      rw [hPu, Submodule.starProjection_orthogonal_apply]; abel
    have hval : ⟪(S ∘L Pu) y, y⟫_ℂ = ⟪S (Pu y), Pu y⟫_ℂ := by
      show ⟪S (Pu y), y⟫_ℂ = _
      calc ⟪S (Pu y), y⟫_ℂ
          = ⟪S (Pu y), Pu y + Uᗮ.starProjection y⟫_ℂ := by rw [hsplit]
        _ = ⟪S (Pu y), Pu y⟫_ℂ + ⟪S (Pu y), Uᗮ.starProjection y⟫_ℂ :=
            inner_add_right _ _ _
        _ = ⟪S (Pu y), Pu y⟫_ℂ := by rw [hzero, add_zero]
    rw [hval]
    calc |RCLike.re ⟪S (Pu y), Pu y⟫_ℂ| ≤ ((r - l) / 2) * ‖Pu y‖ ^ 2 :=
        hUform _ (U.starProjection_apply_mem y)
      _ ≤ ((r - l) / 2) * ‖y‖ ^ 2 := by
          have h1 : ‖Pu y‖ ≤ ‖y‖ := by
            rw [hPu]; exact U.norm_starProjection_apply_le y
          have hsq : ‖Pu y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
            nlinarith [norm_nonneg (Pu y), norm_nonneg y]
          exact mul_le_mul_of_nonneg_left hsq hrl
  have hPx : Pu x = x := by
    rw [hPu]; exact Submodule.starProjection_eq_self_iff.mpr hx
  calc ‖S x‖ = ‖(S ∘L Pu) x‖ := by
        rw [ContinuousLinearMap.comp_apply, hPx]
    _ ≤ ‖S ∘L Pu‖ * ‖x‖ := (S ∘L Pu).le_opNorm x
    _ ≤ ((r - l) / 2) * ‖x‖ := mul_le_mul_of_nonneg_right hbound (norm_nonneg x)

include hB in
/-- **A reducing subspace with spectrum outside the two gaps is bounded below
after the shift.**  The compression is invertible at the centre with resolvent
norm at most `((r-l)/2 + d)⁻¹`, by the sharp self-adjoint distance-to-spectrum
bound. -/
theorem norm_shiftedOperator_ge_of_spectrumIn_gapExterior
    {U : Submodule ℂ H} [U.HasOrthogonalProjection] {l r d : ℝ}
    (hd : 0 < d) (hlr : l ≤ r)
    (hspec : SpectrumIn B U (gapExterior l r d))
    {x : H} (hx : x ∈ U) :
    ((r - l) / 2 + d) * ‖x‖ ≤ ‖shiftedOperator B l r x‖ := by
  letI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  set c : ℝ := gapCenter l r with hc
  set K : ℝ := (r - l) / 2 + d with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  set S1 : U →L[ℂ] U := compressOperator U B with hS1def
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  have hS1 : IsSelfAdjointOperator S1 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_compressOperator hBsa U)
  have hspecS1 : realSpectrum S1 ⊆ gapExterior l r d := by
    rw [hS1def, realSpectrum_compressOperator_eq_restrictedSpectrum B U hspec.invariant]
    exact hspec.subset
  have hsep : ∀ lam ∈ realSpectrum S1, K ≤ ‖((c : ℝ) : ℂ) - (lam : ℂ)‖ := by
    intro lam hlam
    have hmem := hspecS1 hlam
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rcases hmem with hlow | hhigh
    · rw [abs_of_nonneg (by rw [hc, gapCenter]; linarith)]
      rw [hc, hK, gapCenter]; linarith
    · rw [abs_of_nonpos (by rw [hc, gapCenter]; linarith)]
      rw [hc, hK, gapCenter]; linarith
  obtain ⟨hres, hbound⟩ :=
    complex_inResolventSet_and_norm_resolvent_le_inv_distance S1 hS1
      ((c : ℝ) : ℂ) K hKpos hsep
  have hcancel := resolventOperator_mul_cancel S1 hres
  set u : U := ⟨x, hx⟩ with hu
  have hcoe : ((S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u : H) =
      shiftedOperator B l r x := by
    have hrestr : S1 = B.restrict hspec.invariant := by
      rw [hS1def]; exact compressOperator_eq_restrict_of_invariant B U hspec.invariant
    rw [hrestr]
    show B x - ((c : ℝ) : ℂ) • x = _
    rw [shiftedOperator_apply, hc]
  have happly : (resolventOperator S1 ((c : ℝ) : ℂ))
      ((S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u) = u := by
    have h := congrArg (fun T : U →L[ℂ] U => T u) hcancel
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  have hnorm : ‖u‖ ≤ K⁻¹ * ‖(S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u‖ := by
    calc ‖u‖ = ‖(resolventOperator S1 ((c : ℝ) : ℂ))
          ((S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u)‖ := by rw [happly]
      _ ≤ ‖resolventOperator S1 ((c : ℝ) : ℂ)‖ *
            ‖(S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ K⁻¹ * ‖(S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u‖ := by
          have := norm_nonneg ((S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u)
          nlinarith [hbound]
  have hux : ‖u‖ = ‖x‖ := rfl
  have hSu : ‖(S1 - ((c : ℝ) : ℂ) • (1 : U →L[ℂ] U)) u‖ =
      ‖shiftedOperator B l r x‖ := by
    rw [← hcoe]; rfl
  rw [hux, hSu] at hnorm
  rw [inv_mul_eq_div, le_div_iff₀ hKpos] at hnorm
  linarith

omit [CompleteSpace H] hB in
theorem shiftedOperator_congr {l r l' r' : ℝ} (h : gapCenter l' r' = gapCenter l r) :
    shiftedOperator B l' r' = shiftedOperator B l r := by
  rw [shiftedOperator, shiftedOperator, h]

/-! ### Identifying the band subspace

`Π` is a continuous functional calculus of `B`, so it commutes with every
orthogonal projection onto a reducing subspace.  Together with the two
shifted-operator bounds that pins `Π` down. -/

include hB in
/-- The band spectral projection commutes with the projection onto any
reducing subspace. -/
theorem commute_starProjection_centralBandSubspace
    {l r d : ℝ} (hd : 0 < d)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection] (hU : Reduces B U) :
    Commute (centralBandSubspace B hB (l := l) (r := r) (d := d)).starProjection
      U.starProjection := by
  have hBsa : IsSelfAdjoint B :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hB
  have hBU : Commute B U.starProjection :=
    (ContinuousLinearMap.starProjection_comp_comm_of_reduces B U hU).symm
  have hstar : Commute (star B) U.starProjection := by rwa [hBsa.star_eq]
  have h := Commute.cfcHom (a := B) hBsa.isStarNormal hBU hstar
    (TauCeti.BorelCalculus.ofRealLM (bandSymbol B l r d))
  rwa [← boundedSelfAdjointSpectralProjection_centralBand_eq_cfcHom B hB hd hgap,
    ← starProjection_centralBandSubspace B hB] at h

include hB in
/-- The band spectral subspace carries spectrum inside `[l, r]`. -/
theorem spectrumIn_centralBandSubspace
    {l r d : ℝ} (hd : 0 < d)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d) :
    SpectrumIn B (centralBandSubspace B hB (l := l) (r := r) (d := d))
      (Set.Icc l r) := by
  have hinv : ∀ x ∈ centralBandSubspace B hB (l := l) (r := r) (d := d),
      B x ∈ centralBandSubspace B hB (l := l) (r := r) (d := d) :=
    (centralBandSubspace_reduces B hB).1
  have hup := DavisKahan1970.Section8.spectrumIn_Iic_of_re_inner_le
    (T := B) hinv (c := r)
    (fun x hx => re_inner_le_of_mem_centralBandSubspace B hB hd hgap hx)
  have hlo := DavisKahan1970.Section8.spectrumIn_Ici_of_le_re_inner
    (T := B) hinv (c := l)
    (fun x hx => le_re_inner_of_mem_centralBandSubspace B hB hd hgap hx)
  exact ⟨hinv, fun t ht => ⟨hlo.subset ht, hup.subset ht⟩⟩

include hB in
/-- **One half of the identification.**  A reducing subspace whose complement
is spectrally outside the two gaps contains the band spectral subspace. -/
theorem centralBandSubspace_le_of_spectrumIn_gapExterior
    {l r d : ℝ} (hd : 0 < d) (hlr : l ≤ r)
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection] (hU : Reduces B U)
    (hperp : SpectrumIn B Uᗮ (gapExterior l r d)) :
    centralBandSubspace B hB (l := l) (r := r) (d := d) ≤ U := by
  set R := centralBandSubspace B hB (l := l) (r := r) (d := d) with hR
  have hcomm := commute_starProjection_centralBandSubspace B hB hd hgap hU
  intro x hx
  set y : H := Uᗮ.starProjection x with hy
  have hyU : y ∈ Uᗮ := Uᗮ.starProjection_apply_mem x
  have hRx : R.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hyR : y ∈ R := by
    have hperpcomm : R.starProjection ∘L Uᗮ.starProjection =
        Uᗮ.starProjection ∘L R.starProjection := by
      have hsplit : Uᗮ.starProjection =
          (1 : H →L[ℂ] H) - U.starProjection := by
        ext z
        rw [Submodule.starProjection_orthogonal_apply]
        simp
      rw [hsplit]
      show R.starProjection * ((1 : H →L[ℂ] H) - U.starProjection) =
        ((1 : H →L[ℂ] H) - U.starProjection) * R.starProjection
      rw [mul_sub, sub_mul, mul_one, one_mul, hcomm.eq]
    have h := congrArg (fun T : H →L[ℂ] H => T x) hperpcomm
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [hy, ← Submodule.starProjection_eq_self_iff, h, hRx]
  have hupper : ‖shiftedOperator B l r y‖ ≤ ((r - l) / 2) * ‖y‖ :=
    norm_shiftedOperator_le_of_spectrumIn_Icc B hB hlr
      (centralBandSubspace_reduces B hB) (spectrumIn_centralBandSubspace B hB hd hgap)
      hyR
  have hlower : ((r - l) / 2 + d) * ‖y‖ ≤ ‖shiftedOperator B l r y‖ :=
    norm_shiftedOperator_ge_of_spectrumIn_gapExterior B hB hd hlr hperp hyU
  have hy0 : y = 0 := by
    by_contra hne
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hne
    nlinarith
  have hfix : U.starProjection x = x := by
    have hsum := U.starProjection_add_starProjection_orthogonal x
    rw [hy] at hy0
    rw [hy0, add_zero] at hsum
    exact hsum
  rw [← hfix]
  exact U.starProjection_apply_mem x

include hB in
/-- **The other half.**  A reducing subspace whose spectrum sits in a shorter
interval with the same centre is contained in the band spectral subspace. -/
theorem le_centralBandSubspace_of_spectrumIn_Icc
    {l r d l' r' : ℝ} (hd : 0 < d) (hlr : l ≤ r) (hlr' : l' ≤ r')
    (hgap : realSpectrum B ⊆ Set.Icc l r ∪ gapExterior l r d)
    {U : Submodule ℂ H} [U.HasOrthogonalProjection] (hU : Reduces B U)
    (hspec : SpectrumIn B U (Set.Icc l' r'))
    (hcen : gapCenter l' r' = gapCenter l r)
    (hsmall : (r' - l') / 2 < (r - l) / 2 + d) :
    U ≤ centralBandSubspace B hB (l := l) (r := r) (d := d) := by
  set R := centralBandSubspace B hB (l := l) (r := r) (d := d) with hR
  have hcomm := commute_starProjection_centralBandSubspace B hB hd hgap hU
  intro x hx
  set y : H := Rᗮ.starProjection x with hy
  have hyR : y ∈ Rᗮ := Rᗮ.starProjection_apply_mem x
  have hUx : U.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have hyU : y ∈ U := by
    have hperpcomm : U.starProjection ∘L Rᗮ.starProjection =
        Rᗮ.starProjection ∘L U.starProjection := by
      have hsplit : Rᗮ.starProjection = (1 : H →L[ℂ] H) - R.starProjection := by
        ext z
        rw [Submodule.starProjection_orthogonal_apply]
        simp
      rw [hsplit]
      show U.starProjection * ((1 : H →L[ℂ] H) - R.starProjection) =
        ((1 : H →L[ℂ] H) - R.starProjection) * U.starProjection
      rw [mul_sub, sub_mul, mul_one, one_mul, hcomm.eq]
    have h := congrArg (fun T : H →L[ℂ] H => T x) hperpcomm
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [hy, ← Submodule.starProjection_eq_self_iff, h, hUx]
  have hupper : ‖shiftedOperator B l r y‖ ≤ ((r' - l') / 2) * ‖y‖ := by
    have h := norm_shiftedOperator_le_of_spectrumIn_Icc B hB hlr' hU hspec hyU
    rwa [shiftedOperator_congr B hcen] at h
  have hlower : ((r - l) / 2 + d) * ‖y‖ ≤ ‖shiftedOperator B l r y‖ :=
    norm_shiftedOperator_ge_of_mem_centralBandSubspace_orthogonal B hB hd hlr hgap hyR
  have hy0 : y = 0 := by
    by_contra hne
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hne
    nlinarith
  have hfix : R.starProjection x = x := by
    have hsum := R.starProjection_add_starProjection_orthogonal x
    rw [hy] at hy0
    rw [hy0, add_zero] at hsum
    exact hsum
  rw [← hfix]
  exact R.starProjection_apply_mem x

end

end Band

/-! ## 5. The path, its spectral gap, and the moving band subspace -/

section Path

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The real spectrum of a self-adjoint operator splits over a reducing
decomposition. -/
theorem realSpectrum_subset_union_of_reduces
    {T : H →L[ℂ] H} (hT : IsSelfAdjointOperator T) {U : Submodule ℂ H}
    [U.HasOrthogonalProjection] (hU : Reduces T U) {p q : Set ℝ}
    (h0 : SpectrumIn T U p) (h1 : SpectrumIn T Uᗮ q) :
    realSpectrum T ⊆ p ∪ q := by
  letI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  letI : CompleteSpace (Uᗮ : Submodule ℂ H) :=
    (Uᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  rw [realSpectrum_eq_union_compressions_of_reduces T U hT hU]
  rintro x (hx | hx)
  · exact Or.inl (h0.subset (by
      rwa [realSpectrum_compressOperator_eq_restrictedSpectrum T U h0.invariant] at hx))
  · exact Or.inr (h1.subset (by
      rwa [realSpectrum_compressOperator_eq_restrictedSpectrum T Uᗮ h1.invariant] at hx))

omit [CompleteSpace H] in
theorem real_smul_eq_complex_smul (t : ℝ) (E : H →L[ℂ] H) :
    (t • E : H →L[ℂ] H) = ((t : ℂ)) • E := by
  ext x
  simp [Complex.coe_smul]

theorem isSelfAdjointOperator_path {A E : H →L[ℂ] H}
    (hA : IsSelfAdjointOperator A) (hE : IsSelfAdjointOperator E) (t : ℝ) :
    IsSelfAdjointOperator (A + t • E) := by
  rw [real_smul_eq_complex_smul]
  exact operatorPath_isSelfAdjointOperator hA hE t

/-- **The two gaps survive a small self-adjoint perturbation.**  Both open gaps
shrink by `gam` on each side, and they stay nonempty precisely because
`gam < delta / 2`.  This is the printed step
"`A(σ)`, being a perturbation of bound norm at most `γ`, has spectrum disjoint
from `(β - δ + γ, β - γ)`", proved by the Neumann series. -/
theorem realSpectrum_add_subset_of_gap
    {T K : H →L[ℂ] H} (hT : IsSelfAdjointOperator T)
    {alpha beta delta gam : ℝ} (hab : beta ≤ alpha) (_hdelta : 0 < delta)
    (hgam : 0 ≤ gam) (_hgamlt : gam < delta / 2) (hK : ‖K‖ ≤ gam)
    (hgap : realSpectrum T ⊆ Set.Icc beta alpha ∪ gapExterior beta alpha delta) :
    realSpectrum (T + K) ⊆
      Set.Icc (beta - gam) (alpha + gam) ∪
        gapExterior (beta - gam) (alpha + gam) (delta - 2 * gam) := by
  intro lam hlam
  by_contra hnot
  rw [Set.mem_union] at hnot
  have h1 : lam ∉ Set.Icc (beta - gam) (alpha + gam) := fun h => hnot (Or.inl h)
  have h2 : lam ∉ gapExterior (beta - gam) (alpha + gam) (delta - 2 * gam) :=
    fun h => hnot (Or.inr h)
  have h2' : beta - delta + gam < lam ∧ lam < alpha + delta - gam := by
    constructor
    · by_contra hcon
      exact h2 (Or.inl (by simp only [not_lt] at hcon; linarith))
    · by_contra hcon
      exact h2 (Or.inr (by simp only [not_lt] at hcon; linarith))
  have h1' : lam < beta - gam ∨ alpha + gam < lam := by
    rcases lt_or_ge lam (beta - gam) with h | h
    · exact Or.inl h
    · exact Or.inr (by
        by_contra hcon
        exact h1 ⟨h, le_of_not_gt hcon⟩)
  -- the ambient spectrum lies below `beta - delta` or above `beta`, and dually
  have hnorm : ∀ mu : ℝ, ‖((lam : ℝ) : ℂ) - ((mu : ℝ) : ℂ)‖ = |lam - mu| := by
    intro mu
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hcontra : ∀ m : ℝ, 0 < m → gam < m →
      (∀ mu ∈ realSpectrum T, m ≤ |lam - mu|) → False := by
    intro m hm hgm hsep
    have hsep' : ∀ mu ∈ realSpectrum T, m ≤ ‖((lam : ℝ) : ℂ) - ((mu : ℝ) : ℂ)‖ := by
      intro mu hmu; rw [hnorm]; exact hsep mu hmu
    exact notMem_spectrum_add_of_realSpectrum_dist hT hm hsep'
      (lt_of_le_of_lt hK hgm) hlam
  rcases h1' with hlow | hhigh
  · refine hcontra (min (beta - lam) (lam - (beta - delta))) ?_ ?_ ?_
    · exact lt_min (by linarith) (by linarith)
    · exact lt_min (by linarith) (by linarith)
    · intro mu hmu
      rcases hgap hmu with hin | hout
      · have : beta ≤ mu := hin.1
        rw [abs_of_nonpos (by linarith)]
        exact le_trans (min_le_left _ _) (by linarith)
      · rcases hout with hle | hge
        · rw [abs_of_nonneg (by linarith)]
          exact le_trans (min_le_right _ _) (by linarith)
        · rw [abs_of_nonpos (by linarith)]
          exact le_trans (min_le_left _ _) (by linarith)
  · refine hcontra (min (lam - alpha) (alpha + delta - lam)) ?_ ?_ ?_
    · exact lt_min (by linarith) (by linarith)
    · exact lt_min (by linarith) (by linarith)
    · intro mu hmu
      rcases hgap hmu with hin | hout
      · have : mu ≤ alpha := hin.2
        rw [abs_of_nonneg (by linarith)]
        exact le_trans (min_le_left _ _) (by linarith)
      · rcases hout with hle | hge
        · rw [abs_of_nonneg (by linarith)]
          exact le_trans (min_le_left _ _) (by linarith)
        · rw [abs_of_nonpos (by linarith)]
          exact le_trans (min_le_right _ _) (by linarith)

omit [CompleteSpace H] in
/-- Every point of the canonical gap circle is at distance at least `d / 2`
from the real spectrum. -/
theorem margin_le_dist_of_gap
    {T : H →L[ℂ] H} {l r d : ℝ} (hlr : l ≤ r) (hd : 0 < d)
    (hgap : realSpectrum T ⊆ Set.Icc l r ∪ gapExterior l r d)
    {z : ℂ} (hz : ‖z - ((gapCenter l r : ℝ) : ℂ)‖ = (r - l + d) / 2)
    {lam : ℝ} (hlam : lam ∈ realSpectrum T) :
    d / 2 ≤ ‖z - (lam : ℂ)‖ := by
  rw [gapCenter] at hz
  rcases hgap hlam with hin | hout
  · exact canonicalGapCircle_distance_interval hlr hz hin
  · exact canonicalGapCircle_distance_exterior hlr hd.le hz hout

/-- The canonical gap circle separates the real spectrum, selecting exactly the
central band. -/
theorem circleSeparates_of_gap
    {T : H →L[ℂ] H} (hT : IsSelfAdjointOperator T) {l r d : ℝ}
    (hlr : l ≤ r) (hd : 0 < d)
    (hgap : realSpectrum T ⊆ Set.Icc l r ∪ gapExterior l r d) :
    CircleSeparatesRealSpectrum T hT (centralBand l r d) (gapCenter l r)
      ((r - l + d) / 2) where
  radius_pos := by linarith
  contour_resolvent := by
    intro z hz
    exact not_mem_spectrum_of_inResolventSet T
      (complex_inResolventSet_of_distance T hT z (d / 2) (by linarith)
        fun lam hlam => margin_le_dist_of_gap hlr hd hgap hz hlam)
  inside_iff_mem := by
    intro x _
    rw [gapCenter]
    exact canonicalGapCircle_inside_iff (left := l) (right := r) (d := d) (x := x)

end Path

/-! ## 6. Theorem 8.2, the perturbation-norm branch selection -/

section Capstone

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative: the branch is
strictly inside the quarter turn.**

The hypotheses are exactly the printed ones.  `A` and `K` are self-adjoint
(`K` is the paper's `H`); `Q` is a reducing subspace of `A + K` carrying the
`sin 2Θ` spectral placement -- `Λ₀` inside `[β, α]`, `Λ₁` outside
`(β - δ, α + δ)`; `P` is a reducing subspace of `A` whose block `A₀` has
spectrum in the enlarged central interval `[β - δ/2, α + δ/2]`, which is the
extra hypothesis Theorem 8.2 adds; and `‖K‖ < δ/2` is the printed
perturbation alternative.

No contour, no continuation witness, no projection-Lipschitz constant and no
half-gap bridge appears among the hypotheses: they are all constructed inside
the proof, following the printed connectedness bootstrap.

The conclusion is the printed `Θ < π/4` in its directed form: every unit vector
of `P H` makes an angle strictly below `π/4` with `Q H`.  See the module
docstring for why the symmetric projector gap is *not* what the printed
statement can mean. -/
theorem theorem8_2_perturbationHalfGap_source
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hsmall : ‖K‖ < delta / 2) :
    directedGap P Q < Real.sqrt 2 / 2 := by
  classical
  set gam : ℝ := ‖K‖ with hgamdef
  have hgam0 : (0 : ℝ) ≤ gam := norm_nonneg K
  set l : ℝ := beta - gam with hldef
  set rr : ℝ := alpha + gam with hrdef
  set d : ℝ := delta - 2 * gam with hddef
  have hd : 0 < d := by rw [hddef]; linarith
  have hlr : l ≤ rr := by rw [hldef, hrdef]; linarith
  -- the path
  set A0 : H →L[ℂ] H := A + K with hA0def
  have hA0 : IsSelfAdjointOperator A0 := hA.add hK
  set E : H →L[ℂ] H := -K with hEdef
  have hE : IsSelfAdjointOperator E := by
    intro x y
    show ⟪-(K x), y⟫_ℂ = ⟪x, -(K y)⟫_ℂ
    have h : ⟪K x, y⟫_ℂ = ⟪x, K y⟫_ℂ := hK x y
    rw [inner_neg_left, inner_neg_right, h]
  have hBself : ∀ t : ℝ, IsSelfAdjointOperator (A0 + t • E) := fun t =>
    isSelfAdjointOperator_path hA0 hE t
  have hB0 : A0 + (0 : ℝ) • E = A0 := by simp
  have hB1 : A0 + (1 : ℝ) • E = A := by
    rw [one_smul, hA0def, hEdef]; abel
  have hnormE : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖(t • E : H →L[ℂ] H)‖ = t * gam := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, hEdef, norm_neg]
  -- the ambient gap at the start of the path, from the printed `sin 2Θ` data
  have hQred : Reduces A0 Q := ⟨hQ.invariant, hQperp.invariant⟩
  have hgap0 : realSpectrum A0 ⊆
      Set.Icc beta alpha ∪ gapExterior beta alpha delta :=
    realSpectrum_subset_union_of_reduces hA0 hQred hQ hQperp
  have hgapt : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      realSpectrum (A0 + t • E) ⊆ Set.Icc l rr ∪ gapExterior l rr d := by
    intro t ht
    refine realSpectrum_add_subset_of_gap hA0 hab hdelta hgam0 (by linarith) ?_ hgap0
    rw [hnormE t ht]
    nlinarith [ht.1, ht.2]
  -- the moving band subspace and its Riesz representation
  set cen : ℝ := gapCenter l rr with hcendef
  set rad : ℝ := (rr - l + d) / 2 with hraddef
  have hradpos : 0 < rad := by rw [hraddef]; linarith
  have hsep : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      CircleSeparatesRealSpectrum (A0 + t • E) (hBself t) (centralBand l rr d)
        cen rad := fun t ht => circleSeparates_of_gap (hBself t) hlr hd (hgapt t ht)
  set R : ℝ → Submodule ℂ H := fun t =>
    centralBandSubspace (A0 + t • E) (hBself t) (l := l) (r := rr) (d := d) with hRdef
  have hproj : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      (R t).starProjection = Frontier.circleRieszProjection (A0 + t • E) cen rad := by
    intro t ht
    show (centralBandSubspace (A0 + t • E) (hBself t)
      (l := l) (r := rr) (d := d)).starProjection = _
    rw [starProjection_centralBandSubspace]
    exact (circleRieszProjection_eq_boundedSelfAdjointSpectralProjection
      (A0 + t • E) (hBself t) (centralBand l rr d)
      (measurableSet_centralBand l rr d) cen rad (hsep t ht)).symm
  -- norm continuity of the moving projection
  have hunit : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ z : ℂ,
      ‖z - (cen : ℂ)‖ = rad → IsUnit (z • (1 : H →L[ℂ] H) - (A0 + t • E)) := by
    intro t ht z hz
    have hnot := (hsep t ht).contour_resolvent z hz
    have h := spectrum.notMem_iff.mp hnot
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hcontRiesz : ContinuousOn
      (fun t : ℝ => Frontier.circleRieszProjection (A0 + t • E) cen rad)
      (Set.Icc 0 1) :=
    continuous_circleRieszProjection_path A0 E cen rad hradpos.le hunit
  set f : ℝ → ℝ := fun t => directedGap (R t) Q with hfdef
  have hfeq : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f t = ‖Qᗮ.starProjection ∘L
        Frontier.circleRieszProjection (A0 + t • E) cen rad‖ := by
    intro t ht
    show ‖Qᗮ.starProjection ∘L (R t).starProjection‖ = _
    rw [hproj t ht]
  have hfcont : ContinuousOn f (Set.Icc 0 1) := by
    refine ContinuousOn.congr ?_ (fun t ht => hfeq t ht)
    exact (continuous_norm.comp
      (ContinuousLinearMap.compL ℂ H H H Qᗮ.starProjection).continuous).comp_continuousOn
      hcontRiesz
  -- the exterior placement, weakened to the shrunken configuration
  have hextmono : gapExterior beta alpha delta ⊆ gapExterior l rr d := by
    rintro x (hx | hx)
    · exact Or.inl (by rw [hldef, hddef]; linarith)
    · exact Or.inr (by rw [hrdef, hddef]; linarith)
  -- `R 0 ≤ Q`
  have hR0 : R 0 ≤ Q := by
    have hQperp' : SpectrumIn (A0 + (0 : ℝ) • E) Qᗮ (gapExterior l rr d) := by
      rw [hB0]; exact hQperp.mono hextmono
    have hQred' : Reduces (A0 + (0 : ℝ) • E) Q := by rw [hB0]; exact hQred
    exact centralBandSubspace_le_of_spectrumIn_gapExterior _ (hBself 0) hd hlr
      (hgapt 0 ⟨le_rfl, zero_le_one⟩) hQred' hQperp'
  have hf0 : f 0 = 0 := by
    show ‖Qᗮ.starProjection ∘L (R 0).starProjection‖ = 0
    rw [norm_eq_zero]
    ext x
    have hmem : (R 0).starProjection x ∈ Q := hR0 ((R 0).starProjection_apply_mem x)
    show Qᗮ.starProjection ((R 0).starProjection x) = 0
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.starProjection_eq_self_iff.mpr hmem, sub_self]
  -- `P ≤ R 1`
  have hR1 : P ≤ R 1 := by
    have hPred' : Reduces (A0 + (1 : ℝ) • E) P := by rw [hB1]; exact hPred
    have hP' : SpectrumIn (A0 + (1 : ℝ) • E) P
        (Set.Icc (beta - delta / 2) (alpha + delta / 2)) := by rw [hB1]; exact hP
    refine le_centralBandSubspace_of_spectrumIn_Icc _ (hBself 1) hd hlr
      (by linarith) (hgapt 1 ⟨zero_le_one, le_rfl⟩) hPred' hP' ?_ ?_
    · rw [gapCenter, gapCenter, hldef, hrdef]; ring
    · rw [hldef, hrdef, hddef]; linarith
  -- the bootstrap: closed quarter angle forces strict quarter angle
  have hboot : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → f t ≤ Real.sqrt 2 / 2 →
      f t < Real.sqrt 2 / 2 := by
    intro t ht hclose
    have hfinite : FiniteGapConfiguration A0 Q delta := ⟨beta, alpha, hab, hQ, hQperp⟩
    have hVred : Reduces (A0 + t • E) (R t) :=
      centralBandSubspace_reduces (A0 + t • E) (hBself t)
    have hsin := sinTwoTheta_perturbation (A := A0) (B := A0 + t • E)
      hA0 (U := Q) (V := R t) hQred hVred hdelta hfinite
    have hdiff : ‖(A0 + t • E) - A0‖ = t * gam := by
      rw [show (A0 + t • E) - A0 = t • E by abel]
      exact hnormE t ht
    rw [hdiff] at hsin
    have hlowbnd : Real.sqrt 2 * f t ≤ ‖sinTwoAngleOperator Q (R t)‖ :=
      sqrt_two_mul_directedGap_le_norm_sinTwoAngleOperator Q (R t) hclose
    have h2 : Real.sqrt 2 * f t * delta ≤ 2 * (t * gam) := by nlinarith [hsin, hlowbnd]
    have htg : t * gam ≤ gam := by nlinarith [ht.1, ht.2, hgam0]
    have hstrict : Real.sqrt 2 * f t * delta < delta := by nlinarith [h2, htg, hsmall]
    have hlt : Real.sqrt 2 * f t < 1 := by
      by_contra hcon
      rw [not_lt] at hcon
      nlinarith [hstrict, hdelta]
    have hs2 : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
      rw [show Real.sqrt 2 * (Real.sqrt 2 / 2) = Real.sqrt 2 ^ 2 / 2 by ring,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hpos2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [hlt, hs2, hpos2, hcon]
  -- connectedness: `f` never reaches the quarter turn
  have hall : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → f t < Real.sqrt 2 / 2 := by
    intro s hs
    by_contra hcon
    rw [not_lt] at hcon
    have hsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Icc_subset_Icc le_rfl hs.2
    have hcont' : ContinuousOn f (Set.Icc 0 s) := hfcont.mono hsub
    have hmem : Real.sqrt 2 / 2 ∈ Set.Icc (f 0) (f s) := by
      rw [hf0]
      exact ⟨sqrt_two_div_two_pos.le, hcon⟩
    obtain ⟨t, htmem, hft⟩ :=
      intermediate_value_Icc hs.1 hcont' hmem
    have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := hsub htmem
    have := hboot t ht1 (le_of_eq hft)
    rw [hft] at this
    exact lt_irrefl _ this
  -- transport to the source pair
  have hfixP : (R 1).starProjection ∘L P.starProjection = P.starProjection := by
    ext x
    show (R 1).starProjection (P.starProjection x) = P.starProjection x
    exact Submodule.starProjection_eq_self_iff.mpr
      (hR1 (P.starProjection_apply_mem x))
  have hle : directedGap P Q ≤ f 1 := by
    show ‖Qᗮ.starProjection ∘L P.starProjection‖ ≤
      ‖Qᗮ.starProjection ∘L (R 1).starProjection‖
    calc ‖Qᗮ.starProjection ∘L P.starProjection‖
        = ‖(Qᗮ.starProjection ∘L (R 1).starProjection) ∘L P.starProjection‖ := by
          rw [ContinuousLinearMap.comp_assoc, hfixP]
      _ ≤ ‖Qᗮ.starProjection ∘L (R 1).starProjection‖ * ‖P.starProjection‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Qᗮ.starProjection ∘L (R 1).starProjection‖ * 1 := by
          have := P.starProjection_norm_le
          nlinarith [norm_nonneg (Qᗮ.starProjection ∘L (R 1).starProjection)]
      _ = ‖Qᗮ.starProjection ∘L (R 1).starProjection‖ := mul_one _
  exact lt_of_le_of_lt hle (hall 1 ⟨zero_le_one, le_rfl⟩)

/-- **The same conclusion in the printed scalar form.**  The directed angle
from `P H` into `Q H` is strictly below `π / 4`. -/
theorem theorem8_2_perturbationHalfGap_source_angle_lt
    {A K : H →L[ℂ] H} (hA : IsSelfAdjointOperator A) (hK : IsSelfAdjointOperator K)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : Reduces A P)
    (hP : SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hsmall : ‖K‖ < delta / 2) :
    Real.arcsin (directedGap P Q) < Real.pi / 4 := by
  have h := theorem8_2_perturbationHalfGap_source hA hK hdelta hab hQ hQperp hPred hP
    hsmall
  have h0 : (0 : ℝ) ≤ directedGap P Q := norm_nonneg _
  rw [← DavisKahan1970.Section8.arcsin_sqrt_two_div_two]
  refine Real.arcsin_lt_arcsin (by linarith) h ?_
  have : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  linarith

end Capstone

end Section8
end Frontier
end Experimental
end DavisKahan
end TauCeti
