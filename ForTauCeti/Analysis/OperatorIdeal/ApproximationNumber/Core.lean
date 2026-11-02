/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import ForTauCeti.Analysis.InnerProductSpace.KyFan

/-!
# Approximation-number foundation and scalar-specific analytic endpoints

Approximation-number formulas use native `ContinuousLinearMap.singularValue`
with explicit real coercions; the former `approximationSingularValue` data alias
is retired. Shared scalar laws and finite-dimensional identification are consumed directly
from Tau Ceti. This module retains incomplete-space projection facts, strong-cutoff
convergence and the approximate orthonormal variational theorem. It intentionally does
not import the real localization module, so the real proof can depend on this
foundation without creating an import cycle.

The downstream ideal-family construction is `ForTauCeti.Analysis.OperatorIdeal.Family`;
the paper library's own aggregate is `DavisKahan/OperatorIdeal/ApproximationNumbers/`,
which is a different library and is not what a reader of this module wants.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean`.
* Extraction class: **moved**, not restated.  Statements, proofs and namespace are
  unchanged by the move; what changed is the enclosing library, and with it the
  build options the file is measured against.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c)
  2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports are `ForTauCeti` leaves and Mathlib.
-/

public section

namespace TauCeti
namespace ApproximationNumber

open scoped InnerProductSpace
open scoped Topology
open Filter

universe u v vF vG vH vE0 vF0 w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Strong operator convergence expressed pointwise. -/
@[expose]
def StronglyTendsto {ι : Type w} (T : ι → E →L[𝕜] E)
    (l : Filter ι) (S : E →L[𝕜] E) : Prop :=
  ∀ x, Tendsto (fun i => T i x) l (𝓝 (S x))

/-- Orthogonal projection predicate for bounded operators. -/
@[expose]
def IsOrthogonalProjectionMap (P : E →L[𝕜] E) : Prop :=
  P ∘L P = P ∧ P.IsSymmetric

omit [CompleteSpace E] in
/-- An orthogonal projection does not increase vector norms. -/
theorem IsOrthogonalProjectionMap.norm_apply_le
    {P : E →L[𝕜] E} (hP : IsOrthogonalProjectionMap P) (x : E) :
    ‖P x‖ ≤ ‖x‖ := by
  have hPP : P (P x) = P x := by
    have h := congrArg (fun T : E →L[𝕜] E => T x) hP.1
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hPQ : P (x - P x) = 0 := by
    rw [map_sub, hPP, sub_self]
  have horth : ⟪P x, x - P x⟫_𝕜 = 0 := by
    calc
      ⟪P x, x - P x⟫_𝕜 = ⟪x, P (x - P x)⟫_𝕜 :=
        hP.2 x (x - P x)
      _ = 0 := by simp only [hPQ, inner_zero_right]
  have hpyth : ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (P x) (x - P x) horth
    rw [show P x + (x - P x) = x by abel] at h
    rw [sq, sq, sq]
    linarith
  nlinarith [sq_nonneg ‖x - P x‖, norm_nonneg (P x), norm_nonneg x]

omit [CompleteSpace E] in
/-- An orthogonal projection has operator norm at most one. -/
theorem IsOrthogonalProjectionMap.norm_le_one
    {P : E →L[𝕜] E} (hP : IsOrthogonalProjectionMap P) :
    ‖P‖ ≤ 1 := by
  apply P.opNorm_le_bound zero_le_one
  intro x
  simpa only [one_mul] using hP.norm_apply_le x

/-- **A finite-dimensional operator norm is controlled by the values on a basis.**  With
`e` the coordinate isomorphism of `b`, `‖T‖ ≤ ‖e‖ * ∑ⱼ ‖T (b j)‖`.

Extracted from `tendsto_opNorm_zero_of_finiteDimensional`, whose whole content is that
this bound tends to zero: the estimate is a statement about one operator and does not
mention the net, so keeping it inside the limit argument hid a reusable fact behind a
thirty-line `calc`. -/
private theorem opNorm_le_norm_equivFun_mul_sum_basis
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (b : Module.Basis (Module.Basis.ofVectorSpaceIndex 𝕜 V) 𝕜 V)
    (T : V →L[𝕜] G) :
    ‖T‖ ≤ ‖b.equivFunL.toContinuousLinearMap‖ * ∑ j, ‖T (b j)‖ := by
  set e := b.equivFunL.toContinuousLinearMap with he
  refine T.opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)) fun x => ?_
  calc
    ‖T x‖ = ‖T (∑ j, b.repr x j • b j)‖ := by rw [b.sum_repr]
    _ = ‖∑ j, b.repr x j • T (b j)‖ := by rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ j, ‖b.repr x j • T (b j)‖ := norm_sum_le _ _
    _ = ∑ j, ‖b.repr x j‖ * ‖T (b j)‖ :=
      Finset.sum_congr rfl fun j _ => norm_smul _ _
    _ ≤ ∑ j, (‖e‖ * ‖x‖) * ‖T (b j)‖ := by
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖b.repr x j‖ = ‖e x j‖ := by rfl
        _ ≤ ‖e x‖ := norm_le_pi_norm (e x) j
        _ ≤ ‖e‖ * ‖x‖ := e.le_opNorm x
    _ = (‖e‖ * ‖x‖) * ∑ j, ‖T (b j)‖ := by rw [Finset.mul_sum]
    _ = (‖e‖ * ∑ j, ‖T (b j)‖) * ‖x‖ := by ring

/-- On a finite-dimensional source, pointwise convergence of bounded linear
maps to zero upgrades to convergence in operator norm. -/
theorem tendsto_opNorm_zero_of_finiteDimensional
    {ι : Type w} {l : Filter ι}
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : ι → V →L[𝕜] G)
    (hT : ∀ x, Tendsto (fun i => T i x) l (𝓝 0)) :
    Tendsto (fun i => ‖T i‖) l (𝓝 0) := by
  let b := Module.Basis.ofVectorSpace 𝕜 V
  let e := b.equivFunL.toContinuousLinearMap
  let C : ι → ℝ := fun i =>
    ‖e‖ * ∑ j, ‖T i (b j)‖
  have hsum : Tendsto (fun i => ∑ j, ‖T i (b j)‖) l (𝓝 0) := by
    have hsum' := tendsto_finsetSum Finset.univ
      (fun j _ => (hT (b j)).norm)
    simpa only [norm_zero, Finset.sum_const_zero] using hsum'
  have hC : Tendsto C l (𝓝 0) := by
    simpa only [C, mul_zero] using tendsto_const_nhds.mul hsum
  have hbound : ∀ i, ‖T i‖ ≤ C i := fun i => opNorm_le_norm_equivFun_mul_sum_basis b (T i)
  exact squeeze_zero (fun i => norm_nonneg (T i)) hbound hC

section StrongCutoff

variable {E₀ : Type vE0} {F₀ : Type vF0}
  [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]

omit [CompleteSpace F₀] [CompleteSpace E₀] in
/-- **Post-composing with an orthogonal projection cannot raise an approximation number.**
A projection is a contraction, so this is the ideal inequality with `‖P‖ ≤ 1` discharged.

Extracted from the convergence theorem below, where it was the `hUpper` half: it is a
statement about one projection with no net in sight, and it is the half a reader can check
without reading the localization argument. -/
theorem approximationSingularValue_comp_le_of_isOrthogonalProjection
    {P : E₀ →L[𝕜] E₀} (hP : IsOrthogonalProjectionMap P) (n : ℕ) (K : E₀ →L[𝕜] F₀) :
    ((K ∘L P).singularValue n : ℝ) ≤ (K.singularValue n : ℝ) := by
  have hnormNN : ‖P‖ ≤ (1 : ℝ) := by exact_mod_cast hP.norm_le_one
  have hNN : ((K ∘L P).singularValue n : ℝ) ≤ (K.singularValue n : ℝ) := by
    calc ((K ∘L P).singularValue n : ℝ) ≤ (K.singularValue n : ℝ) * ‖P‖ :=
          (NNReal.coe_le_coe.mpr (ContinuousLinearMap.singularValue_comp_le_right K P n))
      _ ≤ (K.singularValue n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hnormNN ((K.singularValue n).coe_nonneg)
      _ = (K.singularValue n : ℝ) := by rw [mul_one]
  exact_mod_cast hNN

omit [CompleteSpace F₀] [CompleteSpace E₀] in
/-- **Cutoff convergence.**  Along a net of orthogonal projections converging strongly to the
identity, every approximation number of `K ∘L P i` converges to the corresponding
approximation number of `K`.

Upper semicontinuity is free (`P i` is a contraction); the lower bound is where the
generalized Courant--Fischer localization enters. The native hypothesis
`TauCeti.HasMinMaxLowerBound` permits an incomplete source when localization is
supplied independently; complete sources obtain it from the accepted theorem. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_of_minMax
    (hlb : TauCeti.HasMinMaxLowerBound 𝕜 E₀ F₀)
    {ι : Type w} {P : ι → E₀ →L[𝕜] E₀} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E₀))
    (n : ℕ) (K : E₀ →L[𝕜] F₀) :
    Tendsto
      (fun i => ((K ∘L P i).singularValue n : ℝ))
      l (𝓝 ((K.singularValue n : ℝ))) := by
  -- Two halves, and they are not symmetric.  `hUpper` is the ideal inequality and is now a
  -- lemma of its own; `hLower` is the whole content: pick a coercive subspace `V` witnessing
  -- `r < aₙ(K)`, note `K ∘ P i` agrees with `K` on `V` in the limit because `V` is
  -- finite-dimensional (`tendsto_opNorm_zero_of_finiteDimensional`), and transport the
  -- coercivity.  The min--max hypothesis enters only in producing `V`.
  have hUpper : ∀ i,
      ((K ∘L P i).singularValue n : ℝ) ≤ (K.singularValue n : ℝ) :=
    fun i => approximationSingularValue_comp_le_of_isOrthogonalProjection (hPproj i) n K
  have hLower : ∀ r : ℝ,
      r < (K.singularValue n : ℝ) →
      ∀ᶠ i in l, r < ((K ∘L P i).singularValue n : ℝ) := by
    intro r hr
    by_cases hr0 : 0 ≤ r
    · obtain ⟨s, hrs, v, hv, hV⟩ := TauCeti.hasMinMaxLowerBound_iff.mp hlb K n hr0
        (by exact hr)
      let c : ℝ := (r + s) / 2
      have hrc : r < c := by dsimp only [c]; linarith
      have hcs : c < s := by dsimp only [c]; linarith
      have hc0 : 0 ≤ c := hr0.trans hrc.le
      let V : Submodule 𝕜 E₀ := Submodule.span 𝕜 (Set.range v)
      let b : Module.Basis (Fin (n + 1)) 𝕜 V := Module.Basis.span hv
      let : FiniteDimensional 𝕜 V := b.finiteDimensional_of_finite
      let D : ι → V →L[𝕜] F₀ := fun i =>
        (K ∘L P i ∘L V.subtypeL) - (K ∘L V.subtypeL)
      have hDpoint : ∀ x : V, Tendsto (fun i => D i x) l (𝓝 0) := by
        intro x
        have hKP : Tendsto (fun i => K (P i (V.subtypeL x))) l
            (𝓝 (K (V.subtypeL x))) :=
          (K.continuous.tendsto (V.subtypeL x)).comp (hP (V.subtypeL x))
        have hconst : Tendsto (fun _ : ι => K (V.subtypeL x)) l
            (𝓝 (K (V.subtypeL x))) := tendsto_const_nhds
        change Tendsto
          (fun i => K (P i (V.subtypeL x)) - K (V.subtypeL x))
          l (𝓝 0)
        simpa only [sub_self] using hKP.sub hconst
      have hDnorm : Tendsto (fun i => ‖D i‖) l (𝓝 0) :=
        tendsto_opNorm_zero_of_finiteDimensional D hDpoint
      have hsmall : ∀ᶠ i in l, ‖D i‖ < s - c :=
        hDnorm.eventually (Iio_mem_nhds (sub_pos.mpr hcs))
      filter_upwards [hsmall] with i hi
      have hcNN : c ≤ ((K ∘L P i).singularValue n : ℝ) := by
        apply (K ∘L P i).le_singularValue_of_linearIndependent hv
        intro x hxV
        have hDx : ‖D i ⟨x, hxV⟩‖ ≤ ‖D i‖ * ‖x‖ := (D i).le_opNorm ⟨x, hxV⟩
        have hDapply : D i ⟨x, hxV⟩ = K (P i x) - K x := rfl
        have htri : ‖K x‖ ≤ ‖K (P i x)‖ + ‖D i ⟨x, hxV⟩‖ := by
          rw [hDapply]
          have h := norm_sub_le (K (P i x)) (K (P i x) - K x)
          (convert h using 1; abel_nf)
        have hsx := hV x hxV
        change c * ‖x‖ ≤ ‖K (P i x)‖
        nlinarith [mul_le_mul_of_nonneg_right hi.le (norm_nonneg x)]
      have hcReal : c ≤ ((K ∘L P i).singularValue n : ℝ) := hcNN
      exact hrc.trans_le hcReal
    · have hrneg : r < 0 := lt_of_not_ge hr0
      filter_upwards [] with i
      exact hrneg.trans_le
        (((K ∘L P i).singularValue n).coe_nonneg)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlower := hLower
    ((K.singularValue n : ℝ) - ε) (by linarith)
  filter_upwards [hlower] with i hi
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · have := hUpper i
    linarith

/-- Cutoff convergence over `ℂ`. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_complex
    {E₀ : Type vE0} {F₀ : Type vF0}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    {ι : Type w} {P : ι → E₀ →L[ℂ] E₀} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℂ E₀))
    (n : ℕ) (K : E₀ →L[ℂ] F₀) :
    Tendsto
      (fun i => ((K ∘L P i).singularValue n : ℝ))
      l (𝓝 ((K.singularValue n : ℝ))) :=
  approximationSingularValue_comp_strongProjection_tendsto_of_minMax
    TauCeti.HasMinMaxLowerBound.of_completeSpace hPproj hP n K

end StrongCutoff

section KyFanStrongCutoff

variable {E₀ : Type vE0} {F₀ : Type vF0}
  [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀] [CompleteSpace E₀]
  [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀] [CompleteSpace F₀]

omit [CompleteSpace F₀] [CompleteSpace E₀] in
/-- Finite Ky Fan approximation gauges converge under strong orthogonal cutoffs: the
termwise statement summed over `Finset.range k`. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    (hlb : TauCeti.HasMinMaxLowerBound 𝕜 E₀ F₀)
    {ι : Type w} {P : ι → E₀ →L[𝕜] E₀} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E₀))
    (k : ℕ) (K : E₀ →L[𝕜] F₀) :
    Tendsto
      (fun i => ((K ∘L P i).kyFanGauge k : ℝ))
      l (𝓝 ((K.kyFanGauge k : ℝ))) := by
  simp only [ ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum]
  exact tendsto_finsetSum (Finset.range k)
    (fun n hn => approximationSingularValue_comp_strongProjection_tendsto_of_minMax
      hlb hPproj hP n K)

/-- Finite Ky Fan approximation gauges converge under complex strong
orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_complex
    {E₁ : Type vE0} {F₁ : Type vF0}
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {ι : Type w} {P : ι → E₁ →L[ℂ] E₁} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℂ E₁))
    (k : ℕ) (K : E₁ →L[ℂ] F₁) :
    Tendsto
      (fun i => ((K ∘L P i).kyFanGauge k : ℝ))
      l (𝓝 ((K.kyFanGauge k : ℝ))) :=
  kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    TauCeti.HasMinMaxLowerBound.of_completeSpace hPproj hP k K

end KyFanStrongCutoff

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Ky Fan gauge is approached by orthonormal pairings.**

For a bounded `K : E →L[𝕜] F` and any `ε > 0` there are orthonormal `k`-families `v` in `E`
and `u` in `F` with `kyFanApproximationGauge k K - ε ≤ re ∑ᵢ ⟪uᵢ, K vᵢ⟫`.  Together with the
reverse inequality this says the gauge is the *supremum* of those pairings.

Only the approximate form is available at this generality, and that is not a defect of the
proof: for a noncompact `K` the supremum need not be attained.  With `K` diagonal with
entries `1 - 1/n` on an orthonormal basis every approximation number equals `1`, so the gauge
is `k`, while `‖K x‖ < ‖x‖` for every `x ≠ 0` makes each pairing strictly smaller.

The two orthonormal families `x` and `y` are hypotheses, not conclusions: they say only that
`E` and `F` have room for `k` orthonormal vectors, without which no such `u`, `v` can exist.

The min--max lower bound `hlb` is what turns the ambient approximation numbers into
approximation numbers of a *finite-dimensional* restriction; Tau Ceti's finite-dimensional
rectangular Ky Fan principle
`LinearMap.exists_orthonormal_sum_inner_eq_kyFanSum` then attains them exactly, and
the compression is transported back along the inclusion and the projection, which are
isometric on the vectors involved. -/
theorem exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner
    [CompleteSpace F]
    (hlb : TauCeti.HasMinMaxLowerBound 𝕜 E F)
    (K : E →L[𝕜] F) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : Fin k → E} (hx : Orthonormal 𝕜 x)
    {y : Fin k → F} (hy : Orthonormal 𝕜 y) :
    ∃ (u : Fin k → F) (v : Fin k → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      (K.kyFanGauge k : ℝ) - ε ≤ RCLike.re (∑ i, ⟪u i, K (v i)⟫_𝕜) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    exact ⟨y, x, hy, hx, by
      simp [ hε.le]⟩
  set δ : ℝ := ε / k with hδdef
  have hδ : 0 < δ := div_pos hε (by exact_mod_cast hkpos)
  -- a finite set of vectors whose span nearly attains the `n`-th approximation number
  have hstep : ∀ n : ℕ, ∃ S : Finset E,
      (K.singularValue n : ℝ)
        < ((K ∘L (Submodule.span 𝕜 (S : Set E)).subtypeL).singularValue n : ℝ) + δ := by
    intro n
    obtain ⟨w, hw⟩ := hlb.exists_finiteRestrictionApproximationNumber_add_gt K n δ hδ
    refine ⟨Finset.image w Finset.univ, ?_⟩
    have hrange : ((Finset.image w Finset.univ : Finset E) : Set E) = Set.range w := by
      simp
    rw [hrange]
    exact hw
  choose S hS using hstep
  -- the finite-dimensional domain restriction
  set T : Finset E := (Finset.range k).biUnion S ∪ Finset.image x Finset.univ with hTdef
  set W : Submodule 𝕜 E := Submodule.span 𝕜 (T : Set E) with hWdef
  have : FiniteDimensional 𝕜 W := FiniteDimensional.span_of_finite 𝕜 T.finite_toSet
  have : CompleteSpace W := FiniteDimensional.complete 𝕜 W
  have hSW : ∀ n < k, Submodule.span 𝕜 ((S n : Set E)) ≤ W := by
    intro n hn
    refine Submodule.span_mono (Finset.coe_subset.mpr ?_)
    exact (Finset.subset_biUnion_of_mem S (Finset.mem_range.mpr hn)).trans
      Finset.subset_union_left
  have hgaugeW : (K.kyFanGauge k : ℝ) - ε
      ≤ ((K ∘L W.subtypeL).kyFanGauge k : ℝ) := by
    have hterm : ∀ n ∈ Finset.range k,
        (K.singularValue n : ℝ)
          < ((K ∘L W.subtypeL).singularValue n : ℝ) + δ := by
      intro n hn
      have hmono := ContinuousLinearMap.approximationNumber_restrict_mono K n
        (hSW n (Finset.mem_range.mp hn))
      have hn' := hS n
      linarith
    have hsum : ∑ n ∈ Finset.range k, (K.singularValue n : ℝ)
        ≤ (∑ n ∈ Finset.range k, ((K ∘L W.subtypeL).singularValue n : ℝ))
          + (k : ℝ) * δ := by
      have := Finset.sum_le_sum (fun n hn => (hterm n hn).le)
      simpa [Finset.sum_add_distrib, mul_comm] using this
    have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
    have hkδ : (k : ℝ) * δ = ε := by
      rw [hδdef]
      field_simp
    simp only [ ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum]
    rw [hkδ] at hsum
    linarith
  -- both restrictions have room for `k` orthonormal vectors
  have hxW : ∀ i, x i ∈ W := fun i => Submodule.subset_span (by simp [hTdef])
  have hx' : Orthonormal 𝕜 (fun i => (⟨x i, hxW i⟩ : W)) := by
    rw [orthonormal_iff_ite] at hx ⊢
    intro i j
    simpa [Submodule.coe_inner] using hx i j
  have hkW : k ≤ Module.finrank 𝕜 W := by
    simpa using hx'.linearIndependent.fintype_card_le_finrank
  set T' : Finset F := (T.image K) ∪ Finset.image y Finset.univ with hT'def
  set W' : Submodule 𝕜 F := Submodule.span 𝕜 (T' : Set F) with hW'def
  have : FiniteDimensional 𝕜 W' := FiniteDimensional.span_of_finite 𝕜 T'.finite_toSet
  have : CompleteSpace W' := FiniteDimensional.complete 𝕜 W'
  have hyW' : ∀ i, y i ∈ W' := fun i => Submodule.subset_span (by simp [hT'def])
  have hy' : Orthonormal 𝕜 (fun i => (⟨y i, hyW' i⟩ : W')) := by
    rw [orthonormal_iff_ite] at hy ⊢
    intro i j
    simpa [Submodule.coe_inner] using hy i j
  have hkW' : k ≤ Module.finrank 𝕜 W' := by
    simpa using hy'.linearIndependent.fintype_card_le_finrank
  have hKW : ∀ z : W, K (z : E) ∈ W' := by
    intro z
    have hle : W ≤ Submodule.comap (K : E →ₗ[𝕜] F) W' := by
      rw [hWdef]
      refine Submodule.span_le.mpr fun t ht => Submodule.subset_span ?_
      simp only [hT'def, Finset.coe_union, Set.mem_union, Finset.coe_image]
      exact Or.inl ⟨t, ht, rfl⟩
    exact hle z.2
  set K' : W →L[𝕜] W' := W'.orthogonalProjectionOnto ∘L (K ∘L W.subtypeL) with hK'def
  have hgaugeK' : (K'.kyFanGauge k : ℝ)
      = ((K ∘L W.subtypeL).kyFanGauge k : ℝ) :=
    (ContinuousLinearMap.kyFanGaugeReal_orthogonalProjectionOnto_comp_eq W' (K ∘L W.subtypeL) hKW k)
  obtain ⟨u', v', hu', hv', heq⟩ :=
    K'.toLinearMap.exists_orthonormal_sum_inner_eq_kyFanSum hkW hkW'
  have hbridge : K'.toLinearMap.kyFanSum k
      = (K'.kyFanGauge k : ℝ) :=
    (ContinuousLinearMap.kyFanGauge_eq_kyFanSum K'.toLinearMap.toContinuousLinearMap k).symm
  refine ⟨fun i => (u' i : F), fun i => (v' i : E), ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite] at hu' ⊢
    intro i j
    simpa [Submodule.coe_inner] using hu' i j
  · rw [orthonormal_iff_ite] at hv' ⊢
    intro i j
    simpa [Submodule.coe_inner] using hv' i j
  · have hpair : ∀ i, ⟪u' i, K'.toLinearMap (v' i)⟫_𝕜
        = ⟪((u' i : F)), K ((v' i : E))⟫_𝕜 := by
      intro i
      have hval : ((K'.toLinearMap (v' i) : W') : F) = W'.starProjection (K ((v' i : E))) := rfl
      rw [Submodule.coe_inner, hval, ← W'.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr (u' i).2]
    have hsum : (∑ i, ⟪((u' i : F)), K ((v' i : E))⟫_𝕜)
        = ∑ i, ⟪u' i, K'.toLinearMap (v' i)⟫_𝕜 :=
      Finset.sum_congr rfl fun i _ => (hpair i).symm
    have hreal : RCLike.re (∑ i, ⟪((u' i : F)), K ((v' i : E))⟫_𝕜)
        = ((K ∘L W.subtypeL).kyFanGauge k : ℝ) := by
      calc
        RCLike.re (∑ i, ⟪((u' i : F)), K ((v' i : E))⟫_𝕜)
            = RCLike.re (∑ i, ⟪u' i, K'.toLinearMap (v' i)⟫_𝕜) :=
              congrArg RCLike.re hsum
        _ = K'.toLinearMap.kyFanSum k := by rw [heq]; simp
        _ = (K'.kyFanGauge k : ℝ) := hbridge
        _ = ((K ∘L W.subtypeL).kyFanGauge k : ℝ) := hgaugeK'
    rw [hreal]
    exact hgaugeW

/-- **The Ky Fan gauge is approached by orthonormal pairings**, over `ℂ`.

The accepted converse min–max theorem supplies the localization input. -/
theorem exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner_complex
    {E₂ : Type vE0} {F₂ : Type vF0}
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (K : E₂ →L[ℂ] F₂) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    {x : Fin k → E₂} (hx : Orthonormal ℂ x)
    {y : Fin k → F₂} (hy : Orthonormal ℂ y) :
    ∃ (u : Fin k → F₂) (v : Fin k → E₂), Orthonormal ℂ u ∧ Orthonormal ℂ v ∧
      (K.kyFanGauge k : ℝ) - ε ≤ RCLike.re (∑ i, ⟪u i, K (v i)⟫_ℂ) :=
  exists_orthonormal_kyFanApproximationGauge_sub_le_re_sum_inner
    TauCeti.HasMinMaxLowerBound.of_completeSpace K hε hx hy

end ApproximationNumber
end TauCeti
