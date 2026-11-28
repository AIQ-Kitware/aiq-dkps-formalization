/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import ForTauCeti.Analysis.InnerProductSpace.KyFan

/-!
# Approximation numbers and strong cutoffs

Approximation-number formulas use native `ContinuousLinearMap.singularValue`
with explicit real coercions; the former `approximationSingularValue` data alias
is retired. Shared scalar laws and finite-dimensional identification are consumed directly
from Tau Ceti. This module retains incomplete-space projection facts, strong-cutoff
convergence and the approximate orthonormal variational theorem. The cutoff proof
uses TauCeti’s finite compression and converse min–max theorems.

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

open ContinuousLinearMap (toPointwiseConvergenceCLM)

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
  obtain ⟨C, _, hC⟩ := b.exists_opNorm_le (F := G)
  have hsum : Tendsto (fun i => ∑ j, ‖T i (b j)‖) l (𝓝 0) := by
    simpa only [norm_zero, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun j _ => (hT (b j)).norm)
  have hbound (i : ι) : ‖T i‖ ≤ C * ∑ j, ‖T i (b j)‖ :=
    hC (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (fun j => Finset.single_le_sum (f := fun j => ‖T i (b j)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ j))
  refine squeeze_zero (fun i => norm_nonneg (T i)) hbound ?_
  simpa only [mul_zero] using tendsto_const_nhds.mul hsum

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
    {P : E₀ →L[𝕜] E₀} (hP : P.toLinearMap.IsSymmetricProjection) (n : ℕ) (K : E₀ →L[𝕜] F₀) :
    ((K ∘L P).singularValue n : ℝ) ≤ (K.singularValue n : ℝ) := by
  obtain ⟨_, hP⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hP
  let V := LinearMap.range P.toLinearMap
  have hproj : P = V.starProjection := by
    ext x
    exact congrArg (fun Q : E₀ →ₗ[𝕜] E₀ => Q x) hP
  have hnorm : ‖P‖ ≤ 1 := by
    rw [hproj]
    exact V.starProjection_norm_le
  calc
    ((K ∘L P).singularValue n : ℝ) ≤ (K.singularValue n : ℝ) * ‖P‖ :=
      NNReal.coe_le_coe.mpr (ContinuousLinearMap.singularValue_comp_le_right K P n)
    _ ≤ (K.singularValue n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hnorm ((K.singularValue n).coe_nonneg)
    _ = (K.singularValue n : ℝ) := mul_one _

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
    (hPproj : ∀ i, (P i).toLinearMap.IsSymmetricProjection)
    (hP : Tendsto
      (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E₀ E₀ ∘ P) l
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E₀ E₀ (ContinuousLinearMap.id 𝕜 E₀))))
    (n : ℕ) (K : E₀ →L[𝕜] F₀) :
    Tendsto
      (fun i => ((K ∘L P i).singularValue n : ℝ))
      l (𝓝 ((K.singularValue n : ℝ))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨V, hV, hcomp⟩ := hlb.exists_singularValue_le_compression K (n + 1) (half_pos hε)
  let W := V.map K.toLinearMap
  let : FiniteDimensional 𝕜 W := by
    dsimp [W]
    infer_instance
  let S := W.orthogonalProjectionOnto.comp (K.comp V.subtypeL)
  let T (i : ι) := W.orthogonalProjectionOnto.comp ((K.comp (P i)).comp V.subtypeL)
  have hT : Tendsto T l (𝓝 S) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply tendsto_opNorm_zero_of_finiteDimensional
    intro x
    let L := W.orthogonalProjectionOnto.comp K
    have hPx : Tendsto (fun i => P i (x : E₀)) l (𝓝 (x : E₀)) :=
      PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp hP x
    have hL : Tendsto (fun i => L (P i x)) l (𝓝 (L x)) :=
      (L.continuous.tendsto (x : E₀)).comp hPx
    change Tendsto (fun i => L (P i x) - L x) l (𝓝 0)
    simpa only [sub_self] using hL.sub (tendsto_const_nhds (x := L x))
  have hSV := ((NNReal.continuous_coe.comp
    (ContinuousLinearMap.continuous_singularValue (E := V) (F := W) n)).tendsto S).comp hT
  have hp : (S.singularValue n : ℝ) - ε / 2 < (S.singularValue n : ℝ) :=
    sub_lt_self _ (half_pos hε)
  filter_upwards [hSV.eventually (Ioi_mem_nhds hp)] with i hi
  have hlo : (K.singularValue n : ℝ) ≤ (S.singularValue n : ℝ) + ε / 2 :=
    hcomp n n.lt_succ_self
  have hle : ((T i).singularValue n : ℝ) ≤ ((K ∘L P i).singularValue n : ℝ) :=
    NNReal.coe_le_coe.mpr
      (ContinuousLinearMap.singularValue_orthogonalProjectionOnto_comp_comp_subtypeL_le
        W V (K ∘L P i) n)
  have hhi := approximationSingularValue_comp_le_of_isOrthogonalProjection (hPproj i) n K
  have hεi : (S.singularValue n : ℝ) - ε / 2 < ((T i).singularValue n : ℝ) := hi
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

omit [CompleteSpace F₀] in
/-- Strong orthogonal cutoffs preserve approximation numbers in the limit when
the source is complete. -/
theorem approximationSingularValue_comp_strongProjection_tendsto
    {ι : Type w} {P : ι → E₀ →L[𝕜] E₀} {l : Filter ι}
    (hPproj : ∀ i, (P i).toLinearMap.IsSymmetricProjection)
    (hP : Tendsto
      (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E₀ E₀ ∘ P) l
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E₀ E₀ (ContinuousLinearMap.id 𝕜 E₀))))
    (n : ℕ) (K : E₀ →L[𝕜] F₀) :
    Tendsto (fun i => ((K ∘L P i).singularValue n : ℝ)) l (𝓝 (K.singularValue n : ℝ)) :=
  approximationSingularValue_comp_strongProjection_tendsto_of_minMax
    TauCeti.HasMinMaxLowerBound.of_completeSpace hPproj hP n K

omit [CompleteSpace F₀] [CompleteSpace E₀] in
/-- Finite Ky Fan approximation gauges converge under strong orthogonal cutoffs: the
termwise statement summed over `Finset.range k`. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    (hlb : TauCeti.HasMinMaxLowerBound 𝕜 E₀ F₀)
    {ι : Type w} {P : ι → E₀ →L[𝕜] E₀} {l : Filter ι}
    (hPproj : ∀ i, (P i).toLinearMap.IsSymmetricProjection)
    (hP : Tendsto
      (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E₀ E₀ ∘ P) l
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E₀ E₀ (ContinuousLinearMap.id 𝕜 E₀))))
    (k : ℕ) (K : E₀ →L[𝕜] F₀) :
    Tendsto
      (fun i => ((K ∘L P i).kyFanGauge k : ℝ))
      l (𝓝 ((K.kyFanGauge k : ℝ))) := by
  simp only [ ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum]
  exact tendsto_finsetSum (Finset.range k)
    (fun n hn => approximationSingularValue_comp_strongProjection_tendsto_of_minMax
      hlb hPproj hP n K)

omit [CompleteSpace F₀] in
/-- Strong orthogonal cutoffs preserve finite Ky Fan gauges in the limit when
the source is complete. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto
    {ι : Type w} {P : ι → E₀ →L[𝕜] E₀} {l : Filter ι}
    (hPproj : ∀ i, (P i).toLinearMap.IsSymmetricProjection)
    (hP : Tendsto
      (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E₀ E₀ ∘ P) l
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E₀ E₀ (ContinuousLinearMap.id 𝕜 E₀))))
    (k : ℕ) (K : E₀ →L[𝕜] F₀) :
    Tendsto (fun i => ((K ∘L P i).kyFanGauge k : ℝ)) l (𝓝 (K.kyFanGauge k : ℝ)) :=
  kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    TauCeti.HasMinMaxLowerBound.of_completeSpace hPproj hP k K

/-- Strong orthogonal cutoffs on the target preserve finite Ky Fan gauges
in the limit. This follows by applying the source-cutoff theorem to the adjoint. -/
theorem kyFanApproximationGauge_left_comp_strongProjection_tendsto
    {ι : Type w} {P : ι → E₀ →L[𝕜] E₀} {l : Filter ι}
    (hPproj : ∀ i, (P i).toLinearMap.IsSymmetricProjection)
    (hP : Tendsto
      (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E₀ E₀ ∘ P) l
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) E₀ E₀ (ContinuousLinearMap.id 𝕜 E₀))))
    (k : ℕ) (K : F₀ →L[𝕜] E₀) :
    Tendsto (fun i => ((P i ∘L K).kyFanGauge k : ℝ)) l (𝓝 (K.kyFanGauge k : ℝ)) := by
  have hright := kyFanApproximationGauge_comp_strongProjection_tendsto hPproj hP k K.adjoint
  have hpoint (i : ι) :
      ((K.adjoint ∘L P i).kyFanGauge k : ℝ) = ((P i ∘L K).kyFanGauge k : ℝ) := by
    rw [← ContinuousLinearMap.kyFanGauge_adjoint (P i ∘L K) k,
      ContinuousLinearMap.adjoint_comp, (hPproj i).isSymmetric.clm_adjoint_eq]
  simpa only [hpoint, ContinuousLinearMap.kyFanGauge_adjoint] using hright

end StrongCutoff

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Ky Fan gauge is approached by orthonormal pairings.**

The given families certify that both spaces admit `k` orthonormal vectors.
The converse min–max theorem supplies a finite compression approximating the
first `k` singular values. Enlarging its source and target to contain the
given families lets the finite rectangular Ky Fan principle produce the
desired pairing. The approximation also applies when a noncompact operator's
supremum is unattained. -/
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
    exact ⟨y, x, hy, hx, by simp [hε.le]⟩
  let δ : ℝ := ε / k
  have hδ : 0 < δ := div_pos hε (by exact_mod_cast hkpos)
  obtain ⟨V, hVfinite, hV⟩ := hlb.exists_singularValue_le_compression K k hδ
  let W := V ⊔ Submodule.span 𝕜 (Set.range x)
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range x)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range x)
  have : FiniteDimensional 𝕜 W := by
    dsimp [W]
    infer_instance
  have hxW (i : Fin k) : x i ∈ W :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_range_self i))
  have hkW : k ≤ Module.finrank 𝕜 W := by
    simpa using (hx.codRestrict W hxW).linearIndependent.fintype_card_le_finrank
  have hterm (n : ℕ) (hn : n ∈ Finset.range k) :
      (K.singularValue n : ℝ) ≤ ((K ∘L W.subtypeL).singularValue n : ℝ) + δ := by
    let L := V.map K.toLinearMap
    have hrange (z : V) : (K ∘L V.subtypeL) z ∈ L :=
      Submodule.mem_map_of_mem z.property
    have hcomp := hV n (Finset.mem_range.mp hn)
    rw [ContinuousLinearMap.approximationNumber_orthogonalProjectionOnto_comp_eq
      L (K ∘L V.subtypeL) hrange n] at hcomp
    exact hcomp.trans (add_le_add
      (ContinuousLinearMap.approximationNumber_restrict_mono K n (le_sup_left : V ≤ W)) le_rfl)
  have hgaugeW : (K.kyFanGauge k : ℝ) - ε
      ≤ ((K ∘L W.subtypeL).kyFanGauge k : ℝ) := by
    have hsum := Finset.sum_le_sum hterm
    have hkδ : (k : ℝ) * δ = ε := by
      dsimp [δ]
      field_simp
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      hkδ] at hsum
    simp only [ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum]
    exact sub_le_iff_le_add.mpr hsum
  let W' := W.map K.toLinearMap ⊔ Submodule.span 𝕜 (Set.range y)
  have : FiniteDimensional 𝕜 (Submodule.span 𝕜 (Set.range y)) :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range y)
  have : FiniteDimensional 𝕜 W' := by
    dsimp [W']
    infer_instance
  have hyW' (i : Fin k) : y i ∈ W' :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_range_self i))
  have hkW' : k ≤ Module.finrank 𝕜 W' := by
    simpa using (hy.codRestrict W' hyW').linearIndependent.fintype_card_le_finrank
  have hKW (z : W) : K (z : E) ∈ W' :=
    Submodule.mem_sup_left (Submodule.mem_map_of_mem z.property)
  let K' : W →L[𝕜] W' := W'.orthogonalProjectionOnto ∘L (K ∘L W.subtypeL)
  have hgaugeK' : (K'.kyFanGauge k : ℝ)
      = ((K ∘L W.subtypeL).kyFanGauge k : ℝ) :=
    (ContinuousLinearMap.kyFanGaugeReal_orthogonalProjectionOnto_comp_eq W' (K ∘L W.subtypeL) hKW k)
  obtain ⟨u', v', hu', hv', heq⟩ :=
    K'.toLinearMap.exists_orthonormal_sum_inner_eq_kyFanSum hkW hkW'
  have hbridge : K'.toLinearMap.kyFanSum k
      = (K'.kyFanGauge k : ℝ) :=
    (ContinuousLinearMap.kyFanGauge_eq_kyFanSum K'.toLinearMap.toContinuousLinearMap k).symm
  refine ⟨fun i => (u' i : F), fun i => (v' i : E),
    W'.subtypeₗᵢ.orthonormal_comp_iff.mpr hu', W.subtypeₗᵢ.orthonormal_comp_iff.mpr hv', ?_⟩
  have hpair : ∀ i, ⟪u' i, K'.toLinearMap (v' i)⟫_𝕜
      = ⟪((u' i : F)), K ((v' i : E))⟫_𝕜 := by
    intro i
    have hval : ((K'.toLinearMap (v' i) : W') : F) = W'.starProjection (K ((v' i : E))) := rfl
    rw [Submodule.coe_inner, hval, Submodule.starProjection_eq_self_iff.mpr (hKW (v' i))]
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
