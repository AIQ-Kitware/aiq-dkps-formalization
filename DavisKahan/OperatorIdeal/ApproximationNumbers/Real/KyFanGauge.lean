/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/

import DavisKahan.OperatorIdeal.ApproximationNumbers.Real.Threshold

/-!
# Strong cutoffs and finite Ky Fan gauges over real Hilbert spaces

From the real finite-dimensional localization theorem, this module proves
convergence of real approximation singular values and finite Ky Fan gauges under
strongly convergent orthogonal cutoffs, together with the real infinite-
dimensional Ky Fan triangle inequality:

* `approximationSingularValue_comp_strongProjection_tendsto_real`;
* `kyFanApproximationGauge_comp_strongProjection_tendsto_real`;
* `kyFanApproximationGauge_add_le_real`.
-/

open scoped InnerProductSpace ComplexConjugate Topology

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta
namespace ApproximationNumbersReal

open Module (finrank)
open Filter
open Foundation
open Foundation.RealComplexification

noncomputable section

universe v vF vG vH w

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! ## Strong cutoffs and finite Ky Fan gauges over real Hilbert spaces -/

/-- Real-Hilbert-space cutoff convergence, obtained from finite-dimensional
localization and uniform convergence on each witness subspace. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_real
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (n : ℕ) (K : E →L[ℝ] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) := by
  have hUpper : ∀ i,
      approximationSingularValue n (K ∘L P i) ≤
        approximationSingularValue n K := by
    intro i
    have hnormNN : ‖P i‖ ≤ (1 : ℝ) := by
      exact_mod_cast (hPproj i).norm_le_one
    have hNN : (K ∘L P i).approximationNumber n ≤
        K.approximationNumber n := by
      calc
        (K ∘L P i).approximationNumber n
            ≤ K.approximationNumber n * ‖P i‖ :=
          K.approximationNumber_comp_le_mul_norm (P i) n
        _ ≤ K.approximationNumber n * 1 :=
          mul_le_mul_of_nonneg_left hnormNN (K.approximationNumber_nonneg n)
        _ = K.approximationNumber n := by rw [mul_one]
    exact_mod_cast hNN
  have hLower : ∀ r : ℝ,
      r < approximationSingularValue n K →
      ∀ᶠ i in l, r < approximationSingularValue n (K ∘L P i) := by
    intro r hr
    by_cases hr0 : 0 ≤ r
    · obtain ⟨s, hrs, v, hv, hV⟩ :=
        exists_linearIndependent_lowerBound_of_lt_approximationNumber_real
          K n hr0 hr
      let c : ℝ := (r + s) / 2
      have hrc : r < c := by dsimp only [c]; linarith
      have hcs : c < s := by dsimp only [c]; linarith
      have hc0 : 0 ≤ c := hr0.trans hrc.le
      let V : Submodule ℝ E := Submodule.span ℝ (Set.range v)
      let b : Module.Basis (Fin (n + 1)) ℝ V := Module.Basis.span hv
      letI : FiniteDimensional ℝ V := b.finiteDimensional_of_finite
      let D : ι → V →L[ℝ] F := fun i =>
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
      have hcNN : c ≤
          (K ∘L P i).approximationNumber n := by
        apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
          (K ∘L P i) n v hv
        intro x hxV hxNorm
        have hDx : ‖D i ⟨x, hxV⟩‖ ≤ ‖D i‖ := by
          have h := (D i).le_opNorm ⟨x, hxV⟩
          change ‖D i ⟨x, hxV⟩‖ ≤ ‖D i‖ * ‖x‖ at h
          rw [hxNorm, mul_one] at h
          exact h
        have hDapply : D i ⟨x, hxV⟩ = K (P i x) - K x := by
          rfl
        have htri : ‖K x‖ ≤ ‖K (P i x)‖ + ‖D i ⟨x, hxV⟩‖ := by
          rw [hDapply]
          have h := norm_sub_le (K (P i x)) (K (P i x) - K x)
          convert h using 1 <;> abel
        have hsx : s ≤ ‖K x‖ := by
          have := hV x hxV
          simpa only [hxNorm, mul_one] using this
        change c ≤ ‖K (P i x)‖
        linarith
      have hcReal : c ≤ approximationSingularValue n (K ∘L P i) := hcNN
      exact hrc.trans_le hcReal
    · have hrneg : r < 0 := lt_of_not_ge hr0
      filter_upwards [] with i
      exact hrneg.trans_le
        (approximationSingularValue_nonneg n (K ∘L P i))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlower := hLower
    (approximationSingularValue n K - ε) (by linarith)
  filter_upwards [hlower] with i hi
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · have := hUpper i
    linarith

/-- Real finite Ky Fan approximation gauges converge under strong orthogonal
cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_real
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (k : ℕ) (K : E →L[ℝ] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  simp only [kyFanApproximationGauge]
  exact tendsto_finsetSum (Finset.range k)
    (fun n _ => approximationSingularValue_comp_strongProjection_tendsto_real
      hPproj hP n K)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Restricting a real operator to a larger source subspace can only increase
its approximation singular values. -/
theorem approximationSingularValue_restrict_mono_real
    (T : E →L[ℝ] F) (n : ℕ) {U V : Submodule ℝ E}
    (hUV : U ≤ V) :
    approximationSingularValue n (T ∘L U.subtypeL) ≤
      approximationSingularValue n (T ∘L V.subtypeL) := by
  let J : U →L[ℝ] V :=
    (Submodule.inclusion hUV).mkContinuous 1 (fun x => by
      change ‖((x : U) : E)‖ ≤ 1 * ‖x‖
      simp)
  have hJnorm : ‖J‖ ≤ (1 : ℝ) := by
    exact_mod_cast (J.opNorm_le_bound zero_le_one fun x => by
      change ‖((x : U) : E)‖ ≤ 1 * ‖x‖
      simp)
  have hcomp : T ∘L U.subtypeL = (T ∘L V.subtypeL) ∘L J := by
    ext x
    rfl
  have hNN : (T ∘L U.subtypeL).approximationNumber n ≤
      (T ∘L V.subtypeL).approximationNumber n := by
    rw [hcomp]
    calc
      ((T ∘L V.subtypeL) ∘L J).approximationNumber n
          ≤ (T ∘L V.subtypeL).approximationNumber n * ‖J‖ :=
        (T ∘L V.subtypeL).approximationNumber_comp_le_mul_norm J n
      _ ≤ (T ∘L V.subtypeL).approximationNumber n * 1 :=
        mul_le_mul_of_nonneg_left hJnorm (ContinuousLinearMap.approximationNumber_nonneg _ _)
      _ = (T ∘L V.subtypeL).approximationNumber n := by rw [mul_one]
  change ((T ∘L U.subtypeL).approximationNumber n : ℝ) ≤
    ((T ∘L V.subtypeL).approximationNumber n : ℝ)
  exact_mod_cast hNN

/-- Projecting the codomain onto a real subspace containing the operator range
preserves every approximation singular value. -/
theorem approximationSingularValue_orthogonalProjectionOnto_comp_eq_real
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (W : Submodule ℝ G) [W.HasOrthogonalProjection]
    (A : V →L[ℝ] G) (hA : ∀ x, A x ∈ W) (n : ℕ) :
    approximationSingularValue n (W.orthogonalProjectionOnto ∘L A) =
      approximationSingularValue n A := by
  let AW : V →L[ℝ] W := W.orthogonalProjectionOnto ∘L A
  have hfactor : W.subtypeL ∘L AW = A := by
    ext x
    change W.starProjection (A x) = A x
    exact W.starProjection_eq_self_iff.mpr (hA x)
  have hproj : ‖W.orthogonalProjectionOnto‖ ≤ (1 : ℝ) := by
    exact_mod_cast W.orthogonalProjectionOnto_norm_le
  have hsub : ‖W.subtypeL‖ ≤ (1 : ℝ) := by
    exact_mod_cast W.norm_subtypeL_le
  have hNN : AW.approximationNumber n = A.approximationNumber n := by
    apply le_antisymm
    · calc
        AW.approximationNumber n
            ≤ ‖W.orthogonalProjectionOnto‖ * A.approximationNumber n :=
          ContinuousLinearMap.approximationNumber_comp_le_norm_mul
            W.orthogonalProjectionOnto A n
        _ ≤ 1 * A.approximationNumber n :=
          mul_le_mul_of_nonneg_right hproj (ContinuousLinearMap.approximationNumber_nonneg _ _)
        _ = A.approximationNumber n := by rw [one_mul]
    · rw [← hfactor]
      calc
        (W.subtypeL ∘L AW).approximationNumber n
            ≤ ‖W.subtypeL‖ * AW.approximationNumber n :=
          ContinuousLinearMap.approximationNumber_comp_le_norm_mul W.subtypeL AW n
        _ ≤ 1 * AW.approximationNumber n :=
          mul_le_mul_of_nonneg_right hsub (ContinuousLinearMap.approximationNumber_nonneg _ _)
        _ = AW.approximationNumber n := by rw [one_mul]
  change (AW.approximationNumber n : ℝ) = (A.approximationNumber n : ℝ)
  exact hNN

/-- Projecting the codomain onto a real subspace containing the range preserves
all finite Ky Fan approximation gauges. -/
theorem kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq_real
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (W : Submodule ℝ G) [W.HasOrthogonalProjection]
    (A : V →L[ℝ] G) (hA : ∀ x, A x ∈ W) (k : ℕ) :
    kyFanApproximationGauge k (W.orthogonalProjectionOnto ∘L A) =
      kyFanApproximationGauge k A := by
  unfold kyFanApproximationGauge
  exact Finset.sum_congr rfl fun n _ =>
    approximationSingularValue_orthogonalProjectionOnto_comp_eq_real W A hA n

/-- The Ky Fan approximation-gauge triangle inequality when the real source is
finite-dimensional and the codomain is arbitrary. -/
theorem kyFanApproximationGauge_add_le_finiteSource_real
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (k : ℕ) (A B : V →L[ℝ] G) :
    kyFanApproximationGauge k (A + B) ≤
      kyFanApproximationGauge k A + kyFanApproximationGauge k B := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  let C : V × V →L[ℝ] G :=
    A ∘L ContinuousLinearMap.fst ℝ V V +
      B ∘L ContinuousLinearMap.snd ℝ V V
  let W : Submodule ℝ G := C.range
  letI : FiniteDimensional ℝ W := by
    apply FiniteDimensional.of_surjective C.rangeRestrict.toLinearMap
    intro y
    rcases y.property with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  letI : W.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace W
  have hA : ∀ x, A x ∈ W := by
    intro x
    change A x ∈ C.range
    refine ⟨(x, 0), ?_⟩
    simp [C]
  have hB : ∀ x, B x ∈ W := by
    intro x
    change B x ∈ C.range
    refine ⟨(0, x), ?_⟩
    simp [C]
  have hAB : ∀ x, (A + B) x ∈ W := by
    intro x
    exact W.add_mem (hA x) (hB x)
  let AW : V →L[ℝ] W := W.orthogonalProjectionOnto ∘L A
  let BW : V →L[ℝ] W := W.orthogonalProjectionOnto ∘L B
  have hsum : W.orthogonalProjectionOnto ∘L (A + B) = AW + BW := by
    ext x
    simp [AW, BW]
  have hAWcont : AW.toLinearMap.toContinuousLinearMap = AW := by
    ext x
    rfl
  have hBWcont : BW.toLinearMap.toContinuousLinearMap = BW := by
    ext x
    rfl
  have hsumcont :
      (AW.toLinearMap + BW.toLinearMap).toContinuousLinearMap = AW + BW := by
    ext x
    rfl
  have htri := kyFanApproximationGauge_add_le_finiteDimensional
    (𝕜 := ℝ) k AW.toLinearMap BW.toLinearMap
  rw [hsumcont, hAWcont, hBWcont] at htri
  calc
    kyFanApproximationGauge k (A + B) =
        kyFanApproximationGauge k (W.orthogonalProjectionOnto ∘L (A + B)) :=
      (kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq_real
        W (A + B) hAB k).symm
    _ = kyFanApproximationGauge k (AW + BW) := by rw [hsum]
    _ ≤ kyFanApproximationGauge k AW + kyFanApproximationGauge k BW := htri
    _ = kyFanApproximationGauge k A + kyFanApproximationGauge k B := by
      rw [kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq_real W A hA k,
        kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq_real W B hB k]

/-- Every positive tolerance admits a real finite-source restriction whose
approximation number is within that tolerance of the ambient value. -/
theorem exists_finiteRestrictionApproximationNumber_add_gt_real
    (T : E →L[ℝ] F) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Fin (n + 1) → E,
      T.approximationNumber n <
        (T ∘L (Submodule.span ℝ (Set.range v)).subtypeL).approximationNumber n + ε := by
  by_cases hsmall : T.approximationNumber n < ε
  · refine ⟨fun _ => 0, hsmall.trans_le ?_⟩
    exact le_add_of_nonneg_left (ContinuousLinearMap.approximationNumber_nonneg _ _)
  · have hεle : ε ≤ T.approximationNumber n := le_of_not_gt hsmall
    have ha0 : 0 < T.approximationNumber n := hε.trans_le hεle
    have hsub : T.approximationNumber n - ε < T.approximationNumber n :=
      sub_lt_self _ hε
    obtain ⟨v, hv⟩ :=
      exists_finiteRestrictionApproximationNumber_gt_of_lt_real T n
        (sub_nonneg.mpr hεle) hsub
    refine ⟨v, ?_⟩
    calc
      T.approximationNumber n =
          (T.approximationNumber n - ε) + ε :=
        by ring
      _ < (T ∘L (Submodule.span ℝ (Set.range v)).subtypeL).approximationNumber n + ε :=
        add_lt_add_left hv ε

/-- Infinite-dimensional Ky Fan addition inequality over real Hilbert spaces,
obtained from simultaneous finite-dimensional localization. -/
theorem kyFanApproximationGauge_add_le_real
    (k : ℕ) (K L : E →L[ℝ] F) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  apply le_of_forall_pos_le_add
  intro ε hε
  let δr : ℝ := ε / (k : ℝ)
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hδr : 0 < δr := div_pos hε hkreal
  let δ : NNReal := ⟨δr, hδr.le⟩
  have hδ : 0 < δ := by
    change 0 < δr
    exact hδr
  choose v hv using fun n =>
    exists_finiteRestrictionApproximationNumber_add_gt_real (K + L) n δ hδ
  let β : Type := Σ n : Fin k, Fin (n.1 + 1)
  let w : β → E := fun p => v p.1.1 p.2
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range w)
  letI : FiniteDimensional ℝ V :=
    Module.Finite.span_of_finite ℝ (Set.finite_range w)
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  let KV : V →L[ℝ] F := K ∘L V.subtypeL
  let LV : V →L[ℝ] F := L ∘L V.subtypeL
  have hsumRestrict : (K + L) ∘L V.subtypeL = KV + LV := by
    ext x
    rfl
  have hterm : ∀ n ∈ Finset.range k,
      approximationSingularValue n (K + L) ≤
        approximationSingularValue n (KV + LV) + (δ : ℝ) := by
    intro n hn
    let U : Submodule ℝ E := Submodule.span ℝ (Set.range (v n))
    have hUV : U ≤ V := by
      apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      apply Submodule.subset_span
      exact ⟨(⟨⟨n, Finset.mem_range.mp hn⟩, j⟩ : β), rfl⟩
    have hmono := approximationSingularValue_restrict_mono_real
      (K + L) n hUV
    have hvNN : (K + L).approximationNumber n <
        ((K + L) ∘L U.subtypeL).approximationNumber n + δ := by
      simpa only [U] using hv n
    have hvReal : approximationSingularValue n (K + L) <
        approximationSingularValue n ((K + L) ∘L U.subtypeL) + (δ : ℝ) := by
      change ((K + L).approximationNumber n : ℝ) <
        (((K + L) ∘L U.subtypeL).approximationNumber n : ℝ) + (δ : ℝ)
      exact_mod_cast hvNN
    calc
      approximationSingularValue n (K + L)
          ≤ approximationSingularValue n ((K + L) ∘L U.subtypeL) + (δ : ℝ) :=
        le_of_lt hvReal
      _ ≤ approximationSingularValue n ((K + L) ∘L V.subtypeL) + (δ : ℝ) :=
        add_le_add_left hmono (δ : ℝ)
      _ = approximationSingularValue n (KV + LV) + (δ : ℝ) := by
        rw [hsumRestrict]
  have hlocal : kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k (KV + LV) + ε := by
    unfold kyFanApproximationGauge
    calc
      ∑ n ∈ Finset.range k, approximationSingularValue n (K + L)
          ≤ ∑ n ∈ Finset.range k,
              (approximationSingularValue n (KV + LV) + (δ : ℝ)) :=
        Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.range k, approximationSingularValue n (KV + LV)) +
          (k : ℝ) * (δ : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
      _ = (∑ n ∈ Finset.range k, approximationSingularValue n (KV + LV)) + ε := by
        change _ + (k : ℝ) * δr = _ + ε
        rw [mul_div_cancel₀ ε hkreal.ne']
  have htri := kyFanApproximationGauge_add_le_finiteSource_real k KV LV
  have hKrestrict : kyFanApproximationGauge k KV ≤ kyFanApproximationGauge k K := by
    unfold kyFanApproximationGauge
    apply Finset.sum_le_sum
    intro n _
    change ((K ∘L V.subtypeL).approximationNumber n : ℝ) ≤
      (K.approximationNumber n : ℝ)
    exact_mod_cast approximationNumber_comp_subtypeL_le_real K n V
  have hLrestrict : kyFanApproximationGauge k LV ≤ kyFanApproximationGauge k L := by
    unfold kyFanApproximationGauge
    apply Finset.sum_le_sum
    intro n _
    change ((L ∘L V.subtypeL).approximationNumber n : ℝ) ≤
      (L.approximationNumber n : ℝ)
    exact_mod_cast approximationNumber_comp_subtypeL_le_real L n V
  calc
    kyFanApproximationGauge k (K + L)
        ≤ kyFanApproximationGauge k (KV + LV) + ε := hlocal
    _ ≤ (kyFanApproximationGauge k KV + kyFanApproximationGauge k LV) + ε :=
      add_le_add_left htri ε
    _ ≤ (kyFanApproximationGauge k K + kyFanApproximationGauge k L) + ε :=
      add_le_add_left (add_le_add hKrestrict hLrestrict) ε


end

end ApproximationNumbersReal
end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti