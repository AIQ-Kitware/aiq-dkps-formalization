/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.KyFan
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan

/-!
# Ky Fan gauges of approximation numbers

The `k`th **Ky Fan gauge** of a bounded operator is the sum of its first `k` approximation
numbers,

```
(T.kyFanGauge k : ℝ) = ∑ n ∈ Finset.range k, (T.singularValue n : ℝ),
```

so `(T.kyFanGauge 1 : ℝ)` is the operator norm and the gauges increase to the nuclear norm.  Each is
a norm on the two-sided ideal it defines, and the family of them determines every
unitarily invariant norm — which is why the Ky Fan gauges, not the individual approximation
numbers, are what an operator-ideal theory is built from.

## The triangle inequality

TauCeti owns the general Ky Fan gauge triangle inequality. The local theorem
`kyFanGaugeReal_add_le_of_exists_finiteRestriction` remains as a field-generic localization
result for callers that provide finite-source approximation directly, without
assuming source completeness. Complete-source consumers use Tau Ceti directly.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/OperatorIdeal/ApproximationNumbers/Core.lean`.
* Original declarations: `TauCeti.DavisKahan.Experimental.ExactSinTheta.{`
  `kyFanApproximationGauge, kyFanApproximationGauge_neg, kyFanApproximationGauge_zero,`
  `kyFanApproximationGauge_zero_map, kyFanApproximationGauge_one,`
  `kyFanApproximationGauge_smul, kyFanApproximationGauge_nonneg,`
  `kyFanApproximationGauge_adjoint, kyFanApproximationGauge_comp_le,`
  `opNorm_le_kyFanApproximationGauge, kyFanApproximationGauge_le_nat_mul_opNorm,`
  `kyFanSum_le_kyFanApproximationGauge,`
  `kyFanSum_eq_kyFanApproximationGauge,`
  `kyFanApproximationGauge_add_le_finiteDimensional,`
  `approximationSingularValue_restrict_mono,`
  `approximationSingularValue_orthogonalProjectionOnto_comp_eq,`
  `kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq,`
  `kyFanApproximationGauge_add_le_finiteSource,`
  `exists_finiteRestrictionApproximationNumber_add_gt,`
  `kyFanApproximationGauge_add_le_complex}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **copied and renamespaced**.  The gauge moves to
  `ContinuousLinearMap.kyFanGaugeReal` with the operator first so dot notation resolves, and
  `approximationSingularValue n K` is spelled `K.approximationNumber n` throughout — it was
  only ever an alias for it. No proof was changed at that extraction. The shared
  elementary laws and finite-source triangle proof are now retired in favor of accepted
  native APIs; only split-embedding, incomplete-space restriction/projection and weaker
  localization results remain.
* Spectra influence: **none**, as of the replacement of the min--max bridge on 2026-07-28.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

noncomputable section

universe u v w x y

variable {𝕜 : Type u} [RCLike 𝕜]

section Basic

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Ky Fan gauges do not see an enlargement of the codomain**, since the approximation
numbers do not: `ι` is a contraction of `F` into `G` and `π` a contractive left inverse,
the model being the inclusion of `F` as one summand of an `ℓ²` direct sum together with
the projection back onto it.  See
`ContinuousLinearMap.singularValue_comp_eq_of_leftInverse`. -/
theorem kyFanGaugeReal_comp_eq_of_leftInverse {G : Type x}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {ι : F →L[𝕜] G} {π : G →L[𝕜] F} (hπι : Function.LeftInverse π ι)
    (hι : ‖ι‖ ≤ 1) (hπ : ‖π‖ ≤ 1) (T : E →L[𝕜] F) (k : ℕ) :
    ((ι ∘L T).kyFanGauge k : ℝ) = (T.kyFanGauge k : ℝ) :=
  by
    rw [ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum, ContinuousLinearMap.kyFanGauge_def,
      NNReal.coe_sum]
    exact Finset.sum_congr rfl fun n _ =>
      congrArg NNReal.toReal (singularValue_comp_eq_of_leftInverse hπι hι hπ T n)

end Basic

section Compression

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
-- Neither space needs to be complete: completeness is what `HasMinMaxLowerBound` is proved
-- from, not what the passage from it to the triangle inequality uses.
omit [CompleteSpace E] [CompleteSpace F] in
/-- Restricting to a larger source subspace can only increase an approximation number. -/
theorem approximationNumber_restrict_mono (T : E →L[𝕜] F) (n : ℕ) {U V : Submodule 𝕜 E}
    (hUV : U ≤ V) :
    ((T ∘L U.subtypeL).singularValue n : ℝ) ≤ ((T ∘L V.subtypeL).singularValue n : ℝ) := by
  let J : U →L[𝕜] V :=
    (Submodule.inclusion hUV).mkContinuous 1 fun x => by
      -- names the application so the norm bound applies to it directly.
      change ‖((x : U) : E)‖ ≤ 1 * ‖x‖
      simp
  have hJnorm : ‖J‖ ≤ (1 : ℝ) :=
    J.opNorm_le_bound zero_le_one fun x => by
      -- names the application so the norm bound applies to it directly.
      change ‖((x : U) : E)‖ ≤ 1 * ‖x‖
      simp
  have hcomp : T ∘L U.subtypeL = (T ∘L V.subtypeL) ∘L J := by
    ext x
    rfl
  rw [hcomp]
  calc
    (((T ∘L V.subtypeL) ∘L J).singularValue n : ℝ)
        ≤ ((T ∘L V.subtypeL).singularValue n : ℝ) * ‖J‖ :=
      (NNReal.coe_le_coe.mpr (ContinuousLinearMap.singularValue_comp_le_right (T ∘L V.subtypeL) J
          n))
    _ ≤ ((T ∘L V.subtypeL).singularValue n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hJnorm ((ContinuousLinearMap.singularValue _ _).coe_nonneg)
    _ = ((T ∘L V.subtypeL).singularValue n : ℝ) := by rw [mul_one]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Compressing the codomain to a subspace that already contains the range preserves every
approximation number. -/
theorem approximationNumber_orthogonalProjectionOnto_comp_eq
    (W : Submodule 𝕜 F) [W.HasOrthogonalProjection]
    (A : E →L[𝕜] F) (hA : ∀ x, A x ∈ W) (n : ℕ) :
    ((W.orthogonalProjectionOnto ∘L A).singularValue n : ℝ) = (A.singularValue n : ℝ) := by
  set AW : E →L[𝕜] W := W.orthogonalProjectionOnto ∘L A with hAW
  have hfactor : W.subtypeL ∘L AW = A := by
    ext x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change W.starProjection (A x) = A x
    exact W.starProjection_eq_self_iff.mpr (hA x)
  have hproj : ‖W.orthogonalProjectionOnto‖ ≤ (1 : ℝ) := W.orthogonalProjectionOnto_norm_le
  have hsub : ‖W.subtypeL‖ ≤ (1 : ℝ) := W.norm_subtypeL_le
  refine le_antisymm ?_ ?_
  · calc
      (AW.singularValue n : ℝ)
          ≤ ‖W.orthogonalProjectionOnto‖ * (A.singularValue n : ℝ) :=
        (NNReal.coe_le_coe.mpr (ContinuousLinearMap.singularValue_comp_le_left
            W.orthogonalProjectionOnto A n))
      _ ≤ 1 * (A.singularValue n : ℝ) :=
        mul_le_mul_of_nonneg_right hproj ((ContinuousLinearMap.singularValue _ _).coe_nonneg)
      _ = (A.singularValue n : ℝ) := by rw [one_mul]
  · rw [← hfactor]
    calc
      ((W.subtypeL ∘L AW).singularValue n : ℝ)
          ≤ ‖W.subtypeL‖ * (AW.singularValue n : ℝ) :=
        (NNReal.coe_le_coe.mpr (ContinuousLinearMap.singularValue_comp_le_left W.subtypeL AW n))
      _ ≤ 1 * (AW.singularValue n : ℝ) :=
        mul_le_mul_of_nonneg_right hsub ((ContinuousLinearMap.singularValue _ _).coe_nonneg)
      _ = (AW.singularValue n : ℝ) := by rw [one_mul]

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Ky Fan form of `approximationNumber_orthogonalProjectionOnto_comp_eq`. -/
theorem kyFanGaugeReal_orthogonalProjectionOnto_comp_eq
    (W : Submodule 𝕜 F) [W.HasOrthogonalProjection]
    (A : E →L[𝕜] F) (hA : ∀ x, A x ∈ W) (k : ℕ) :
    ((W.orthogonalProjectionOnto ∘L A).kyFanGauge k : ℝ) = (A.kyFanGauge k : ℝ) :=
  by
    rw [ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum, ContinuousLinearMap.kyFanGauge_def,
      NNReal.coe_sum]
    exact Finset.sum_congr rfl fun n _ =>
      approximationNumber_orthogonalProjectionOnto_comp_eq W A hA n

end Compression

section Localization

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Step 3 of the triangle inequality, and the only step that is not field-generic —
so it takes the field-dependent input as a hypothesis.**

Given that every approximation number of `S + T` is approached by its restrictions to
finite-dimensional subspaces of the source, the Ky Fan triangle inequality for `S` and `T`
follows: span the finitely many near-optimal vectors, restrict there, apply the
finite-dimensional-source case, and let the tolerance go to zero.

Nothing else in the argument sees the scalars.  Over `ℂ` the hypothesis is
`exists_finiteRestrictionApproximationNumber_add_gt`, a corollary of the min-max theorem;
over `ℝ`, where Mathlib's continuous functional calculus is not available for operators on
the space itself, it is proved by complexification.  Stating the step this way is what keeps
the two fields from needing two copies of the argument. -/
theorem kyFanGaugeReal_add_le_of_exists_finiteRestriction {S T : E →L[𝕜] F}
    (hfr : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ v : Fin (n + 1) → E,
      ((S + T).singularValue n : ℝ) <
        (((S + T) ∘L (Submodule.span 𝕜 (Set.range v)).subtypeL).singularValue n : ℝ) + ε)
    (k : ℕ) :
    ((S + T).kyFanGauge k : ℝ) ≤ (S.kyFanGauge k : ℝ) + (T.kyFanGauge k : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp
  apply le_of_forall_pos_le_add
  intro ε hε
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hδ : 0 < ε / (k : ℝ) := div_pos hε hkreal
  choose v hv using fun n => hfr n (ε / (k : ℝ)) hδ
  let β : Type := Σ n : Fin k, Fin (n.1 + 1)
  let w : β → E := fun p => v p.1.1 p.2
  let V : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range w)
  let : FiniteDimensional 𝕜 V := Module.Finite.span_of_finite 𝕜 (Set.finite_range w)
  let : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  let SV : V →L[𝕜] F := S ∘L V.subtypeL
  let TV : V →L[𝕜] F := T ∘L V.subtypeL
  have hsumRestrict : (S + T) ∘L V.subtypeL = SV + TV := by
    ext x
    rfl
  have hterm : ∀ n ∈ Finset.range k,
      ((S + T).singularValue n : ℝ) ≤ ((SV + TV).singularValue n : ℝ) + ε / (k : ℝ) := by
    intro n hn
    let U : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range (v n))
    have hUV : U ≤ V := by
      refine Submodule.span_le.mpr ?_
      rintro x ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(⟨⟨n, Finset.mem_range.mp hn⟩, j⟩ : β), rfl⟩
    calc
      ((S + T).singularValue n : ℝ)
          ≤ (((S + T) ∘L U.subtypeL).singularValue n : ℝ) + ε / (k : ℝ) := (hv n).le
      _ ≤ (((S + T) ∘L V.subtypeL).singularValue n : ℝ) + ε / (k : ℝ) :=
        by gcongr; exact (S + T).approximationNumber_restrict_mono n hUV
      _ = ((SV + TV).singularValue n : ℝ) + ε / (k : ℝ) := by rw [hsumRestrict]
  have hlocal : ((S + T).kyFanGauge k : ℝ) ≤ ((SV + TV).kyFanGauge k : ℝ) + ε := by
    calc
      ((S + T).kyFanGauge k : ℝ) ≤ ∑ n ∈ Finset.range k,
          (((SV + TV).singularValue n : ℝ) + ε / (k : ℝ)) := by
            rw [ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum]
            exact Finset.sum_le_sum hterm
      _ = ((SV + TV).kyFanGauge k : ℝ) + (k : ℝ) * (ε / (k : ℝ)) := by
        rw [ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum, Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
      _ = ((SV + TV).kyFanGauge k : ℝ) + ε := by rw [mul_div_cancel₀ ε hkreal.ne']
  have hrestrictS : (SV.kyFanGauge k : ℝ) ≤ (S.kyFanGauge k : ℝ) := by
    rw [ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum, ContinuousLinearMap.kyFanGauge_def,
      NNReal.coe_sum]
    exact Finset.sum_le_sum fun n _ => S.approximationNumber_comp_subtypeL_le n V
  have hrestrictT : (TV.kyFanGauge k : ℝ) ≤ (T.kyFanGauge k : ℝ) := by
    rw [ContinuousLinearMap.kyFanGauge_def, NNReal.coe_sum, ContinuousLinearMap.kyFanGauge_def,
      NNReal.coe_sum]
    exact Finset.sum_le_sum fun n _ => T.approximationNumber_comp_subtypeL_le n V
  calc
    ((S + T).kyFanGauge k : ℝ) ≤ ((SV + TV).kyFanGauge k : ℝ) + ε := hlocal
    _ ≤ ((SV.kyFanGauge k : ℝ) + (TV.kyFanGauge k : ℝ)) + ε := by
      gcongr
      exact NNReal.coe_le_coe.mpr (ContinuousLinearMap.kyFanGauge_add_le SV TV k)
    _ ≤ ((S.kyFanGauge k : ℝ) + (T.kyFanGauge k : ℝ)) + ε := by gcongr

end Localization

end

end ContinuousLinearMap
