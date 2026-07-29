/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
import ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm

/-!
# Adapter: canonical ideal families to the historical Davis--Kahan record

`TauCeti.SymmetricOperatorIdealFamily` is the canonical form of a symmetric
operator ideal family (one gauge in `ℝ≥0∞`, four laws, structural
extensionality, completeness as `CompleteSpace`).  The Davis--Kahan production
tree was written against the historical
`RectangularSymmetricIdealFamily`, which carries membership and a real gauge as
independent data together with fourteen fields and a hand-rolled Cauchy
criterion.

This module supplies the forgetful map

```
TauCeti.SymmetricOperatorIdealFamily.toRectangular :
  SymmetricOperatorIdealFamily 𝕜 → RectangularSymmetricIdealFamily 𝕜
```

so that

* the redesign is *validated*: every law of the historical record is a theorem
  about the canonical one, so nothing the Davis--Kahan proofs rely on was lost;
* the ~70 modules that consume the historical record keep compiling while they
  are migrated one at a time.

The map is deliberately one-directional.  There is no inverse: a historical
record does not determine a canonical family, because its gauge is unconstrained
off the ideal — which is exactly the extensionality defect the redesign removes.

This adapter is **transitional**.  It should be deleted once the production
tree consumes `SymmetricOperatorIdealFamily` directly.
-/

namespace TauCeti

open scoped ENNReal

universe u v

namespace SymmetricOperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]

open DavisKahan.Experimental.ExactSinTheta

/-- The historical Davis--Kahan ideal-family record obtained from a canonical
symmetric ideal family: membership is finiteness of the gauge, and the real
gauge is the canonical gauge read in `ℝ`. -/
noncomputable def toRectangular (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete] :
    RectangularSymmetricIdealFamily.{u, v} 𝕜 where
  Mem := @fun _ _ _ _ _ _ _ _ A => N.gauge A ≠ ∞
  gauge := @fun _ _ _ _ _ _ _ _ A => (N.gauge A).toReal
  zero_mem := by intros; exact N.toOperatorIdealFamily.carrier.zero_mem
  add_mem := by intros; exact N.toOperatorIdealFamily.carrier.add_mem ‹_› ‹_›
  smul_mem := by intros; exact N.toOperatorIdealFamily.carrier.smul_mem _ ‹_›
  adjoint_mem := by intros; exact N.adjoint_mem_carrier ‹_›
  comp_mem := by intros; exact N.toOperatorIdealFamily.comp_mem_carrier _ _ ‹_›
  gauge_nonneg := by intros; exact ENNReal.toReal_nonneg
  gauge_zero := by intros; simp
  gauge_eq_zero := by
    intros
    rename_i hA h
    exact N.toOperatorIdealFamily.gauge_eq_zero
      (((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right hA)
  gauge_add_le := by
    intros
    rename_i hA hB
    rw [← ENNReal.toReal_add hA hB]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)
      (N.toOperatorIdealFamily.gauge_add_le _ _)
  gauge_smul := by
    intros
    rw [N.toOperatorIdealFamily.gauge_smul, ENNReal.toReal_mul, toReal_enorm]
  gauge_adjoint := by intros; rw [N.gauge_adjoint]
  gauge_comp_le := by
    intros
    rename_i L A R hA
    have hbound := N.toOperatorIdealFamily.gauge_comp_le L A R
    have hfin : ‖L‖ₑ * N.gauge A * ‖R‖ₑ ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA) (by simp)
    refine (ENNReal.toReal_mono hfin hbound).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_enorm, toReal_enorm]
  opNorm_le_gauge := by
    intros
    rename_i hA
    have h := ENNReal.toReal_mono hA (N.toOperatorIdealFamily.enorm_le_gauge _)
    rwa [toReal_enorm] at h
  gauge_complete := by
    intro E F _ _ _ _ _ _ A hmem hcauchy
    -- Read the sequence inside the ideal, where the gauge *is* the norm.
    set a : ℕ → N.toOperatorIdealFamily.Elem E F :=
      fun n => OperatorIdealFamily.Elem.mk (hmem n) with ha
    have hdist : ∀ m n, dist (a m) (a n) = (N.gauge (A m - A n)).toReal := by
      intro m n
      rw [dist_eq_norm, ha, OperatorIdealFamily.Elem.norm_def]
      simp
    have hcs : CauchySeq a := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨M, hM⟩ := hcauchy ε hε
      exact ⟨M, fun m hm n hn => by rw [hdist]; exact hM m n hm hn⟩
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcs
    refine ⟨l.val, l.val_mem, fun ε hε => ?_⟩
    rw [Metric.tendsto_atTop] at hl
    obtain ⟨M, hM⟩ := hl ε hε
    refine ⟨M, fun n hn => ?_⟩
    have := hM n hn
    rwa [dist_eq_norm, OperatorIdealFamily.Elem.norm_def, show (a n - l).val = A n - l.val from
      by simp [ha]] at this

/-- Membership transfers across the rectangular adapter. -/
@[simp]
theorem toRectangular_mem (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete] {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : N.toRectangular.Mem A ↔ N.gauge A ≠ ∞ := Iff.rfl

/-- The gauge is unchanged by the rectangular adapter -- the property that makes it an adapter
rather than a different family. -/
@[simp]
theorem toRectangular_gauge (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete] {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : N.toRectangular.gauge A = (N.gauge A).toReal := rfl

/-- The adapter sends the canonical operator-norm family to the historical
operator-norm family: on members the two gauges agree. -/
theorem toRectangular_operatorNormFamily_gauge {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (operatorNormFamily.{u, v} 𝕜).toRectangular.gauge A =
      RectangularSymmetricIdealFamily.operatorNorm.gauge A := by
  rw [toRectangular_gauge, gauge_operatorNormFamily, toReal_enorm]
  rfl

end SymmetricOperatorIdealFamily

end TauCeti
