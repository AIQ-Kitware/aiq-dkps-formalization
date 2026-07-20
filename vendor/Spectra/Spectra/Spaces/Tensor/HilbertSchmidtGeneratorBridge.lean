/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Spectra.Spaces.Tensor.HilbertSchmidtFlow

/-!
# Generator graph of the Hilbert--Schmidt Sylvester flow

The tensor flow

`z |-> (U(t) tensor conjugate(V(t))) z`

represents `X |-> U(t) X V(-t)`.  This file proves the nontrivial direction of
the generator graph correspondence: if a tensor `z` lies in the generator
domain with generator value `c`, then the represented bounded operator maps
the domain of `generator V` into the domain of `generator U` and satisfies

`generator U * X - X * generator V = C`.

This direction is exactly what the defect-first square-norm construction needs
after the inverse spectral multiplier has produced a tensor-domain vector.
The converse graph inclusion is intentionally kept separate; it requires a
closed-core argument rather than another formal difference-quotient rewrite.
-/

open InnerProductSpace Complex Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace Spectra
namespace HilbertSchmidtTensor

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Domain-aware Sylvester equation for the generators of two unitary groups. -/
structure HasGeneratorSylvesterEquation
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    (X C : F →L[ℂ] E) : Prop where
  mapsTo_domain : ∀ x : (OneParameterUnitaryGroup.generator V).domain,
    X (x : F) ∈ (OneParameterUnitaryGroup.generator U).domain
  equation : ∀ x : (OneParameterUnitaryGroup.generator V).domain,
    OneParameterUnitaryGroup.generator U
        ⟨X (x : F), mapsTo_domain x⟩ -
      X (OneParameterUnitaryGroup.generator V x) = C (x : F)

private theorem tendsto_neg_punctured :
    Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

/-- Difference quotient decomposition underlying the generator graph theorem. -/
theorem genDiffQuot_toOperator_decomposition
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    (z : Space E F) (x : F) (t : ℝ) :
    OneParameterUnitaryGroup.genDiffQuot U (toOperator z x) t =
      toOperator
          (OneParameterUnitaryGroup.genDiffQuot (sylvesterGroup U V) z t) x +
        U.U t
          (toOperator z
            (OneParameterUnitaryGroup.genDiffQuot V x (-t))) := by
  -- `toOperator` is the unbundled map, so `map_smul`/`map_sub` do not reach it;
  -- without its own linearity lemmas the difference quotient never splits and
  -- the flow rewrite has nothing to fire on.
  simp only [OneParameterUnitaryGroup.genDiffQuot_apply,
    map_smul, map_sub, toOperator_smul, toOperator_sub,
    toOperator_sylvesterGroup, smul_apply, sub_apply,
    ContinuousLinearMap.comp_apply]
  by_cases ht : t = 0
  · subst t
    simp
  · have hinv : (I * ((-t : ℝ) : ℂ))⁻¹ = -(I * (t : ℂ))⁻¹ := by
      rw [ofReal_neg, mul_neg, inv_neg]
    rw [hinv]
    module

/-- Generator-domain membership of a tensor implies domain transport for the
represented operator. -/
theorem toOperator_maps_generatorDomain
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    {z c : Space E F}
    (hz : z ∈ (OneParameterUnitaryGroup.generator (sylvesterGroup U V)).domain)
    (hzc : OneParameterUnitaryGroup.generator (sylvesterGroup U V) ⟨z, hz⟩ = c)
    (x : (OneParameterUnitaryGroup.generator V).domain) :
    toOperator z (x : F) ∈ (OneParameterUnitaryGroup.generator U).domain := by
  let W := sylvesterGroup U V
  have hfirstTensor :=
    OneParameterUnitaryGroup.generator_tendsto W ⟨z, hz⟩
  rw [hzc] at hfirstTensor
  have hfirstOperator : Tendsto
      (fun t => toOperator
        (OneParameterUnitaryGroup.genDiffQuot W z t))
      (𝓝[≠] (0 : ℝ)) (𝓝 (toOperator c)) :=
    ((toOperatorL (E := E) (F := F)).continuous.tendsto c).comp
      hfirstTensor
  have hfirst : Tendsto
      (fun t => toOperator
        (OneParameterUnitaryGroup.genDiffQuot W z t) (x : F))
      (𝓝[≠] (0 : ℝ)) (𝓝 (toOperator c (x : F))) :=
    (((ContinuousLinearMap.apply ℂ E (x : F)).continuous.tendsto
      (toOperator c)).comp hfirstOperator)

  have hq : Tendsto
      (fun t : ℝ => OneParameterUnitaryGroup.genDiffQuot V (x : F) (-t))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (OneParameterUnitaryGroup.generator V x)) :=
    (OneParameterUnitaryGroup.generator_tendsto V x).comp
      tendsto_neg_punctured
  have hZq : Tendsto
      (fun t : ℝ => toOperator z
        (OneParameterUnitaryGroup.genDiffQuot V (x : F) (-t)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (toOperator z (OneParameterUnitaryGroup.generator V x))) :=
    ((toOperator z).continuous.tendsto _).comp hq
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hsecondRaw := OneParameterUnitaryGroup.tendsto_apply_unitary_family
    (fun t => U.U t)
    (fun t y => U.norm_preserving t y)
    U.strong_continuous ht0 hZq
  have hsecond : Tendsto
      (fun t : ℝ => U.U t
        (toOperator z
          (OneParameterUnitaryGroup.genDiffQuot V (x : F) (-t))))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (toOperator z (OneParameterUnitaryGroup.generator V x))) := by
    simpa [U.identity] using hsecondRaw

  -- The goal names the partial operator's domain; the membership lemma is
  -- stated for the generator domain, and the two are bridged definitionally.
  rw [OneParameterUnitaryGroup.generator_domain,
    OneParameterUnitaryGroup.mem_generatorDomain]
  refine ⟨toOperator c (x : F) +
    toOperator z (OneParameterUnitaryGroup.generator V x), ?_⟩
  have hsum := hfirst.add hsecond
  exact hsum.congr' (Eventually.of_forall fun t =>
    (genDiffQuot_toOperator_decomposition U V z (x : F) t).symm)

/-- The represented operator satisfies the generator-level closed Sylvester
equation. -/
theorem toOperator_hasGeneratorSylvesterEquation
    (U : OneParameterUnitaryGroup (H := E))
    (V : OneParameterUnitaryGroup (H := F))
    {z c : Space E F}
    (hz : z ∈ (OneParameterUnitaryGroup.generator (sylvesterGroup U V)).domain)
    (hzc : OneParameterUnitaryGroup.generator (sylvesterGroup U V) ⟨z, hz⟩ = c) :
    HasGeneratorSylvesterEquation U V (toOperator z) (toOperator c) := by
  let hmaps : ∀ x : (OneParameterUnitaryGroup.generator V).domain,
      toOperator z (x : F) ∈ (OneParameterUnitaryGroup.generator U).domain :=
    toOperator_maps_generatorDomain U V hz hzc
  refine ⟨hmaps, ?_⟩
  intro x
  have hlimit : Tendsto
      (OneParameterUnitaryGroup.genDiffQuot U (toOperator z (x : F)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (toOperator c (x : F) +
        toOperator z (OneParameterUnitaryGroup.generator V x))) := by
    have hfirstTensor :=
      OneParameterUnitaryGroup.generator_tendsto
        (sylvesterGroup U V) ⟨z, hz⟩
    rw [hzc] at hfirstTensor
    have hfirstOperator : Tendsto
        (fun t => toOperator
          (OneParameterUnitaryGroup.genDiffQuot (sylvesterGroup U V) z t))
        (𝓝[≠] (0 : ℝ)) (𝓝 (toOperator c)) :=
      ((toOperatorL (E := E) (F := F)).continuous.tendsto c).comp
        hfirstTensor
    have hfirst :=
      (((ContinuousLinearMap.apply ℂ E (x : F)).continuous.tendsto
        (toOperator c)).comp hfirstOperator)
    have hq := (OneParameterUnitaryGroup.generator_tendsto V x).comp
      tendsto_neg_punctured
    have hZq := ((toOperator z).continuous.tendsto _).comp hq
    have ht0 : Tendsto (fun t : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hsecondRaw := OneParameterUnitaryGroup.tendsto_apply_unitary_family
      (fun t => U.U t)
      (fun t y => U.norm_preserving t y)
      U.strong_continuous ht0 hZq
    have hsecond : Tendsto
        (fun t : ℝ => U.U t
          (toOperator z
            (OneParameterUnitaryGroup.genDiffQuot V (x : F) (-t))))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (toOperator z (OneParameterUnitaryGroup.generator V x))) := by
      simpa [U.identity] using hsecondRaw
    exact (hfirst.add hsecond).congr'
      (Eventually.of_forall fun t =>
        (genDiffQuot_toOperator_decomposition U V z (x : F) t).symm)
  have hgen := OneParameterUnitaryGroup.generator_tendsto U
    ⟨toOperator z (x : F), hmaps x⟩
  have heq := tendsto_nhds_unique hgen hlimit
  rw [heq]
  abel

end
end HilbertSchmidtTensor
end Spectra
