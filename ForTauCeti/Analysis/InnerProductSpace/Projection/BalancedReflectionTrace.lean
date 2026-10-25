/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BalancedReflection
public import ForTauCeti.Analysis.InnerProductSpace.Projection.PairedPhaseTrace

/-!
# Principal-angle sums of balanced reflecting transports

A balanced reflection has only fixed and right-angle transport blocks.
Its negative-space dimension is the right-angle multiplicity, so every
zero-preserving principal-angle sum is that dimension times the value
at a right angle. The remaining fixed space contributes zero.
-/

public section

noncomputable section

namespace Submodule

open TauCeti
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Every zero-preserving principal-angle sum for a balanced reflecting
transport counts the negative reflection space at a right angle. No
assumption on the common fixed source and target spaces is needed. -/
theorem sum_principalAngles_of_balanced_reflection_complex
    (K L : Submodule ℂ E) (A : E →L[ℂ] E) (hA : IsStarProjection A)
    (hbalance : (2 : ℂ) • (A * K.starProjection * A) = A)
    (V : E ≃ₗᵢ[ℂ] E) (hV : (V : E →L[ℂ] E) = 1 - (2 : ℂ) • A)
    (hmap : K.map V.toLinearMap = L) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ i : Fin (Module.finrank ℂ K), f (K.principalAngles L i)) =
      Module.finrank ℂ A.range * f (Real.pi / 2) := by
  classical
  obtain ⟨horth, J₀, _, hJ₀act, hVcoords, _⟩ :=
    balanced_reflection_paired_decomposition K A hA hbalance V hV
  let H := A.range
  let Z := (pairedInvolutionEmbedding H K.reflection horth).toLinearMap.rangeᗮ
  let d := pairedInvolutionDecomposition H K.reflection horth
  let b := stdOrthonormalBasis ℂ H
  have hfix (z : Z) : V (z : E) = (z : E) := by
    have h := hVcoords (WithLp.toLp 2 (WithLp.toLp 2 (0, 0), z))
    simpa [pairedInvolutionDecomposition_apply] using h
  have hJZ (z : E) (hz : z ∈ Z) : K.reflection z ∈ Z := by
    rw [← hJ₀act ⟨z, hz⟩]
    exact (J₀ ⟨z, hz⟩).property
  have hPexpr : K.starProjection = (1 / 2 : ℂ) • (1 + (K.reflection : E →L[ℂ] E)) := by
    rw [Submodule.coe_reflection]
    module
  have hKZ : ∀ z ∈ Z, K.starProjection z ∈ Z := by
    intro z hz
    rw [hPexpr]
    change (1 / 2 : ℂ) • (z + K.reflection z) ∈ Z
    exact Z.smul_mem _ (Z.add_mem hz (hJZ z hz))
  have hsymfix (z : Z) : V.symm (z : E) = (z : E) := by
    apply V.injective
    rw [V.apply_symm_apply, hfix]
  have hLact (z : Z) : L.starProjection z = K.starProjection z := by
    rw [← hmap, Submodule.starProjection_map_apply, hsymfix]
    exact hfix ⟨K.starProjection z, hKZ z z.property⟩
  have hLZ : ∀ z ∈ Z, L.starProjection z ∈ Z := by
    intro z hz
    have h := hLact ⟨z, hz⟩
    change L.starProjection z = K.starProjection z at h
    rw [h]
    exact hKZ z hz
  have hcomap : K.comap Z.subtype = L.comap Z.subtype := by
    ext z
    constructor
    · intro hz
      change (z : E) ∈ L
      rw [← hmap]
      have h := Submodule.mem_map_of_mem (f := V.toLinearMap) hz
      change V (z : E) ∈ K.map V.toLinearMap at h
      rwa [hfix z] at h
    · intro hz
      change (z : E) ∈ K
      change (z : E) ∈ L at hz
      rw [← hmap] at hz
      obtain ⟨x, hx, hxz⟩ := hz
      have hxeq : x = (z : E) := V.injective (hxz.trans (hfix z).symm)
      rwa [hxeq] at hx
  have hneg (x : H) : V (x : E) = -(x : E) := by
    have h := hVcoords (WithLp.toLp 2 (WithLp.toLp 2 (x, 0), 0))
    simpa [pairedInvolutionDecomposition_apply] using h
  have hpos (x : H) : V (K.reflection x) = K.reflection x := by
    have h := hVcoords (WithLp.toLp 2 (WithLp.toLp 2 (0, x), 0))
    simpa [pairedInvolutionDecomposition_apply] using h
  have hu (i) : V (b i : E) = Complex.exp ((Real.pi : ℂ) * Complex.I) • (b i : E) := by
    rw [hneg]
    simp only [Complex.exp_pi_mul_I, neg_one_smul]
  have hw (i) : V (K.reflection (b i)) =
      Complex.exp (((-(0 : ℝ) : ℝ) : ℂ) * Complex.I) • K.reflection (b i) := by
    simpa using hpos (b i)
  have hmean (i : Fin (Module.finrank ℂ H)) : (Real.pi + (0 : ℝ)) / 2 ∈
      Set.Icc 0 (Real.pi / 2) := by
    simp only [add_zero]
    exact ⟨by positivity, le_rfl⟩
  have hd : ∀ x, d x = (x.fst.fst : E) + K.reflection x.fst.snd + (x.snd : E) :=
    pairedInvolutionDecomposition_apply H K.reflection horth
  have hsum := sum_principalAngles_eq_paired_phases_add_comap_complex
    K L H Z V hmap b (fun _ => Real.pi) (fun _ => 0) hu hw hmean d hd hKZ hLZ f hf
  have hzero : (K.comap Z.subtype).principalAngles (L.comap Z.subtype) = 0 := by
    simpa only [← hcomap] using (K.comap Z.subtype).principalAngles_self
  rw [hzero] at hsum
  simpa only [add_zero, Finsupp.coe_zero, Pi.zero_apply, hf, Finset.sum_const_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum

end Submodule
