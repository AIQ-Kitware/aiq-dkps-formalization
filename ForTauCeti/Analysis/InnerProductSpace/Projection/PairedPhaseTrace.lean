/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.PairedPhase
public import ForTauCeti.Analysis.InnerProductSpace.Projection.InvariantSubspace
public import ForTauCeti.Analysis.InnerProductSpace.Projection.FiniteSpectralTrace
public import ForTauCeti.Analysis.InnerProductSpace.SpectralTrace
public import Mathlib.Logic.Equiv.Prod

/-!
# Principal-angle sums in paired phase coordinates

A complete orthogonal decomposition into reflection-paired transporter
eigenvectors and a reducing remainder computes every zero-preserving sum
of the accepted principal angles. Each paired mean phase contributes once;
the remainder contributes the principal angles of the restricted pair.

Use an eigenbasis of the restricted sine operator on the remainder, combine
it with the paired basis, and evaluate the directed sine spectral trace.
The source projection has diagonal weight one half on each paired vector.
The invariant-subspace projection identity identifies the remaining trace.
No ordering or multiplicity comparison between angle lists is needed.
-/

public section

noncomputable section

namespace Submodule

open TauCeti
open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

set_option maxHeartbeats 800000 in
-- The nested product basis and its two functional-calculus trace evaluations
-- require more elaboration than the default heartbeat allowance.
/-- A complete paired phase decomposition computes every zero-preserving
principal-angle sum, with the actual restricted pair on the remainder. -/
theorem sum_principalAngles_eq_paired_phases_add_comap_complex
    (K L H Z : Submodule ℂ E) (U : E ≃ₗᵢ[ℂ] E)
    (hmap : K.map U.toLinearMap = L)
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ H) (alpha beta : Fin n → ℝ)
    (hu : ∀ i, U (b i : E) = Complex.exp ((alpha i : ℂ) * Complex.I) • (b i : E))
    (hw : ∀ i, U (K.reflection (b i)) =
      Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (b i))
    (hmean : ∀ i, (alpha i + beta i) / 2 ∈ Set.Icc 0 (Real.pi / 2))
    (d : WithLp 2 (WithLp 2 (H × H) × Z) ≃ₗᵢ[ℂ] E)
    (hd : ∀ x, d x = (x.fst.fst : E) + K.reflection x.fst.snd + (x.snd : E))
    (hK : ∀ x ∈ Z, K.starProjection x ∈ Z)
    (hL : ∀ x ∈ Z, L.starProjection x ∈ Z)
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ i : Fin (Module.finrank ℂ K), f (K.principalAngles L i)) =
      (∑ i, f ((alpha i + beta i) / 2)) +
        ∑ j : Fin (Module.finrank ℂ (K.comap Z.subtype)),
          f ((K.comap Z.subtype).principalAngles (L.comap Z.subtype) j) := by
  classical
  let K₀ := K.comap Z.subtype
  let L₀ := L.comap Z.subtype
  let S := K.sinAngleOperator L
  let S₀ := K₀.sinAngleOperator L₀
  let hS₀ := (K₀.isPositive_sinAngleOperator L₀).toLinearMap
  let bf := hS₀.isSymmetric.eigenvectorBasis rfl
  let mu := hS₀.isSymmetric.eigenvalues rfl
  have hbf (j) : S₀ (bf j) = (mu j : ℂ) • bf j :=
    hS₀.isSymmetric.apply_eigenvectorBasis rfl j
  have hmu (j) : 0 ≤ mu j := hS₀.nonneg_eigenvalues rfl j
  let m := Module.finrank ℂ Z
  let pairIndex : Fin 2 × Fin n ≃ Fin n ⊕ Fin n :=
    (Equiv.prodCongr finTwoEquiv (Equiv.refl (Fin n))).trans (Equiv.boolProdEquivSum (Fin n))
  let q := Equiv.sumCongr pairIndex.symm (Equiv.refl (Fin m))
  let e := (((b.prod b).prod bf).map d).reindex q
  have he0 (i : Fin n) : e (.inl (0, i)) = (b i : E) := by
    dsimp only [e]
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply]
    have hq : q.symm (.inl (0, i)) = .inl (.inl i) := rfl
    rw [hq]
    simp [OrthonormalBasis.prod_apply, hd]
  have he1 (i : Fin n) : e (.inl (1, i)) = K.reflection (b i) := by
    dsimp only [e]
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply]
    have hq : q.symm (.inl (1, i)) = .inl (.inr i) := rfl
    rw [hq]
    simp [OrthonormalBasis.prod_apply, hd]
  have hef (j : Fin m) : e (.inr j) = (bf j : E) := by
    dsimp only [e]
    rw [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply]
    have hq : q.symm (.inr j) = .inr j := rfl
    rw [hq]
    simp [OrthonormalBasis.prod_apply, hd]
  have hJ0 (i) : K.reflection (e (.inl (0, i))) = e (.inl (1, i)) := by rw [he0, he1]
  have hJ1 (i) : K.reflection (e (.inl (1, i))) = e (.inl (0, i)) := by
    rw [he1, K.reflection_reflection, he0]
  have hS0 (i) : S (e (.inl (0, i))) =
      (Real.sin ((alpha i + beta i) / 2) : ℂ) • e (.inl (0, i)) := by
    rw [he0]
    exact (sinAngleOperator_apply_of_paired_phase_eigenvectors_complex K L U hmap
      (b i) (alpha i) (beta i) (hu i) (hw i) (hmean i)).1
  have hS1 (i) : S (e (.inl (1, i))) =
      (Real.sin ((alpha i + beta i) / 2) : ℂ) • e (.inl (1, i)) := by
    rw [he1]
    exact (sinAngleOperator_apply_of_paired_phase_eigenvectors_complex K L U hmap
      (b i) (alpha i) (beta i) (hu i) (hw i) (hmean i)).2
  have hSf (j) : S (e (.inr j)) = (mu j : ℂ) • e (.inr j) := by
    rw [hef]
    exact sinAngleOperator_apply_of_comap_eigenvector K L Z hK hL
      (bf j) (mu j) (hmu j) (hbf j)
  have hPinner (x : E) (hxx : inner ℂ x x = 1)
      (hJx : inner ℂ x (K.reflection x) = 0) :
      inner ℂ x (K.starProjection x) = ((1 / 2 : ℝ) : ℂ) := by
    have h := congrArg (fun y => inner ℂ x y) (Submodule.reflection_apply (K := K) x)
    rw [hJx, inner_sub_right, two_smul, inner_add_right, hxx] at h
    push_cast
    linear_combination -(1 / 2 : ℂ) * h
  let F := fun z : ℂ => (f (Real.arcsin z.re) : ℂ)
  let : IsStarNormal S := (K.isPositive_sinAngleOperator L).isSelfAdjoint.isStarNormal
  let : IsStarNormal S₀ := (K₀.isPositive_sinAngleOperator L₀).isSelfAdjoint.isStarNormal
  have hpair (x : E) (theta : ℝ) (hθ : theta ∈ Set.Icc 0 (Real.pi / 2))
      (hSx : S x = (Real.sin theta : ℂ) • x)
      (hPx : inner ℂ x (K.starProjection x) = ((1 / 2 : ℝ) : ℂ)) :
      (inner ℂ x ((K.starProjection * cfc F S) x)).re = f theta / 2 := by
    change (inner ℂ x (K.starProjection (cfc F S x))).re = _
    rw [ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal F hSx]
    dsimp only [F]
    rw [Complex.ofReal_re,
      Real.arcsin_sin (by linarith [hθ.1, Real.pi_pos]) hθ.2,
      map_smul, inner_smul_right, hPx, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  have hp0 (i) := hpair _ _ (hmean i) (hS0 i)
    (hPinner _ (e.inner_eq_one _) (by rw [hJ0]; exact e.inner_eq_zero (by simp)))
  have hp1 (i) := hpair _ _ (hmean i) (hS1 i)
    (hPinner _ (e.inner_eq_one _) (by rw [hJ1]; exact e.inner_eq_zero (by simp)))
  have hfixed (j) :
      (inner ℂ (e (.inr j)) ((K.starProjection * cfc F S) (e (.inr j)))).re =
        (inner ℂ (bf j) ((K₀.starProjection * cfc F S₀) (bf j))).re := by
    rw [hef]
    change (inner ℂ (bf j : E) (K.starProjection (cfc F S (bf j : E)))).re =
      (inner ℂ (bf j) (K₀.starProjection (cfc F S₀ (bf j)))).re
    rw [ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal F
      (show S (bf j : E) = (mu j : ℂ) • (bf j : E) by simpa only [hef] using hSf j),
      ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal F (hbf j),
      map_smul, map_smul, inner_smul_right, inner_smul_right]
    rw [← starProjection_comap_subtype_apply_of_invariant K Z hK (bf j)]
    rfl
  have hcyc : LinearMap.trace ℂ E (cfc F S * K.starProjection).toLinearMap =
      LinearMap.trace ℂ E (K.starProjection * cfc F S).toLinearMap := LinearMap.trace_mul_comm ℂ _ _
  have hcyc₀ : LinearMap.trace ℂ Z (cfc F S₀ * K₀.starProjection).toLinearMap =
      LinearMap.trace ℂ Z (K₀.starProjection * cfc F S₀).toLinearMap :=
    LinearMap.trace_mul_comm ℂ _ _
  have hlocalEval : (LinearMap.trace ℂ Z (cfc F S₀ * K₀.starProjection).toLinearMap).re =
      ∑ j, (inner ℂ (bf j) ((K₀.starProjection * cfc F S₀) (bf j))).re := by
    rw [hcyc₀, LinearMap.trace_eq_sum_inner _ bf, Complex.re_sum]
    rfl
  have htrace : (LinearMap.trace ℂ E (cfc F S * K.starProjection).toLinearMap).re =
      (∑ i, f ((alpha i + beta i) / 2)) +
        (LinearMap.trace ℂ Z (cfc F S₀ * K₀.starProjection).toLinearMap).re := by
    rw [hcyc, LinearMap.trace_eq_sum_inner _ e, Complex.re_sum,
      Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two]
    simp only [ContinuousLinearMap.coe_coe, hp0, hp1, hfixed]
    rw [hlocalEval]
    apply congrArg₂ (· + ·) _ rfl
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hglobal := K.re_trace_cfc_sinAngleOperator_mul_starProjection L
    (fun s => f (Real.arcsin s)) (by simpa using hf)
  have hlocal := K₀.re_trace_cfc_sinAngleOperator_mul_starProjection L₀
    (fun s => f (Real.arcsin s)) (by simpa using hf)
  have hglobal' : (LinearMap.trace ℂ E (cfc F S * K.starProjection).toLinearMap).re =
      ∑ i : Fin (Module.finrank ℂ K), f (K.principalAngles L i) := by
    simpa only [← principalAngles_apply] using hglobal
  have hlocal' : (LinearMap.trace ℂ Z (cfc F S₀ * K₀.starProjection).toLinearMap).re =
      ∑ j : Fin (Module.finrank ℂ K₀), f (K₀.principalAngles L₀ j) := by
    simpa only [← principalAngles_apply] using hlocal
  exact hglobal'.symm.trans (htrace.trans
    (congrArg (fun t => (∑ i, f ((alpha i + beta i) / 2)) + t) hlocal'))

end Submodule
