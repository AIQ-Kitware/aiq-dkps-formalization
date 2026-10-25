/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenReflectingDescent
public import ForTauCeti.Analysis.InnerProductSpace.PlanarReflection
public import ForTauCeti.Analysis.InnerProductSpace.Projection.TwoBlocks

/-!
# Reflecting blocks at complex Schatten local minima

The source projection and reflecting transporter determine their own
normal coordinates. Combining those coordinates with feasible descent
forces a nonidentity reflecting local minimum to exchange the source
and its orthogonal complement. No real matrix or basis is prescribed.
The complete two-projection decomposition then gives fixed/right blocks
on the actual zero-gradient kernel of every ambient local minimum.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A self-adjoint local minimum commuting with its self-adjoint source
is the identity. No dimension restriction is needed, and the nuclear
endpoint is included. -/
theorem eq_one_of_isLocalMinOn_selfAdjoint_commuting_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (P R : E →L[ℂ] E) (hP : IsSelfAdjoint P)
    (hR : R ∈ unitary (E →L[ℂ] E)) (hself : IsSelfAdjoint R) (hcomm : Commute R P)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = R * P * star R} R) : R = 1 := by
  have hno : ∀ x : E, R x = -x → x = 0 := by
    apply no_neg_one_of_isLocalMinOn_transports_of_source_invariant_complex
      p hp (Unitary.linearIsometryEquiv ⟨R, hR⟩) P hP hmin
    intro x hx
    change R x = -x at hx
    change R (P x) = -(P x)
    calc
      R (P x) = P (R x) := congrArg (fun A : E →L[ℂ] E => A x) hcomm.eq
      _ = -(P x) := by rw [hx, map_neg]
  have hsq : R * R = 1 := by
    simpa only [hself.star_eq] using Unitary.star_mul_self_of_mem hR
  have hRR (x : E) : R (R x) = x := congrArg (fun A : E →L[ℂ] E => A x) hsq
  apply ContinuousLinearMap.ext
  intro x
  change R x = x
  have hn : R (x - R x) = -(x - R x) := by rw [map_sub, hRR]; abel
  exact (sub_eq_zero.mp (hno _ hn)).symm

/-- A source-commuting involutive restriction at an ambient local
minimum fixes its whole invariant subspace. The remaining ambient
unitary action is unrestricted, and the nuclear endpoint is included. -/
theorem fixes_invariant_subspace_of_isLocalMinOn_involutive_commuting_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : E ≃ₗᵢ[ℂ] E) (P : E →L[ℂ] E) (hP : IsSelfAdjoint P)
    (N : Submodule ℂ E) (hTN : ∀ x ∈ N, T x ∈ N) (hPN : ∀ x ∈ N, P x ∈ N)
    (hTT : ∀ x ∈ N, T (T x) = x) (hcomm : ∀ x ∈ N, T (P x) = P (T x))
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧
        W * P * star W = (T : E →L[ℂ] E) * P * star (T : E →L[ℂ] E)}
      (T : E →L[ℂ] E)) : ∀ x ∈ N, T x = x := by
  let M := N ⊓ (T.toLinearMap + LinearMap.id).ker
  have hMmem (x : E) : x ∈ M ↔ x ∈ N ∧ T x = -x := by
    change (x ∈ N ∧ T x + x = 0) ↔ (x ∈ N ∧ T x = -x)
    rw [add_eq_zero_iff_eq_neg]
  have hPM : ∀ x ∈ M, P x ∈ M := by
    intro x hx
    obtain ⟨hxN, hxneg⟩ := (hMmem x).mp hx
    refine (hMmem (P x)).mpr ⟨hPN x hxN, ?_⟩
    rw [hcomm x hxN, hxneg, map_neg]
  intro x hx
  by_contra hTx
  have hy : T (x - T x) = -(x - T x) := by rw [map_sub, hTT x hx]; abel
  have hyM : x - T x ∈ M := (hMmem _).mpr ⟨N.sub_mem hx (hTN x hx), hy⟩
  have hM : M ≠ ⊥ := by
    intro hbot
    rw [hbot] at hyM
    exact hTx (sub_eq_zero.mp hyM).symm
  exact not_isLocalMinOn_of_negative_identity_on_invariant_subspace_complex
    p hp T P hP M hM (fun y hy => ((hMmem y).mp hy).2) hPM hmin

/-- A nonidentity self-adjoint local transport minimum on a complex
plane exchanges the source with its orthogonal complement. The source
projection is nonconstant; all feasible ambient unitary competitors
are included. This holds for every finite Schatten exponent above one. -/
theorem conjugate_eq_one_sub_of_isLocalMinOn_reflecting_plane_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (P R : E →L[ℂ] E) (hP : IsStarProjection P)
    (hR : R ∈ unitary (E →L[ℂ] E)) (hself : IsSelfAdjoint R)
    (hE : Module.finrank ℂ E = 2) (hzero : P ≠ 0) (hone : P ≠ 1)
    (hpos : R ≠ 1)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = R * P * star R} R) :
    R * P * star R = 1 - P := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ E)
  have hneg : R ≠ -1 := by
    intro h
    rw [h] at hmin
    apply ReflectingVariation.not_isLocalMinOn_negative_identity p hp P
    simpa only [star_neg, star_one, neg_mul, one_mul, mul_neg, mul_one, neg_neg] using hmin
  obtain ⟨e, d, k, hdk, _, hPcoord, hRcoord⟩ :=
    PlanarReflection.exists_source_reflection_coordinates P R hP hR hself
      hE hzero hone hpos hneg
  have hPc : e.conjStarAlgEquiv ReflectingVariation.sourceProjection = P := hPcoord
  have hRc : e.conjStarAlgEquiv (ReflectingVariation.variation d k 0) = R := by
    rw [ReflectingVariation.variation_zero]
    exact hRcoord
  have hlocal := isLocalMinOn_transport_of_conj_linearIsometryEquiv p hp e
    (ReflectingVariation.variation d k 0) ReflectingVariation.sourceProjection
    (ReflectingVariation.variation_mem_unitary d k hdk 0)
    (by simpa only [hPc, hRc] using hmin)
  have hd : d = 0 := by
    by_contra hd
    exact ReflectingVariation.not_isLocalMinOn_reflecting_transports p hp hp1 d k hdk hd hlocal
  subst d
  have hk : k ^ 2 = 1 := by simpa only [zero_pow (by decide : 2 ≠ 0), zero_add] using hdk
  have hmat : ReflectingVariation.reflectionMatrix 0 k * Matrix.diagonal ![1, 0] *
      star (ReflectingVariation.reflectionMatrix 0 k) = 1 - Matrix.diagonal ![1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ReflectingVariation.reflectionMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_apply, Matrix.vecMul, dotProduct]
    exact_mod_cast (show k * k = 1 by nlinarith [hk])
  have hmodel : ReflectingVariation.variation 0 k 0 * ReflectingVariation.sourceProjection *
      star (ReflectingVariation.variation 0 k 0) = 1 - ReflectingVariation.sourceProjection := by
    rw [ReflectingVariation.variation_zero]
    simpa only [map_mul, map_star, map_sub, map_one, ReflectingVariation.sourceProjection] using
      congrArg (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) hmat
  calc
    R * P * star R = e.conjStarAlgEquiv
        (ReflectingVariation.variation 0 k 0 * ReflectingVariation.sourceProjection *
          star (ReflectingVariation.variation 0 k 0)) := by
      rw [map_mul, map_mul, map_star, hPc, hRc]
    _ = e.conjStarAlgEquiv (1 - ReflectingVariation.sourceProjection) := by rw [hmodel]
    _ = 1 - P := by rw [map_sub, map_one, hPc]

/-- Every self-adjoint local minimum on a complex plane is the identity
or exchanges the source and its complement. Zero and full source spaces
are included and force the identity case. This is a necessary condition
for local minimality over all unitary transporters. -/
theorem eq_one_or_conjugate_eq_one_sub_of_isLocalMinOn_reflecting_plane_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (P R : E →L[ℂ] E) (hP : IsStarProjection P)
    (hR : R ∈ unitary (E →L[ℂ] E)) (hself : IsSelfAdjoint R)
    (hE : Module.finrank ℂ E = 2)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * P * star W = R * P * star R} R) :
    R = 1 ∨ R * P * star R = 1 - P := by
  by_cases hpos : R = 1
  · exact Or.inl hpos
  right
  by_cases hzero : P = 0
  · exact False.elim (hpos (eq_one_of_isLocalMinOn_selfAdjoint_commuting_complex
      p hp P R hP.isSelfAdjoint hR hself (by rw [hzero]; exact Commute.zero_right R) hmin))
  by_cases hone : P = 1
  · exact False.elim (hpos (eq_one_of_isLocalMinOn_selfAdjoint_commuting_complex
      p hp P R hP.isSelfAdjoint hR hself (by rw [hone]; exact Commute.one_right R) hmin))
  exact conjugate_eq_one_sub_of_isLocalMinOn_reflecting_plane_complex
    p hp hp1 P R hP hR hself hE hzero hone hpos hmin

/-- Every actual invariant involutive plane at an ambient local minimum
is fixed pointwise or exchanges its source with its orthogonal complement.
Zero and full source restrictions and the identity restriction are included.
The remaining ambient unitary action is unrestricted, and no coordinates
or restricted operators are supplied. -/
theorem fixes_or_exchanges_source_complement_on_invariant_plane_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (T : E ≃ₗᵢ[ℂ] E) (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (N : Submodule ℂ E) (hN : Module.finrank ℂ N = 2)
    (hTN : ∀ x ∈ N, T x ∈ N) (hPN : ∀ x ∈ N, P x ∈ N)
    (hTT : ∀ x ∈ N, T (T x) = x)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧
        W * P * star W = (T : E →L[ℂ] E) * P * star (T : E →L[ℂ] E)}
      (T : E →L[ℂ] E)) :
    (∀ x ∈ N, T x = x) ∨ (∀ x ∈ N, T (P (T x)) = x - P x) := by
  obtain ⟨V, hV, hlocal⟩ := exists_isLocalMinOn_restriction_of_invariant
    p hp T P hP.isSelfAdjoint N hTN hPN hmin
  let P₀ : N →L[ℂ] N := (P.toLinearMap.restrict hPN).toContinuousLinearMap
  have hP₀ : IsStarProjection P₀ := by
    refine ⟨?_, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (hP.isSelfAdjoint.isSymmetric.restrict_invariant hPN)⟩
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change P (P x) = P x
    exact congrArg (fun A : E →L[ℂ] E => A x) hP.isIdempotentElem.eq
  have hVsq : (V : N →L[ℂ] N) * (V : N →L[ℂ] N) = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (V (V x) : E) = (x : E)
    rw [hV, hV, hTT x x.property]
  have hVunit : (V : N →L[ℂ] N) ∈ unitary (N →L[ℂ] N) :=
    (Unitary.linearIsometryEquiv.symm V).property
  have hVself : IsSelfAdjoint (V : N →L[ℂ] N) := by
    change star (V : N →L[ℂ] N) = (V : N →L[ℂ] N)
    calc
      _ = star (V : N →L[ℂ] N) * ((V : N →L[ℂ] N) * (V : N →L[ℂ] N)) := by
        rw [hVsq, mul_one]
      _ = (star (V : N →L[ℂ] N) * (V : N →L[ℂ] N)) * (V : N →L[ℂ] N) :=
        (mul_assoc _ _ _).symm
      _ = (V : N →L[ℂ] N) := by rw [Unitary.star_mul_self_of_mem hVunit, one_mul]
  rcases eq_one_or_conjugate_eq_one_sub_of_isLocalMinOn_reflecting_plane_complex
    p hp hp1 P₀ (V : N →L[ℂ] N) hP₀ hVunit hVself hN hlocal with hVeq | hconj
  · left
    intro x hx
    have hv := congrArg (fun A : N →L[ℂ] N => (A ⟨x, hx⟩ : E)) hVeq
    exact (hV ⟨x, hx⟩).symm.trans hv
  · right
    rw [hVself.star_eq] at hconj
    intro x hx
    have h := congrArg (fun A : N →L[ℂ] N => (A ⟨x, hx⟩ : E)) hconj
    change (V (P₀ (V ⟨x, hx⟩)) : E) = x - P x at h
    rw [hV] at h
    change T (P (V ⟨x, hx⟩)) = x - P x at h
    rwa [hV] at h

/-- On every actual common invariant block of dimension at most two,
an involutive ambient local minimum is fixed or exchanges the source
and its complement. A one-dimensional block is necessarily fixed. -/
theorem fixes_or_exchanges_source_complement_on_small_invariant_block_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (T : E ≃ₗᵢ[ℂ] E) (P : E →L[ℂ] E) (hP : IsStarProjection P)
    (N : Submodule ℂ E) (hN : Module.finrank ℂ N ≤ 2)
    (hTN : ∀ x ∈ N, T x ∈ N) (hPN : ∀ x ∈ N, P x ∈ N)
    (hTT : ∀ x ∈ N, T (T x) = x)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧
        W * P * star W = (T : E →L[ℂ] E) * P * star (T : E →L[ℂ] E)}
      (T : E →L[ℂ] E)) :
    (∀ x ∈ N, T x = x) ∨
      (Module.finrank ℂ N = 2 ∧ ∀ x ∈ N, T (P (T x)) = x - P x) := by
  by_cases hdim : Module.finrank ℂ N = 2
  · rcases fixes_or_exchanges_source_complement_on_invariant_plane_of_isLocalMinOn_complex
      p hp hp1 T P hP N hdim hTN hPN hTT hmin with hfix | hexchange
    · exact Or.inl hfix
    · exact Or.inr ⟨hdim, hexchange⟩
  left
  have hdim1 : Module.finrank ℂ N ≤ 1 := by omega
  let A := (T.toLinearMap.restrict hTN).toContinuousLinearMap
  let B := (P.toLinearMap.restrict hPN).toContinuousLinearMap
  have hcomm := ContinuousLinearMap.commute_of_finrank_le_one A B hdim1
  apply fixes_invariant_subspace_of_isLocalMinOn_involutive_commuting_complex
    p hp T P hP.isSelfAdjoint N hTN hPN hTT _ hmin
  intro x hx
  exact congrArg (fun C : N →L[ℂ] N => (C ⟨x, hx⟩ : E)) hcomm.eq

/-- An arbitrary-rank reflecting local minimum has a complete orthogonal
family of actual common invariant blocks. Every block is fixed pointwise
or is a two-plane exchanging its source and complementary sectors.
The family is constructed from the source and negative-phase projections. -/
theorem exists_fixed_or_right_orthogonal_blocks_of_isLocalMinOn_reflection_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (T : E ≃ₗᵢ[ℂ] E) (P S : E →L[ℂ] E) (hP : IsStarProjection P) (hS : IsStarProjection S)
    (hT : (T : E →L[ℂ] E) = 1 - (2 : ℂ) • S)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧
        W * P * star W = (T : E →L[ℂ] E) * P * star (T : E →L[ℂ] E)}
      (T : E →L[ℂ] E)) :
    ∃ F : Finset (Submodule ℂ E),
      (∀ N ∈ F, N ≠ ⊥ ∧ Module.finrank ℂ N ≤ 2 ∧
        (∀ x ∈ N, P x ∈ N) ∧ (∀ x ∈ N, T x ∈ N) ∧
        ((∀ x ∈ N, T x = x) ∨
          (Module.finrank ℂ N = 2 ∧ ∀ x ∈ N, T (P (T x)) = x - P x))) ∧
      (F : Set (Submodule ℂ E)).Pairwise Submodule.IsOrtho ∧ F.sup id = ⊤ := by
  have hact (x : E) : T x = x - (2 : ℂ) • S x :=
    congrArg (fun A : E →L[ℂ] E => A x) hT
  have hSS (x : E) : S (S x) = S x :=
    congrArg (fun A : E →L[ℂ] E => A x) hS.isIdempotentElem.eq
  have hTT (x : E) : T (T x) = x := by
    calc
      T (T x) = T (x - (2 : ℂ) • S x) := congrArg T (hact x)
      _ = T x - (2 : ℂ) • T (S x) := by rw [map_sub, map_smul]
      _ = (x - (2 : ℂ) • S x) - (2 : ℂ) • (S x - (2 : ℂ) • S (S x)) := by
        rw [hact x, hact (S x)]
      _ = x := by rw [hSS]; module
  obtain ⟨F, hF, horth, hspan⟩ := exists_orthogonal_blocks_of_two_projections P S hP hS
  refine ⟨F, ?_, horth, hspan⟩
  intro N hN
  obtain ⟨hN0, hdim, hPN, hSN⟩ := hF N hN
  have hTN : ∀ x ∈ N, T x ∈ N := by
    intro x hx
    rw [hact]
    exact N.sub_mem hx (N.smul_mem _ (hSN x hx))
  exact ⟨hN0, hdim, hPN, hTN,
    fixes_or_exchanges_source_complement_on_small_invariant_block_of_isLocalMinOn_complex
      p hp hp1 T P hP N hdim hTN hPN (fun x _ => hTT x) hmin⟩

/-- The actual zero-gradient kernel of every ambient local minimum has
a complete orthogonal fixed/right decomposition, at arbitrary rank.
The kernel restriction, its source projection and all blocks are derived
from the original transporter and subspace. No supplied model is assumed. -/
theorem gradient_kernel_fixed_or_right_blocks_of_isLocalMinOn_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (K : Submodule ℂ E) (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) :
    let Z := (schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).toLinearMap.ker
    let P₀ := (K.comap Z.subtype).starProjection
    ∃ R : Z ≃ₗᵢ[ℂ] Z, (∀ z : Z, (R z : E) = (U : E →L[ℂ] E) z) ∧
      ∃ F : Finset (Submodule ℂ Z),
        (∀ N ∈ F, N ≠ ⊥ ∧ Module.finrank ℂ N ≤ 2 ∧
          (∀ z ∈ N, P₀ z ∈ N) ∧ (∀ z ∈ N, R z ∈ N) ∧
          ((∀ z ∈ N, R z = z) ∨
            (Module.finrank ℂ N = 2 ∧ ∀ z ∈ N, R (P₀ (R z)) = z - P₀ z))) ∧
        (F : Set (Submodule ℂ Z)).Pairwise Submodule.IsOrtho ∧ F.sup id = ⊤ := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let Z := G.toLinearMap.ker
  let P₀ := (K.comap Z.subtype).starProjection
  obtain ⟨R, S, hS, hR, hrepr⟩ := gradient_kernel_reflection_representation
    p.toReal (by linarith : 0 < p.toReal) U
  have hcomm := (gradient_square_reduces_projections_of_isLocalMinOn_transports
    p hp hp1 K Q U htrans hmin).1
  have hPK : ∀ x ∈ Z, K.starProjection x ∈ Z := by
    exact (isSelfAdjoint_schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).isSymmetric
      |>.mapsTo_ker_of_commute_square
        (show Commute K.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
          congrArg ContinuousLinearMap.toLinearMap hcomm.eq)
  have hUK : ∀ x ∈ Z, (Unitary.linearIsometryEquiv U) x ∈ Z := by
    intro x hx
    change (U : E →L[ℂ] E) x ∈ Z
    rw [← hR ⟨x, hx⟩]
    exact (R ⟨x, hx⟩).property
  have hlocalAmbient : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W =
        (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E)}
      (U : E →L[ℂ] E) := by simpa only [htrans] using hmin
  obtain ⟨V, hV, hlocal⟩ := exists_isLocalMinOn_restriction_of_invariant
    p hp (Unitary.linearIsometryEquiv U) K.starProjection (isSelfAdjoint_starProjection K)
    Z hUK hPK hlocalAmbient
  have hVR : V = R := by
    apply LinearIsometryEquiv.ext
    intro z
    apply Subtype.ext
    exact (hV z).trans (hR z).symm
  have hPres : (K.starProjection.toLinearMap.restrict hPK).toContinuousLinearMap = P₀ := by
    apply ContinuousLinearMap.ext
    intro z
    apply Subtype.ext
    exact (Submodule.starProjection_comap_subtype_apply_of_invariant K Z hPK z).symm
  rw [hVR, hPres] at hlocal
  exact ⟨R, hR, exists_fixed_or_right_orthogonal_blocks_of_isLocalMinOn_reflection_complex
    p hp hp1 R P₀ S isStarProjection_starProjection hS hrepr hlocal⟩

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
