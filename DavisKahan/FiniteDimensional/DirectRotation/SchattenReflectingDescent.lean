/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenReflectingVariation
public import ForTauCeti.Analysis.InnerProductSpace.SchattenTransportRestriction
public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimizerKernel

/-!
# Reflecting blocks at an unrestricted ambient local minimum

The exact planar descent can be inserted into any actual orthogonal
reducing decomposition while fixing its remaining unitary block. Thus an
ambient local minimum cannot contain a reflecting plane with nonzero
diagonal parameter. This is the exceptional-block exclusion used in the
proposed Schatten local-to-global theorem; extracting every such block
from an arbitrary gradient kernel remains a separate geometric step.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open scoped ENNReal

variable {E R : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [FiniteDimensional ℂ R] [CompleteSpace R]

/-- Every actual reflecting two-plane at an ambient local minimum must
have zero diagonal parameter. Competitors range over all ambient complex
unitary transports; the complementary unitary block is arbitrary.
The conclusion holds for every finite Schatten exponent greater than one. -/
theorem reflecting_block_eq_zero_of_isLocalMinOn_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (hp1 : 1 < p.toReal)
    (d k : ℝ) (hdk : d ^ 2 + k ^ 2 = 1)
    (e : WithLp 2 (ReflectingVariation.Plane × R) ≃ₗᵢ[ℂ] E)
    (V : unitary (R →L[ℂ] R)) (P₀ : R →L[ℂ] R)
    (hmin :
      let W := e.conjStarAlgEquiv ((ReflectingVariation.variation d k 0).withLpProdMap 2
        (V : R →L[ℂ] R))
      let P := e.conjStarAlgEquiv (ReflectingVariation.sourceProjection.withLpProdMap 2 P₀)
      IsLocalMinOn
        (fun T : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
          (LinearMap.id - T.toLinearMap) ^ p.toReal)
        {T | T ∈ unitary (E →L[ℂ] E) ∧ T * P * star T = W * P * star W} W) : d = 0 := by
  by_contra hd0
  apply ReflectingVariation.not_isLocalMinOn_reflecting_transports p hp hp1 d k hdk hd0
  exact isLocalMinOn_block_transport_of_orthogonal_sum p hp e
    (ReflectingVariation.variation d k 0) (ReflectingVariation.variation_mem_unitary d k hdk 0)
    V ReflectingVariation.sourceProjection P₀ hmin

/-- A nonzero reducing block on which the transporter is minus the
identity cannot occur at an ambient local minimum. This includes the
one-dimensional negative blocks in the two-projection decomposition. -/
theorem not_isLocalMinOn_of_negative_identity_block_complex
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] [CompleteSpace F] [Nontrivial F]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (e : WithLp 2 (F × R) ≃ₗᵢ[ℂ] E)
    (V : unitary (R →L[ℂ] R)) (P₁ : F →L[ℂ] F) (P₀ : R →L[ℂ] R) :
    let W := e.conjStarAlgEquiv ((-1 : F →L[ℂ] F).withLpProdMap 2 (V : R →L[ℂ] R))
    let P := e.conjStarAlgEquiv (P₁.withLpProdMap 2 P₀)
    ¬ IsLocalMinOn
      (fun T : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - T.toLinearMap) ^ p.toReal)
      {T | T ∈ unitary (E →L[ℂ] E) ∧ T * P * star T = W * P * star W} W := by
  dsimp only
  intro hmin
  have hU : (-1 : F →L[ℂ] F) ∈ unitary (F →L[ℂ] F) := by
    simp [Unitary.mem_iff]
  have hrestrict := isLocalMinOn_block_transport_of_orthogonal_sum p hp e
    (-1 : F →L[ℂ] F) hU V P₁ P₀ hmin
  apply ReflectingVariation.not_isLocalMinOn_negative_identity p hp P₁
  simpa only [star_neg, star_one, neg_mul, one_mul, mul_neg, mul_one, neg_neg] using hrestrict

/-- A nonzero source-invariant subspace on which the actual transporter
is minus the identity excludes ambient local minimality. The orthogonal
coordinates and the complementary unitary restriction are constructed,
not supplied. The source operator need only be self-adjoint. -/
theorem not_isLocalMinOn_of_negative_identity_on_invariant_subspace_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : E ≃ₗᵢ[ℂ] E) (P : E →L[ℂ] E) (hP : IsSelfAdjoint P)
    (N : Submodule ℂ E) (hN : N ≠ ⊥)
    (hTN : ∀ x ∈ N, T x = -x) (hPN : ∀ x ∈ N, P x ∈ N) :
    ¬ IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧
        W * P * star W = (T : E →L[ℂ] E) * P * star (T : E →L[ℂ] E)}
      (T : E →L[ℂ] E) := by
  let : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN
  have hTinv : ∀ x ∈ N, T x ∈ N := by
    intro x hx
    rw [hTN x hx]
    exact N.neg_mem hx
  obtain ⟨_, _, _, hTred⟩ := T.exists_restriction_of_finite_invariant N hTinv
  have hTorth : ∀ x ∈ Nᗮ, T x ∈ Nᗮ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem T.toLinearMap).mp
      hTred.orthogonal_mem_invtSubmodule
  obtain ⟨V, hV, _, _⟩ := T.exists_restriction_of_finite_invariant Nᗮ hTorth
  have hPorth : ∀ x ∈ Nᗮ, P x ∈ Nᗮ := by
    intro x hx y hy
    exact (hP.isSymmetric y x).symm.trans (hx (P y) (hPN y hy))
  let P₁ : N →L[ℂ] N := (P.toLinearMap.restrict hPN).toContinuousLinearMap
  let P₀ : Nᗮ →L[ℂ] Nᗮ := (P.toLinearMap.restrict hPorth).toContinuousLinearMap
  let e := N.orthogonalDecomposition.symm
  have hTblock : e.conjStarAlgEquiv
      ((-1 : N →L[ℂ] N).withLpProdMap 2 (V : Nᗮ →L[ℂ] Nᗮ)) =
        (T : E →L[ℂ] E) := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.symm_apply_apply,
      ContinuousLinearMap.withLpProdMap_apply]
    change -(y.fst : E) + (V y.snd : E) = T ((y.fst : E) + (y.snd : E))
    rw [map_add, hTN y.fst y.fst.property, hV]
  have hPblock : e.conjStarAlgEquiv (P₁.withLpProdMap 2 P₀) = P := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.symm_apply_apply,
      ContinuousLinearMap.withLpProdMap_apply]
    change P (y.fst : E) + P (y.snd : E) = P ((y.fst : E) + (y.snd : E))
    exact (map_add P _ _).symm
  have hexclude := not_isLocalMinOn_of_negative_identity_block_complex p hp e
    (Unitary.linearIsometryEquiv.symm V) P₁ P₀
  dsimp only at hexclude
  rw [Unitary.coe_symm_linearIsometryEquiv_apply, hTblock, hPblock] at hexclude
  exact hexclude

/-- If the negative eigenspace is source-invariant, an actual local
transport minimum has no negative eigenvectors. This includes the
nuclear endpoint and requires no prescribed decomposition. -/
theorem no_neg_one_of_isLocalMinOn_transports_of_source_invariant_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : E ≃ₗᵢ[ℂ] E) (P : E →L[ℂ] E) (hP : IsSelfAdjoint P)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧
        W * P * star W = (T : E →L[ℂ] E) * P * star (T : E →L[ℂ] E)}
      (T : E →L[ℂ] E))
    (hinv : ∀ x : E, T x = -x → T (P x) = -(P x)) :
    ∀ x : E, T x = -x → x = 0 := by
  let N := (T.toLinearMap + LinearMap.id).ker
  have hNmem (x : E) : x ∈ N ↔ T x = -x := by
    change T x + x = 0 ↔ T x = -x
    exact add_eq_zero_iff_eq_neg
  intro x hx
  by_contra hx0
  have hN : N ≠ ⊥ := by
    intro hbot
    have hxN := (hNmem x).mpr hx
    rw [hbot] at hxN
    exact hx0 hxN
  exact not_isLocalMinOn_of_negative_identity_on_invariant_subspace_complex
    p hp T P hP N hN (fun y hy => (hNmem y).mp hy)
    (fun y hy => (hNmem (P y)).mpr (hinv y ((hNmem y).mp hy))) hmin

/-- Source invariance of the actual negative eigenspace suffices for
the pure Schatten local-to-global theorem. Local minimality itself then
excludes that eigenspace. The other spectral spaces are unrestricted. -/
theorem isMinOn_of_isLocalMinOn_transports_of_negative_eigenspace_invariant_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (hinv : ∀ x : E, (U : E →L[ℂ] E) x = -x →
      (U : E →L[ℂ] E) (K.starProjection x) = -(K.starProjection x)) :
    IsMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E) := by
  apply isMinOn_of_isLocalMinOn_transports_of_no_neg_one_complex
    p hp hp1 hp2 K L U hmap hmin
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  apply no_neg_one_of_isLocalMinOn_transports_of_source_invariant_complex
    p hp (Unitary.linearIsometryEquiv U) K.starProjection
    (isSelfAdjoint_starProjection K)
  · simpa only [Unitary.coe_linearIsometryEquiv_apply, ht] using hmin
  · exact hinv

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
