/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SchattenOptimizerPhases
public import DavisKahan.FiniteDimensional.DirectRotation.SchattenLocalGlobal

/-!
# Every acute Schatten optimizer commutes with canonical rotation

The actual paired basis diagonalizes the optimizer and canonical rotation
simultaneously. On the exceptional gradient kernel, acuteness forces the
optimizer to be identity. Source invariance makes the projections agree
there, so canonical rotation is identity as well. Completeness gives
commutation on the whole ambient space, with arbitrary multiplicities.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- At an acute local minimum, both the optimizer and every completed
canonical rotation fix the actual gradient kernel pointwise. -/
theorem optimizer_and_canonical_fix_gradient_kernel_of_isLocalMinOn_acute_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (hacute : ∀ i : ℕ, K.principalAngles L i < Real.pi / 2)
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    ∀ x, schattenUnitaryGradient p.toReal (U : E →L[ℂ] E) x = 0 →
      (U : E →L[ℂ] E) x = x ∧ nonacuteDirectRotation K L D x = x := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let Z := G.toLinearMap.ker
  let R := nonacuteDirectRotation K L D
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  have hUfix := apply_eq_self_on_gradient_kernel_of_isMinOn_acute_transports_complex
    p hp hp1 hp2 K L U hmap
    (isMinOn_of_isLocalMinOn_transports_complex p hp hp1 hp2 K L U hmap hmin) hacute
  have hG : IsSelfAdjoint G := isSelfAdjoint_schattenUnitaryGradient _ _
  have hPK := (gradient_square_reduces_projections_of_isLocalMinOn_transports
    p hp hp1 K L.starProjection U ht hmin).1
  have hPZ : ∀ x ∈ Z, K.starProjection x ∈ Z :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute K.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPK.eq)
  intro x hx
  refine ⟨hUfix x hx, ?_⟩
  have hz : x ∈ Z := hx
  have hRfix : R x = x := by
    have hstar := congrArg (fun A : E →L[ℂ] E => A x)
      (Unitary.star_mul_self_of_mem U.property)
    change star (U : E →L[ℂ] E) ((U : E →L[ℂ] E) x) = x at hstar
    rw [hUfix x hx] at hstar
    have hPQ := congrArg (fun A : E →L[ℂ] E => A x) ht
    change (U : E →L[ℂ] E) (K.starProjection (star (U : E →L[ℂ] E) x)) =
      L.starProjection x at hPQ
    rw [hstar, hUfix _ (hPZ x hz)] at hPQ
    exact nonacuteDirectRotation_apply_eq_self_of_projections_eq K L D x hPQ
  exact hRfix

/-- Every local Schatten minimum for an acute pair commutes with its
canonical rotation, at every finite rank and with arbitrary angle
multiplicities, including zero and critical angles. -/
theorem commute_canonicalRotation_of_isLocalMinOn_acute_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (hacute : ∀ i : ℕ, K.principalAngles L i < Real.pi / 2)
    (D : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L) :
    Commute (U : E →L[ℂ] E) (nonacuteDirectRotation K L D) := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
  let Z := G.toLinearMap.ker
  let R := nonacuteDirectRotation K L D
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  have hfix := optimizer_and_canonical_fix_gradient_kernel_of_isLocalMinOn_acute_transports_complex
    p hp hp1 hp2 K L U hmap hmin hacute D
  have hUfix (x : E) (hx : G x = 0) : (U : E →L[ℂ] E) x = x := (hfix x hx).1
  have hRfix (z : Z) : R (z : E) = (z : E) := (hfix z z.property).2
  obtain ⟨n, e, theta, eps, _, _, hu, hw, hR0, hR1, _, _, _, _⟩ :=
    positive_gradient_canonical_relative_phase_basis_of_isLocalMinOn_complex
      p hp hp1 hp2 K L U hmap hmin D
  change ∀ i, R (e i : E) = Complex.exp ((theta i : ℂ) * Complex.I) • (e i : E) at hR0
  change ∀ i, R (K.reflection (e i)) =
    Complex.exp (((-theta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i) at hR1
  have hH : (U : E →L[ℂ] E).toLinearMap ∘ₗ R.toLinearMap ∘ₗ H.subtype =
      R.toLinearMap ∘ₗ (U : E →L[ℂ] E).toLinearMap ∘ₗ H.subtype := by
    apply e.toBasis.ext
    intro i
    change (U : E →L[ℂ] E) (R (e i : E)) = R ((U : E →L[ℂ] E) (e i : E))
    simp only [hR0, hu, map_smul, smul_smul, mul_comm]
  have hJH : (U : E →L[ℂ] E).toLinearMap ∘ₗ R.toLinearMap ∘ₗ
      K.reflection.toLinearMap ∘ₗ H.subtype =
      R.toLinearMap ∘ₗ (U : E →L[ℂ] E).toLinearMap ∘ₗ
        K.reflection.toLinearMap ∘ₗ H.subtype := by
    apply e.toBasis.ext
    intro i
    change (U : E →L[ℂ] E) (R (K.reflection (e i))) =
      R ((U : E →L[ℂ] E) (K.reflection (e i)))
    simp only [hR1, hw, map_smul, smul_smul, mul_comm]
  have hkernel (z : Z) : (U : E →L[ℂ] E) (R z) = R ((U : E →L[ℂ] E) z) := by
    calc
      _ = (U : E →L[ℂ] E) z := congrArg (U : E →L[ℂ] E) (hRfix z)
      _ = (z : E) := hUfix z z.property
      _ = _ := by rw [hUfix z z.property, hRfix]
  obtain ⟨_, _, _, _, _, _, _, d, _, _, _, _, hd, _, _, _, _, _, _⟩ :=
    schatten_transport_spectral_decomposition_of_isLocalMinOn_complex p hp hp1 hp2
      K L.starProjection U ht hmin
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := d.surjective x
  change (U : E →L[ℂ] E) (R (d y)) = R ((U : E →L[ℂ] E) (d y))
  rw [hd]
  simp only [map_add]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (LinearMap.congr_fun hH y.fst.fst)
      (LinearMap.congr_fun hJH y.fst.snd)) (hkernel y.snd)

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
