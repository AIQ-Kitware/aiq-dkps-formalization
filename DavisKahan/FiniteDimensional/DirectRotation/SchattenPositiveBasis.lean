/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGradientPlanes
import ForTauCeti.Analysis.InnerProductSpace.PairedSpectralDecomposition

/-!
# Simultaneous phase coordinates on the whole positive gradient space

The symmetric gradient restricted to its positive point-spectral space has
an internal orthogonal eigenspace decomposition. On each level we use the
phase basis supplied by constrained local minimality, rather than an arbitrary
spectral basis. Mathlib's collected orthonormal basis then combines the levels
without losing the transporter or reflection-paired eigenvector equations.

This constructs coordinates on the entire positive space, including repeated
levels and the maximal level. Pairing this basis by source reflection and
adjoining the gradient kernel gives the subsequent ambient decomposition.
The construction also permits the positive space to be zero-dimensional.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

set_option maxHeartbeats 800000 in
/-- The entire positive gradient space at a constrained local minimum has
an orthonormal phase basis. Source reflection pairs every vector with an
opposite-gradient eigenvector, and every pair attains its exact scalar cost. -/
theorem positive_gradient_phase_basis_of_isLocalMinOn_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) :
    let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
    let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
    ∃ n : ℕ, ∃ (e : OrthonormalBasis (Fin n) ℂ H) (g alpha beta : Fin n → ℝ),
      (∀ i, 0 < g i) ∧
      (∀ i, G (e i : E) = (g i : ℂ) • (e i : E)) ∧
      (∀ i, (U : E →L[ℂ] E) (e i : E) =
        Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E)) ∧
      (∀ i, (U : E →L[ℂ] E) (K.reflection (e i)) =
        Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i)) ∧
      (∀ i, (alpha i + beta i) / 2 ∈ Ioo 0 (Real.pi / 2)) ∧
      (∀ i, ‖1 - Complex.exp ((alpha i : ℂ) * Complex.I)‖ ^ p.toReal +
        ‖1 - Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I)‖ ^ p.toReal =
          phaseMinimum p.toReal ((alpha i + beta i) / 2)) := by
  classical
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
  have hG : G.toLinearMap.IsSymmetric :=
    (isSelfAdjoint_schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)).isSymmetric
  have hinv : ∀ x ∈ H, G.toLinearMap x ∈ H := by
    intro x hx
    exact (Module.End.map_pointSpectralSubspace_le (A := G.toLinearMap) (Ω := Ioi 0))
      (Submodule.mem_map_of_mem hx)
  let T := G.toLinearMap.restrict hinv
  have hT : T.IsSymmetric := hG.restrict_invariant hinv
  let A (mu : Module.End.Eigenvalues T) := Module.End.eigenspace T mu.val
  let L (mu : Module.End.Eigenvalues T) := Module.End.eigenspace G.toLinearMap (mu.val.re : ℂ)
  have hlevel (mu : Module.End.Eigenvalues T) :
      0 < mu.val.re ∧
      ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ (L mu))) ℂ (A mu))
        (alpha beta : Fin (Module.finrank ℂ (L mu)) → ℝ),
        (∀ i, (U : E →L[ℂ] E) ((b i : H) : E) =
          Complex.exp ((alpha i : ℂ) * Complex.I) • ((b i : H) : E)) ∧
        (∀ i, (U : E →L[ℂ] E) (K.reflection (b i : H)) =
          Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (b i : H)) ∧
        (∀ i, (alpha i + beta i) / 2 ∈ Ioo 0 (Real.pi / 2)) ∧
        (∀ i, ‖1 - Complex.exp ((alpha i : ℂ) * Complex.I)‖ ^ p.toReal +
          ‖1 - Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I)‖ ^ p.toReal =
            phaseMinimum p.toReal ((alpha i + beta i) / 2)) := by
    have hreal : (mu.val.re : ℂ) = mu.val :=
      RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self mu.property)
    obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector
      (show Module.End.HasEigenvalue T mu.val from mu.property)
    have hx0 : (x : E) ≠ 0 := fun h => hx.2 (Subtype.ext h)
    have hxG : G.toLinearMap (x : E) = (mu.val.re : ℂ) • (x : E) := by
      have h := congrArg (fun y : H => (y : E)) hx.apply_eq_smul
      change G.toLinearMap (x : E) = mu.val • (x : E) at h
      rwa [← hreal] at h
    have hpos : 0 < mu.val.re :=
      (Module.End.pointSpectrumIn_iff_restrictedPointSpectrum_subset.mp
        (Module.End.pointSpectrumIn_pointSpectralSubspace G.toLinearMap (Ioi 0)))
        (Module.End.mem_restrictedPointSpectrum x.property hx0 hxG)
    have hspec : (mu.val.re : ℂ) ∈ spectrum ℂ G := by
      rw [ContinuousLinearMap.spectrum_eq]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp
        (Module.End.hasEigenvalue_of_hasEigenvector
          ⟨Module.End.mem_eigenspace_iff.mpr hxG, hx0⟩)
    have hLH : L mu ≤ H := Module.End.eigenspace_le_pointSpectralSubspace hpos
    let d : L mu ≃ₗᵢ[ℂ] A mu :=
      { toLinearEquiv :=
          { toFun := fun y => ⟨⟨y, hLH y.property⟩, by
              apply Module.End.mem_eigenspace_iff.mpr
              apply Subtype.ext
              change G.toLinearMap (y : E) = mu.val • (y : E)
              rw [← hreal]
              exact Module.End.mem_eigenspace_iff.mp y.property⟩
            invFun := fun y => ⟨((y : H) : E), by
              apply Module.End.mem_eigenspace_iff.mpr
              have h := congrArg (fun z : H => (z : E))
                (Module.End.mem_eigenspace_iff.mp y.property)
              change G.toLinearMap ((y : H) : E) = mu.val • ((y : H) : E) at h
              rwa [← hreal] at h⟩
            left_inv := by intro y; rfl
            right_inv := by intro y; rfl
            map_add' := by intro y z; rfl
            map_smul' := by intro c y; rfl }
        norm_map' := by intro y; rfl }
    obtain ⟨b, alpha, beta, hu, hw, hmean, hcost⟩ :=
      gradient_eigenspace_phase_basis_of_isLocalMinOn_transports p hp hp1 hp2
        K Q U htrans hmin mu.val.re hpos hspec
    refine ⟨hpos, b.map d, alpha, beta, ?_, ?_, hmean, hcost⟩
    · intro i
      change (U : E →L[ℂ] E) (b i : E) = _
      exact hu i
    · intro i
      change (U : E →L[ℂ] E) (K.reflection (b i)) = _
      exact hw i
  choose hpos b alpha beta hu hw hmean hcost using hlevel
  let I := (mu : Module.End.Eigenvalues T) × Fin (Module.finrank ℂ (L mu))
  let bp : OrthonormalBasis I ℂ H :=
    hT.direct_sum_isInternal.collectedOrthonormalBasis hT.orthogonalFamily_eigenspaces' b
  have hbp (i : I) : bp i = (b i.1 i.2 : H) := by
    have h := congrFun (hT.direct_sum_isInternal.collectedBasis_coe
      (fun mu => (b mu).toBasis)) i
    simpa only [bp, DirectSum.IsInternal.collectedOrthonormalBasis,
      Module.Basis.coe_toOrthonormalBasis, OrthonormalBasis.coe_toBasis] using h
  let q := Fintype.equivFin I
  let e := bp.reindex q
  let g (i : Fin (Fintype.card I)) := (q.symm i).1.val.re
  let alpha' (i : Fin (Fintype.card I)) := alpha (q.symm i).1 (q.symm i).2
  let beta' (i : Fin (Fintype.card I)) := beta (q.symm i).1 (q.symm i).2
  have he (i) : e i = (b (q.symm i).1 (q.symm i).2 : H) := by
    rw [OrthonormalBasis.reindex_apply]
    exact hbp _
  refine ⟨Fintype.card I, e, g, alpha', beta', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hpos _
  · intro i
    rw [he]
    have h := congrArg (fun y : H => (y : E))
      (Module.End.mem_eigenspace_iff.mp (b (q.symm i).1 (q.symm i).2).property)
    have hr : ((q.symm i).1.val.re : ℂ) = (q.symm i).1.val := RCLike.conj_eq_iff_re.mp
      (hT.conj_eigenvalue_eq_self (q.symm i).1.property)
    change G ((b (q.symm i).1 (q.symm i).2 : H) : E) =
      (q.symm i).1.val • ((b (q.symm i).1 (q.symm i).2 : H) : E) at h
    change G ((b (q.symm i).1 (q.symm i).2 : H) : E) = _
    rw [← hr] at h
    exact h
  · intro i
    rw [he]
    exact hu _ _
  · intro i
    rw [he]
    exact hw _ _
  · intro i
    exact hmean _ _
  · intro i
    exact hcost _ _

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
