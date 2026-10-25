/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenGlobalLowerBound
import ForTauCeti.Analysis.InnerProductSpace.Projection.ReflectionTransport

/-!
# Every Schatten optimizer preserves the principal-sine spaces

The actual paired-gradient basis consists of common eigenvectors of the
transporter and sine angle operator. On the exceptional kernel, reflection
transport and invariance of the two projections give the same commutation.
Completeness of the actual decomposition then proves that every local,
hence every global, minimizer preserves each geometric angle space.
Unequal principal angles cannot mix. The phase choices within each
equal-angle space remain to be classified.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
private theorem commute_apply_of_common_eigenvector (A B : E →L[ℂ] E)
    (x : E) (a b : ℂ) (hA : A x = a • x) (hB : B x = b • x) :
    A (B x) = B (A x) := by
  simp only [hA, hB, map_smul, smul_smul, mul_comm]

/-- Every unrestricted finite complex Schatten transport local minimum
commutes with the intrinsic sine angle operator. Consequently unequal
principal-angle spaces cannot mix, including zero and right-angle sectors.
No angle multiplicity or spectral endpoint is excluded. -/
theorem commute_sinAngleOperator_of_isLocalMinOn_transports_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) :
    Commute (U : E →L[ℂ] E) (K.sinAngleOperator L) := by
  let G := schattenUnitaryGradient p.toReal (U : E →L[ℂ] E)
  let H := Module.End.pointSpectralSubspace G.toLinearMap (Ioi 0)
  let Z := G.toLinearMap.ker
  let S := K.sinAngleOperator L
  let S₀ := (K.comap Z.subtype).sinAngleOperator (L.comap Z.subtype)
  have ht := (map_eq_iff_conjugate_starProjection_complex K L U).mp hmap
  obtain ⟨n, e, alpha, beta, V, W, R, d, hV, hW, hR, hself, hd, _, hVe, hWe,
      hmean, _, _⟩ := schatten_transport_spectral_decomposition_of_isLocalMinOn_complex
        p hp hp1 hp2 K L.starProjection U ht hmin
  have hG : IsSelfAdjoint G := isSelfAdjoint_schattenUnitaryGradient _ _
  obtain ⟨hPK, hPL⟩ := gradient_square_reduces_projections_of_isLocalMinOn_transports
    p hp hp1 K L.starProjection U ht hmin
  have hK : ∀ x ∈ Z, K.starProjection x ∈ Z :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute K.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPK.eq)
  have hL : ∀ x ∈ Z, L.starProjection x ∈ Z :=
    hG.isSymmetric.mapsTo_ker_of_commute_square
      (show Commute L.starProjection.toLinearMap (G.toLinearMap * G.toLinearMap) from
        congrArg ContinuousLinearMap.toLinearMap hPL.eq)
  obtain ⟨R', hR', _, hmapR', _⟩ := gradient_kernel_principalAngle_lower_bound p hp K L U hmap
  have heq : R' = R := by
    ext z
    exact (hR' z).trans (hR z).symm
  rw [heq] at hmapR'
  let Runit := Unitary.linearIsometryEquiv.symm R
  have hmapR : (K.comap Z.subtype).map
      (Unitary.linearIsometryEquiv Runit).toLinearMap = L.comap Z.subtype := by
    simpa only [Runit, MulEquiv.apply_symm_apply] using hmapR'
  have htransR := (map_eq_iff_conjugate_starProjection_complex
    (K.comap Z.subtype) (L.comap Z.subtype) Runit).mp hmapR
  have hcommR := Submodule.commute_sinAngleOperator_of_selfAdjoint_transport
    (K.comap Z.subtype) (L.comap Z.subtype) R hself htransR
  have hrestrict (z : Z) : (S₀ z : E) = S (z : E) :=
    Submodule.sinAngleOperator_comap_subtype_apply_of_invariant K L Z hK hL z
  have hkernel (z : Z) :
      (U : E →L[ℂ] E) (S (z : E)) = S ((U : E →L[ℂ] E) z) := by
    calc
      _ = (U : E →L[ℂ] E) (S₀ z : E) := congrArg (U : E →L[ℂ] E) (hrestrict z).symm
      _ = (R (S₀ z) : E) := (hR (S₀ z)).symm
      _ = (S₀ (R z) : E) := congrArg (fun y : Z => (y : E))
        (congrArg (fun T : Z →L[ℂ] Z => T z) hcommR.eq)
      _ = S (R z : E) := hrestrict (R z)
      _ = S ((U : E →L[ℂ] E) z) := congrArg S (hR z)
  have hu (i) : (U : E →L[ℂ] E) (e i : E) =
      Complex.exp ((alpha i : ℂ) * Complex.I) • (e i : E) := by
    rw [← hV, hVe]
    rfl
  have hw (i) : (U : E →L[ℂ] E) (K.reflection (e i)) =
      Complex.exp (((-beta i : ℝ) : ℂ) * Complex.I) • K.reflection (e i) := by
    rw [← hW, hWe, Submodule.coe_smul, map_smul]
  have hs (i) := Submodule.sinAngleOperator_apply_of_paired_phase_eigenvectors_complex
    K L (Unitary.linearIsometryEquiv U) hmap (e i) (alpha i) (beta i) (hu i) (hw i)
    ⟨(hmean i).1.le, (hmean i).2.le⟩
  have hH : (U : E →L[ℂ] E).toLinearMap ∘ₗ S.toLinearMap ∘ₗ H.subtype =
      S.toLinearMap ∘ₗ (U : E →L[ℂ] E).toLinearMap ∘ₗ H.subtype := by
    apply e.toBasis.ext
    intro i
    exact commute_apply_of_common_eigenvector (U : E →L[ℂ] E) S (e i) _ _ (hu i) (hs i).1
  have hJH : (U : E →L[ℂ] E).toLinearMap ∘ₗ S.toLinearMap ∘ₗ
      K.reflection.toLinearMap ∘ₗ H.subtype =
      S.toLinearMap ∘ₗ (U : E →L[ℂ] E).toLinearMap ∘ₗ
        K.reflection.toLinearMap ∘ₗ H.subtype := by
    apply e.toBasis.ext
    intro i
    exact commute_apply_of_common_eigenvector (U : E →L[ℂ] E) S
      (K.reflection (e i)) _ _ (hw i) (hs i).2
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := d.surjective x
  change (U : E →L[ℂ] E) (S (d y)) = S ((U : E →L[ℂ] E) (d y))
  rw [hd]
  simp only [map_add]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) (LinearMap.congr_fun hH y.fst.fst)
      (LinearMap.congr_fun hJH y.fst.snd)) (hkernel y.snd)

/-- Every local minimizing transporter maps each sine-angle eigenvector
back into the same geometric angle space, with arbitrary multiplicity. -/
theorem sinAngleOperator_apply_transport_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E))
    (s : ℂ) (x : E) (hx : K.sinAngleOperator L x = s • x) :
    K.sinAngleOperator L ((U : E →L[ℂ] E) x) = s • (U : E →L[ℂ] E) x := by
  have hcomm := commute_sinAngleOperator_of_isLocalMinOn_transports_complex
    p hp hp1 hp2 K L U hmap hmin
  calc
    _ = (U : E →L[ℂ] E) (K.sinAngleOperator L x) :=
      (congrArg (fun T : E →L[ℂ] E => T x) hcomm.eq).symm
    _ = _ := by rw [hx, map_smul]

/-- Every intrinsic sine-angle eigenspace is mapped onto itself by a
local minimizing transporter, including empty eigenspaces. -/
theorem map_sinAngleOperator_eigenspace_of_isLocalMinOn_complex
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) (U : unitary (E →L[ℂ] E))
    (hmap : K.map (Unitary.linearIsometryEquiv U).toLinearMap = L)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => UnitarilyInvariantSeminorm.schatten ℂ E E p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = L.starProjection}
      (U : E →L[ℂ] E)) (s : ℂ) :
    (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s).map
      (Unitary.linearIsometryEquiv U).toLinearMap =
        Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro y ⟨x, hx, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    exact sinAngleOperator_apply_transport_of_isLocalMinOn_complex
      p hp hp1 hp2 K L U hmap hmin s x (Module.End.mem_eigenspace_iff.mp hx)
  · exact (Unitary.linearIsometryEquiv U).toLinearEquiv.finrank_map_eq _

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
