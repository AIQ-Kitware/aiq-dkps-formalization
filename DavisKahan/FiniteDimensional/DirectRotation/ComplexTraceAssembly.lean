/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceOptimality
import ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
import ForTauCeti.Analysis.InnerProductSpace.OrthogonalGluing
import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockTrace
import ForTauCeti.Analysis.InnerProductSpace.AngleGeometryBlockSum

/-!
# Ambient extensions of the complex planar trace minimizer

The planar construction has a rank-one displacement. Its singular-value data
survive isometric zero-extension to any finite-dimensional complex Hilbert
space. In particular, its *full ambient trace norm* is still `2 sin theta`.
The projector difference, zero-extended along the same isometry, has the same
full trace norm. These equalities are the trace bookkeeping needed when the
nontrivial principal planes are glued orthogonally.

We also record that equal-dimensional complex subspaces always admit a
transporting unitary, without any acuteness hypothesis. This existence alone
does not yet assert trace optimality: that requires a coordinated choice of
the plane-wise transports and an orthogonal block trace-additivity theorem.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace ComplexTraceOptimality

open scoped InnerProductSpace
open Module (finrank)

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

/-- Zero-extend a planar operator along a complex linear isometric embedding.
The ambient operator is zero on the orthogonal complement of the embedded plane. -/
def planarZeroExtension (ι : E2 →ₗᵢ[ℂ] H) (T : E2 →ₗ[ℂ] E2) :
    H →ₗ[ℂ] H :=
  ι.toLinearMap ∘ₗ T ∘ₗ LinearMap.adjoint ι.toLinearMap

/-- Zero-extension preserves the complete, zero-padded singular-value sequence.
This is a composition of the two existing rectangular isometry lemmas. -/
theorem singularValues_planarZeroExtension
    (ι : E2 →ₗᵢ[ℂ] H) (T : E2 →ₗ[ℂ] E2) :
    (planarZeroExtension ι T).singularValues = T.singularValues := by
  unfold planarZeroExtension
  calc
    (ι.toLinearMap ∘ₗ T ∘ₗ LinearMap.adjoint ι.toLinearMap).singularValues =
        (T ∘ₗ LinearMap.adjoint ι.toLinearMap).singularValues :=
      singularValues_linearIsometry_comp ι _
    _ = T.singularValues := singularValues_comp_adjoint_linearIsometry ι T

/-- Every Ky Fan prefix of a zero-extended plane equals the corresponding
prefix in the original plane, including prefixes beyond dimension two. -/
theorem kyFanSum_planarZeroExtension
    (ι : E2 →ₗᵢ[ℂ] H) (T : E2 →ₗ[ℂ] E2) (k : ℕ) :
    kyFanSum k (planarZeroExtension ι T) = kyFanSum k T := by
  simp only [kyFanSum_eq_sum_fin, singularValues_planarZeroExtension]

/-- The range of a zero-extended planar map has complex dimension at most two. -/
theorem finrank_range_planarZeroExtension_le_two
    (ι : E2 →ₗᵢ[ℂ] H) (T : E2 →ₗ[ℂ] E2) :
    finrank ℂ (LinearMap.range (planarZeroExtension ι T)) ≤ 2 := by
  have hsub : LinearMap.range (planarZeroExtension ι T) ≤
      LinearMap.range ι.toLinearMap := by
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨T (LinearMap.adjoint ι.toLinearMap x), rfl⟩
  calc
    finrank ℂ (LinearMap.range (planarZeroExtension ι T)) ≤
        finrank ℂ (LinearMap.range ι.toLinearMap) := Submodule.finrank_mono hsub
    _ ≤ finrank ℂ E2 := LinearMap.finrank_range_le _
    _ = 2 := finrank_euclideanSpace_fin

/-- A rank-at-most-two operator has no trace-norm contribution after its
first two singular values. -/
private theorem kyFanSum_finrank_eq_two_of_rank_le
    (A : H →ₗ[ℂ] H) (h : finrank ℂ (LinearMap.range A) ≤ 2) :
    kyFanSum (finrank ℂ H) A = kyFanSum 2 A := by
  rw [kyFanSum_eq_linearMap_kyFanSum, kyFanSum_eq_linearMap_kyFanSum]
  calc
    A.kyFanSum (finrank ℂ H) =
        A.kyFanSum (min (finrank ℂ H) (finrank ℂ (LinearMap.range A))) :=
      (LinearMap.kyFanSum_min_finrank_range A _).symm
    _ = A.kyFanSum (min 2 (finrank ℂ (LinearMap.range A))) := by
      rw [min_eq_right (LinearMap.finrank_range_le A), min_eq_right h]
    _ = A.kyFanSum 2 := LinearMap.kyFanSum_min_finrank_range A _

/-- The *full ambient trace norm* of an embedded planar operator equals its
original trace norm, regardless of the dimension of the ambient space. -/
theorem trace_planarZeroExtension
    (ι : E2 →ₗᵢ[ℂ] H) (T : E2 →ₗ[ℂ] E2) :
    kyFanSum (finrank ℂ H) (planarZeroExtension ι T) = kyFanSum 2 T := by
  calc
    kyFanSum (finrank ℂ H) (planarZeroExtension ι T) =
        kyFanSum 2 (planarZeroExtension ι T) :=
      kyFanSum_finrank_eq_two_of_rank_le _
        (finrank_range_planarZeroExtension_le_two ι T)
    _ = kyFanSum 2 T := kyFanSum_planarZeroExtension ι T 2

/-- A phase-corrected complex principal plane, embedded into an arbitrarily
large ambient complex Hilbert space, contributes exactly `2 sin theta` to the
ambient trace displacement. -/
theorem trace_planarPhaseDisplacement
    (ι : E2 →ₗᵢ[ℂ] H) (theta : ℝ)
    (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    kyFanSum (finrank ℂ H)
      (planarZeroExtension ι (LinearMap.id - (phaseUnitary theta).toLinearMap)) =
        2 * Real.sin theta := by
  rw [trace_planarZeroExtension]
  exact kyFanSum_phaseUnitary theta h0 hpi

/-- The embedded difference of the two principal-plane projections has the
same full ambient trace norm as the embedded phase displacement. -/
theorem trace_planarProjectionDifference
    (ι : E2 →ₗᵢ[ℂ] H) (theta : ℝ)
    (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    kyFanSum (finrank ℂ H)
      (planarZeroExtension ι (projection sourceLine - projection (targetLine theta))) =
        2 * Real.sin theta := by
  rw [trace_planarZeroExtension]
  exact kyFanSum_projectionDifference theta h0 hpi

/-- The two zero-extended planar operators have identical trace norms. -/
theorem trace_planarPhase_eq_projectionDifference
    (ι : E2 →ₗᵢ[ℂ] H) (theta : ℝ)
    (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    kyFanSum (finrank ℂ H)
        (planarZeroExtension ι (LinearMap.id - (phaseUnitary theta).toLinearMap)) =
      kyFanSum (finrank ℂ H)
        (planarZeroExtension ι (projection sourceLine - projection (targetLine theta))) := by
  rw [trace_planarPhaseDisplacement ι theta h0 hpi,
    trace_planarProjectionDifference ι theta h0 hpi]

/-- Equal-dimensional complex subspaces admit an ambient transporting unitary,
including when their maximal principal angle is a right angle. The choice of
this unitary is not asserted to be trace minimizing. -/
theorem exists_complex_unitary_transporter_of_finrank_eq
    (U V : Submodule ℂ H) (hUV : finrank ℂ U = finrank ℂ V) :
    ∃ W : H ≃ₗᵢ[ℂ] H, U.map W.toLinearMap = V := by
  classical
  have hperp : finrank ℂ (Uᗮ : Submodule ℂ H) =
      finrank ℂ (Vᗮ : Submodule ℂ H) := by
    have hU := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℂ) (K := U)
    have hV := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℂ) (K := V)
    omega
  let f : U ≃ₗᵢ[ℂ] V :=
    (stdOrthonormalBasis ℂ U).repr.trans
      (((stdOrthonormalBasis ℂ V).reindex (finCongr hUV.symm)).repr).symm
  let g : Uᗮ ≃ₗᵢ[ℂ] Vᗮ :=
    (stdOrthonormalBasis ℂ (Uᗮ : Submodule ℂ H)).repr.trans
      (((stdOrthonormalBasis ℂ (Vᗮ : Submodule ℂ H)).reindex
        (finCongr hperp.symm)).repr).symm
  exact ⟨orthogonalGlue f g, map_orthogonalGlue f g⟩

end

/-! ## Exact trace equality under two orthogonal complex principal planes -/

/-- Direct sum of two phase-corrected complex planar unitaries. -/
noncomputable def twoPlanePhaseUnitary (theta phi : ℝ) :
    WithLp 2 (E2 × E2) ≃ₗᵢ[ℂ] WithLp 2 (E2 × E2) :=
  LinearIsometryEquiv.withLpProdCongr 2 (phaseUnitary theta) (phaseUnitary phi)

/-- Its displacement is the orthogonal block sum of the two planar
displacements. -/
theorem twoPlanePhaseUnitary_displacement (theta phi : ℝ) :
    (LinearMap.id : WithLp 2 (E2 × E2) →ₗ[ℂ] WithLp 2 (E2 × E2)) -
        (twoPlanePhaseUnitary theta phi).toLinearMap =
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (LinearMap.id - (phaseUnitary theta).toLinearMap)
        (LinearMap.id - (phaseUnitary phi).toLinearMap) := by
  have hid :
      UnitarilyInvariantSeminorm.orthogonalBlockSum
        (LinearMap.id : E2 →ₗ[ℂ] E2) (LinearMap.id : E2 →ₗ[ℂ] E2) =
        (LinearMap.id : WithLp 2 (E2 × E2) →ₗ[ℂ] WithLp 2 (E2 × E2)) := by
    ext x
    apply WithLp.ofLp_injective 2
    simp [UnitarilyInvariantSeminorm.orthogonalBlockSum_apply]
    rfl
  calc
    LinearMap.id - (twoPlanePhaseUnitary theta phi).toLinearMap =
        UnitarilyInvariantSeminorm.orthogonalBlockSum
          (LinearMap.id : E2 →ₗ[ℂ] E2) (LinearMap.id : E2 →ₗ[ℂ] E2) -
        UnitarilyInvariantSeminorm.orthogonalBlockSum
          (phaseUnitary theta).toLinearMap (phaseUnitary phi).toLinearMap := by
      rw [hid, UnitarilyInvariantSeminorm.orthogonalBlockSum_linearIsometryEquiv]
      rfl
    _ = _ := (UnitarilyInvariantSeminorm.orthogonalBlockSum_sub _ _ _ _).symm

/-- The *full four-dimensional trace* of two independently phase-minimized
principal planes is exactly the trace norm of the corresponding block sum of
projection differences, with no acuteness assumption. -/
theorem twoPlanePhaseUnitary_trace_eq_projectionDifference
    (theta phi : ℝ)
    (h0theta : 0 ≤ theta) (hpiTheta : theta ≤ Real.pi / 2)
    (h0phi : 0 ≤ phi) (hpiPhi : phi ≤ Real.pi / 2) :
    kyFanSum (finrank ℂ (WithLp 2 (E2 × E2)))
        (LinearMap.id - (twoPlanePhaseUnitary theta phi).toLinearMap) =
      kyFanSum (finrank ℂ (WithLp 2 (E2 × E2)))
        (UnitarilyInvariantSeminorm.orthogonalBlockSum
          (projection sourceLine - projection (targetLine theta))
          (projection sourceLine - projection (targetLine phi))) := by
  rw [twoPlanePhaseUnitary_displacement,
    kyFanSum_orthogonalBlockSum_full, kyFanSum_orthogonalBlockSum_full]
  have hdim : finrank ℂ E2 = 2 := finrank_euclideanSpace_fin
  rw [hdim]
  exact congrArg₂ (· + ·)
    (phaseUnitary_global_trace_minimizer theta h0theta hpiTheta).2
    (phaseUnitary_global_trace_minimizer phi h0phi hpiPhi).2


/-- The source lines in an orthogonal sum of two complex principal planes. -/
noncomputable def twoPlaneSource : Submodule ℂ (WithLp 2 (E2 × E2)) :=
  UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule sourceLine sourceLine

/-- The two independently rotated target lines. -/
noncomputable def twoPlaneTarget (theta phi : ℝ) :
    Submodule ℂ (WithLp 2 (E2 × E2)) :=
  UnitarilyInvariantSeminorm.orthogonalBlockSumSubmodule
    (targetLine theta) (targetLine phi)

/-- The direct sum of the two phase minimizers carries the direct sum of the
source lines to the direct sum of their targets. -/
theorem twoPlanePhaseUnitary_transports (theta phi : ℝ) :
    twoPlaneSource.map (twoPlanePhaseUnitary theta phi).toLinearMap =
      twoPlaneTarget theta phi := by
  exact TauCeti.map_orthogonalBlockSumSubmodule
    sourceLine sourceLine (targetLine theta) (targetLine phi)
    (phaseUnitary theta) (phaseUnitary phi)
    (phaseUnitary_transports theta) (phaseUnitary_transports phi)

/-- The two-plane phase unitary attains the trace-distance lower bound, so it
is a global trace-norm minimizer among *all* unitaries transporting these
block-sum subspaces. Both angles may equal `π / 2`. -/
theorem twoPlanePhaseUnitary_global_trace_minimizer
    (theta phi : ℝ)
    (h0theta : 0 ≤ theta) (hpiTheta : theta ≤ Real.pi / 2)
    (h0phi : 0 ≤ phi) (hpiPhi : phi ≤ Real.pi / 2) :
    (∀ W : WithLp 2 (E2 × E2) ≃ₗᵢ[ℂ] WithLp 2 (E2 × E2),
      twoPlaneSource.map W.toLinearMap = twoPlaneTarget theta phi →
      kyFanSum (finrank ℂ (WithLp 2 (E2 × E2)))
        (LinearMap.id - (twoPlanePhaseUnitary theta phi).toLinearMap) ≤
      kyFanSum (finrank ℂ (WithLp 2 (E2 × E2)))
        (LinearMap.id - W.toLinearMap)) ∧
    kyFanSum (finrank ℂ (WithLp 2 (E2 × E2)))
        (LinearMap.id - (twoPlanePhaseUnitary theta phi).toLinearMap) =
      kyFanSum (finrank ℂ (WithLp 2 (E2 × E2)))
        (projection twoPlaneSource - projection (twoPlaneTarget theta phi)) := by
  have hproj :
      projection twoPlaneSource - projection (twoPlaneTarget theta phi) =
        UnitarilyInvariantSeminorm.orthogonalBlockSum
          (projection sourceLine - projection (targetLine theta))
          (projection sourceLine - projection (targetLine phi)) := by
    rw [twoPlaneSource, twoPlaneTarget,
      projection_orthogonalBlockSumSubmodule,
      projection_orthogonalBlockSumSubmodule,
      ← UnitarilyInvariantSeminorm.orthogonalBlockSum_sub]
  have heq := twoPlanePhaseUnitary_trace_eq_projectionDifference
    theta phi h0theta hpiTheta h0phi hpiPhi
  rw [← hproj] at heq
  constructor
  · intro W hmap
    calc
      kyFanSum (finrank ℂ (WithLp 2 (E2 × E2)))
          (LinearMap.id - (twoPlanePhaseUnitary theta phi).toLinearMap) =
          kyFanSum (finrank ℂ (WithLp 2 (E2 × E2)))
            (projection twoPlaneSource - projection (twoPlaneTarget theta phi)) := heq
      _ ≤ kyFanSum (finrank ℂ (WithLp 2 (E2 × E2)))
            (LinearMap.id - W.toLinearMap) :=
        projectionDifference_kyFanSum_le_displacement
          twoPlaneSource (twoPlaneTarget theta phi) W hmap _
  · exact heq

end ComplexTraceOptimality
end DavisKahan.FiniteDimensional
end TauCeti
