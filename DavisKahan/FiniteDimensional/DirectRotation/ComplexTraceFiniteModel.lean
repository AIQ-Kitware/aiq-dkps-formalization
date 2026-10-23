/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceAssembly

/-!
# Exact complex trace minimizers on arbitrarily many principal planes

The two-plane construction extends to *every finite number* of orthogonal
complex principal planes.  The induction uses only the full-trace block-sum
identity and the projection-displacement lower bound.  In particular, it
includes zero angles and right angles; there is no `IsAcute` assumption.

This is the finite-model half of arbitrary-dimensional complex trace
optimality. Identifying an arbitrary subspace pair with this model additionally
requires the finite CS/Halmos decomposition, including common and exterior
summands. Those identifications are not hypotheses or conclusions here.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace ComplexTraceOptimality

open scoped InnerProductSpace BigOperators
open Module (finrank)
open UnitarilyInvariantSeminorm

noncomputable section

/-- A unitary transporting two complex subspaces attains the projection lower
bound for the full trace norm.  Once this equality holds, global minimality
follows from `projectionDifference_kyFanSum_le_displacement`. -/
def AttainsProjectionTraceBound {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (U V : Submodule ℂ H) (W : H ≃ₗᵢ[ℂ] H) : Prop :=
  U.map W.toLinearMap = V ∧
    kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) =
      kyFanSum (finrank ℂ H) (projection U - projection V)

/-- Any attainer realizes an actual global minimum among all admissible unitaries. -/
theorem AttainsProjectionTraceBound.le_competitor
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    {U V : Submodule ℂ H} {W : H ≃ₗᵢ[ℂ] H}
    (h : AttainsProjectionTraceBound U V W)
    (Z : H ≃ₗᵢ[ℂ] H) (hZ : U.map Z.toLinearMap = V) :
    kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) ≤
      kyFanSum (finrank ℂ H) (LinearMap.id - Z.toLinearMap) := by
  rw [h.2]
  exact projectionDifference_kyFanSum_le_displacement U V Z hZ _

/-- Exact trace optimality survives an orthogonal sum of two *arbitrary*
complex pairs.  This is the inductive form of the verified two-plane theorem. -/
theorem attainsProjectionTraceBound_orthogonalBlockSum
    {H₁ H₂ : Type*}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [FiniteDimensional ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [FiniteDimensional ℂ H₂]
    (U₁ V₁ : Submodule ℂ H₁) (U₂ V₂ : Submodule ℂ H₂)
    (W₁ : H₁ ≃ₗᵢ[ℂ] H₁) (W₂ : H₂ ≃ₗᵢ[ℂ] H₂)
    (h₁ : AttainsProjectionTraceBound U₁ V₁ W₁)
    (h₂ : AttainsProjectionTraceBound U₂ V₂ W₂) :
    AttainsProjectionTraceBound
      (orthogonalBlockSumSubmodule U₁ U₂)
      (orthogonalBlockSumSubmodule V₁ V₂)
      (LinearIsometryEquiv.withLpProdCongr 2 W₁ W₂) := by
  have hid :
      orthogonalBlockSum
          (LinearMap.id : H₁ →ₗ[ℂ] H₁) (LinearMap.id : H₂ →ₗ[ℂ] H₂) =
        (LinearMap.id : WithLp 2 (H₁ × H₂) →ₗ[ℂ] WithLp 2 (H₁ × H₂)) := by
    ext x
    apply WithLp.ofLp_injective 2
    simp only [orthogonalBlockSum_apply, LinearMap.id_apply]
    rfl
  have hdisp :
      (LinearMap.id : WithLp 2 (H₁ × H₂) →ₗ[ℂ] WithLp 2 (H₁ × H₂)) -
          (LinearIsometryEquiv.withLpProdCongr 2 W₁ W₂).toLinearMap =
        orthogonalBlockSum (LinearMap.id - W₁.toLinearMap)
          (LinearMap.id - W₂.toLinearMap) := by
    rw [← hid, ← orthogonalBlockSum_linearIsometryEquiv]
    exact (orthogonalBlockSum_sub _ _ _ _).symm
  have hproj :
      projection (orthogonalBlockSumSubmodule U₁ U₂) -
          projection (orthogonalBlockSumSubmodule V₁ V₂) =
        orthogonalBlockSum (projection U₁ - projection V₁)
          (projection U₂ - projection V₂) := by
    rw [projection_orthogonalBlockSumSubmodule U₁ U₂,
      projection_orthogonalBlockSumSubmodule V₁ V₂,
      ← orthogonalBlockSum_sub]
  constructor
  · exact TauCeti.map_orthogonalBlockSumSubmodule
      U₁ U₂ V₁ V₂ W₁ W₂ h₁.1 h₂.1
  · rw [hdisp, hproj, kyFanSum_orthogonalBlockSum_full,
      kyFanSum_orthogonalBlockSum_full, h₁.2, h₂.2]

/-- Composition of submodule images, stated using the local bundled linear-map
representation.  This also avoids relying on a version-dependent simp name. -/
private theorem submodule_map_linear_comp
    {H K L : Type*}
    [AddCommGroup H] [Module ℂ H]
    [AddCommGroup K] [Module ℂ K]
    [AddCommGroup L] [Module ℂ L]
    (U : Submodule ℂ H) (A : H →ₗ[ℂ] K) (B : K →ₗ[ℂ] L) :
    (U.map A).map B = U.map (B ∘ₗ A) := by
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨A x, ⟨x, hx, rfl⟩, rfl⟩

/-! ## Transporting exact trace optimality along an ambient unitary -/

/-- Full (or partial) Ky Fan sums are unchanged by an ambient isometric
conjugation. This is the two-sided singular-value invariance already provided
by the linear-map API. -/
private theorem kyFanSum_conjugate
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (F : H ≃ₗᵢ[ℂ] K) (A : H →ₗ[ℂ] H) (k : ℕ) :
    kyFanSum k (F.toLinearMap ∘ₗ A ∘ₗ F.symm.toLinearMap) = kyFanSum k A := by
  rw [kyFanSum_eq_linearMap_kyFanSum, kyFanSum_eq_linearMap_kyFanSum]
  calc
    (F.toLinearMap ∘ₗ A ∘ₗ F.symm.toLinearMap).kyFanSum k =
        (A ∘ₗ F.symm.toLinearMap).kyFanSum k :=
      LinearMap.kyFanSum_linearIsometryEquiv_comp F _ k
    _ = A.kyFanSum k :=
      LinearMap.kyFanSum_comp_linearIsometryEquiv A F.symm k

/-- An orthogonal projector conjugates with an isometry transporting its range. -/
private theorem projection_map_conjugate
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (F : H ≃ₗᵢ[ℂ] K) (U : Submodule ℂ H) :
    projection (U.map F.toLinearMap) =
      F.toLinearMap ∘ₗ projection U ∘ₗ F.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  change (U.map F.toLinearMap).starProjection x =
    F (U.starProjection (F.symm x))
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (K := U.map F.toLinearMap) ?_ ?_
  · exact ⟨U.starProjection (F.symm x), U.starProjection_apply_mem _, rfl⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    change ⟪x - F (U.starProjection (F.symm x)), F z⟫_ℂ = 0
    have horth :
        ⟪F.symm x - U.starProjection (F.symm x), z⟫_ℂ = 0 := by
      exact inner_eq_zero_symm.mpr
        (Submodule.inner_right_of_mem_orthogonal hz
          (U.sub_starProjection_mem_orthogonal (F.symm x)))
    calc
      ⟪x - F (U.starProjection (F.symm x)), F z⟫_ℂ =
          ⟪F (F.symm x - U.starProjection (F.symm x)), F z⟫_ℂ := by
            rw [map_sub, F.apply_symm_apply]
      _ = ⟪F.symm x - U.starProjection (F.symm x), z⟫_ℂ := by
            rw [F.inner_map_map]
      _ = 0 := horth

/-- Any attained full-trace equality is invariant under an ambient unitary
change of coordinates. This turns a principal-plane model construction into a
construction on its actual ambient Hilbert space. -/
theorem AttainsProjectionTraceBound.conjugate
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    {U V : Submodule ℂ H} {T : H ≃ₗᵢ[ℂ] H}
    (h : AttainsProjectionTraceBound U V T) (F : H ≃ₗᵢ[ℂ] K) :
    AttainsProjectionTraceBound (U.map F.toLinearMap) (V.map F.toLinearMap)
      ((F.symm.trans T).trans F) := by
  let W : K ≃ₗᵢ[ℂ] K := (F.symm.trans T).trans F
  have hcomm : W.toLinearMap ∘ₗ F.toLinearMap =
      F.toLinearMap ∘ₗ T.toLinearMap := by
    ext x
    change F (T (F.symm (F x))) = F (T x)
    rw [F.symm_apply_apply]
  have hmap : (U.map F.toLinearMap).map W.toLinearMap =
      (V.map F.toLinearMap) := by
    calc
      (U.map F.toLinearMap).map W.toLinearMap =
          U.map (W.toLinearMap ∘ₗ F.toLinearMap) :=
        submodule_map_linear_comp U F.toLinearMap W.toLinearMap
      _ = U.map (F.toLinearMap ∘ₗ T.toLinearMap) := by rw [hcomm]
      _ = (U.map T.toLinearMap).map F.toLinearMap :=
        (submodule_map_linear_comp U T.toLinearMap F.toLinearMap).symm
      _ = V.map F.toLinearMap := by rw [h.1]
  have hdisp : (LinearMap.id : K →ₗ[ℂ] K) - W.toLinearMap =
      F.toLinearMap ∘ₗ (LinearMap.id - T.toLinearMap) ∘ₗ F.symm.toLinearMap := by
    ext x
    change x - F (T (F.symm x)) = F (F.symm x - T (F.symm x))
    rw [map_sub, F.apply_symm_apply]
  have hproj : projection (U.map F.toLinearMap) -
      projection (V.map F.toLinearMap) =
      F.toLinearMap ∘ₗ (projection U - projection V) ∘ₗ F.symm.toLinearMap := by
    rw [projection_map_conjugate F U, projection_map_conjugate F V]
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  have hdim : finrank ℂ K = finrank ℂ H :=
    F.toLinearEquiv.finrank_eq.symm
  constructor
  · exact hmap
  · rw [hdisp, hproj, kyFanSum_conjugate, kyFanSum_conjugate, hdim]
    exact h.2

/-- A common (or exterior) summand requires no displacement: the identity
unitary attains the trace bound for a pair of identical subspaces. -/
theorem AttainsProjectionTraceBound.refl
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (C : Submodule ℂ H) :
    AttainsProjectionTraceBound C C (LinearIsometryEquiv.refl ℂ H) := by
  constructor
  · change C.map (LinearMap.id : H →ₗ[ℂ] H) = C
    simp
  · change kyFanSum (finrank ℂ H) (LinearMap.id - LinearMap.id) =
        kyFanSum (finrank ℂ H) (projection C - projection C)
    simp

/-- Transport an attained full-trace equality from *any* unitary-equivalent
model pair.  This is the abstract bridge separating operator-norm computations
from the geometric CS decomposition. -/
theorem AttainsProjectionTraceBound.exists_minimizer_of_unitaryEquivalent
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    {U V : Submodule ℂ H} {T : H ≃ₗᵢ[ℂ] H}
    (h : AttainsProjectionTraceBound U V T)
    (F : H ≃ₗᵢ[ℂ] K)
    (U' V' : Submodule ℂ K)
    (hU : U.map F.toLinearMap = U')
    (hV : V.map F.toLinearMap = V') :
    ∃ W : K ≃ₗᵢ[ℂ] K,
      U'.map W.toLinearMap = V' ∧
      kyFanSum (finrank ℂ K) (LinearMap.id - W.toLinearMap) =
        kyFanSum (finrank ℂ K) (projection U' - projection V') ∧
      ∀ Z : K ≃ₗᵢ[ℂ] K, U'.map Z.toLinearMap = V' →
        kyFanSum (finrank ℂ K) (LinearMap.id - W.toLinearMap) ≤
          kyFanSum (finrank ℂ K) (LinearMap.id - Z.toLinearMap) := by
  let W : K ≃ₗᵢ[ℂ] K := (F.symm.trans T).trans F
  have hF := h.conjugate F
  have h' : AttainsProjectionTraceBound U' V' W := by
    simpa only [hU, hV] using hF
  exact ⟨W, h'.1, h'.2, fun Z hZ => h'.le_competitor Z hZ⟩

/-- Hilbert space of `n+1` orthogonal complex principal planes, represented
by nested `L²` sums.  The inductive representation avoids any choice of a
coordinate permutation or basis extension. -/
abbrev phasePlaneModel : ℕ → Type
  | 0 => E2
  | n + 1 => WithLp 2 (E2 × phasePlaneModel n)

-- Construct the class values before registering them as instances.  Otherwise
-- inference can recursively select the instance being defined, and the induced
-- additive/module structures need not reduce to the canonical `WithLp` ones.
@[instance_reducible]
noncomputable def phasePlaneModel_normedAddCommGroup :
    (n : ℕ) → NormedAddCommGroup (phasePlaneModel n)
  | 0 => inferInstanceAs (NormedAddCommGroup E2)
  | n + 1 => by
      letI : NormedAddCommGroup (phasePlaneModel n) :=
        phasePlaneModel_normedAddCommGroup n
      exact inferInstanceAs (NormedAddCommGroup (WithLp 2 (E2 × phasePlaneModel n)))

attribute [instance] phasePlaneModel_normedAddCommGroup

@[instance_reducible]
noncomputable def phasePlaneModel_innerProductSpace :
    (n : ℕ) → InnerProductSpace ℂ (phasePlaneModel n)
  | 0 => inferInstanceAs (InnerProductSpace ℂ E2)
  | n + 1 => by
      letI : InnerProductSpace ℂ (phasePlaneModel n) :=
        phasePlaneModel_innerProductSpace n
      exact inferInstanceAs (InnerProductSpace ℂ (WithLp 2 (E2 × phasePlaneModel n)))

attribute [instance] phasePlaneModel_innerProductSpace

/-- The canonical finite-dimensional instance for an orthogonal product, with
both component instances explicit at the recursive call site. -/
private theorem finiteDimensional_withLpProd
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K] :
    FiniteDimensional ℂ (WithLp 2 (H × K)) := inferInstance

theorem phasePlaneModel_finiteDimensional :
    (n : ℕ) → FiniteDimensional ℂ (phasePlaneModel n)
  | 0 => inferInstanceAs (FiniteDimensional ℂ E2)
  | n + 1 =>
      @finiteDimensional_withLpProd E2 (phasePlaneModel n)
        (inferInstanceAs (NormedAddCommGroup E2))
        (inferInstanceAs (InnerProductSpace ℂ E2))
        (inferInstanceAs (FiniteDimensional ℂ E2))
        (phasePlaneModel_normedAddCommGroup n)
        (phasePlaneModel_innerProductSpace n)
        (phasePlaneModel_finiteDimensional n)

attribute [instance] phasePlaneModel_finiteDimensional

/-- Direct sum of `n+1` complex source lines. -/
def phasePlaneModelSource : (n : ℕ) → Submodule ℂ (phasePlaneModel n)
  | 0 => sourceLine
  | n + 1 => orthogonalBlockSumSubmodule sourceLine (phasePlaneModelSource n)

/-- Direct sum of the prescribed target lines, indexed by their angles. -/
def phasePlaneModelTarget :
    (n : ℕ) → (Fin (n + 1) → ℝ) → Submodule ℂ (phasePlaneModel n)
  | 0, theta => targetLine (theta 0)
  | n + 1, theta =>
      orthogonalBlockSumSubmodule (targetLine (theta 0))
        (phasePlaneModelTarget n (fun i => theta i.succ))

/-- Componentwise phase-minimizing complex unitary on `n+1` planes. -/
def phasePlaneModelUnitary :
    (n : ℕ) → (Fin (n + 1) → ℝ) →
      (phasePlaneModel n ≃ₗᵢ[ℂ] phasePlaneModel n)
  | 0, theta => phaseUnitary (theta 0)
  | n + 1, theta =>
      LinearIsometryEquiv.withLpProdCongr 2 (phaseUnitary (theta 0))
        (phasePlaneModelUnitary n (fun i => theta i.succ))

/-- **Finite many complex planes, including right angles:** the product of
phase minimizers transports the source subspace and realizes the full trace
projection distance exactly. This is inductive over an arbitrary plane count. -/
theorem phasePlaneModel_attains (n : ℕ) (theta : Fin (n + 1) → ℝ)
    (hzero : ∀ i, 0 ≤ theta i)
    (hpi : ∀ i, theta i ≤ Real.pi / 2) :
    AttainsProjectionTraceBound
      (phasePlaneModelSource n) (phasePlaneModelTarget n theta)
      (phasePlaneModelUnitary n theta) := by
  induction n with
  | zero =>
      change sourceLine.map (phaseUnitary (theta 0)).toLinearMap =
          targetLine (theta 0) ∧
        kyFanSum (finrank ℂ E2)
            (LinearMap.id - (phaseUnitary (theta 0)).toLinearMap) =
          kyFanSum (finrank ℂ E2)
            (projection sourceLine - projection (targetLine (theta 0)))
      constructor
      · exact phaseUnitary_transports (theta 0)
      · have hdim : finrank ℂ E2 = 2 := finrank_euclideanSpace_fin
        rw [hdim]
        exact (phaseUnitary_global_trace_minimizer
          (theta 0) (hzero 0) (hpi 0)).2
  | succ n ih =>
      change AttainsProjectionTraceBound
        (orthogonalBlockSumSubmodule sourceLine (phasePlaneModelSource n))
        (orthogonalBlockSumSubmodule (targetLine (theta 0))
          (phasePlaneModelTarget n (fun i => theta i.succ)))
        (LinearIsometryEquiv.withLpProdCongr 2 (phaseUnitary (theta 0))
          (phasePlaneModelUnitary n (fun i => theta i.succ)))
      exact attainsProjectionTraceBound_orthogonalBlockSum
        sourceLine (targetLine (theta 0))
        (phasePlaneModelSource n) (phasePlaneModelTarget n (fun i => theta i.succ))
        (phaseUnitary (theta 0))
        (phasePlaneModelUnitary n (fun i => theta i.succ))
        ⟨phaseUnitary_transports (theta 0), by
          have hdim : finrank ℂ E2 = 2 := finrank_euclideanSpace_fin
          rw [hdim]
          exact (phaseUnitary_global_trace_minimizer
            (theta 0) (hzero 0) (hpi 0)).2⟩
        (ih (fun i => theta i.succ) (fun i => hzero i.succ) (fun i => hpi i.succ))

/-- The projector difference on `n+1` complex principal planes has full
trace norm `2 ∑ᵢ sin θᵢ`.  In particular, zero and right angles require no
exceptional branches. -/
theorem phasePlaneModel_projection_trace_formula (n : ℕ)
    (theta : Fin (n + 1) → ℝ)
    (hzero : ∀ i, 0 ≤ theta i)
    (hpi : ∀ i, theta i ≤ Real.pi / 2) :
    kyFanSum (finrank ℂ (phasePlaneModel n))
      (projection (phasePlaneModelSource n) -
        projection (phasePlaneModelTarget n theta)) =
      ∑ i : Fin (n + 1), 2 * Real.sin (theta i) := by
  induction n with
  | zero =>
      change kyFanSum (finrank ℂ E2)
          (projection sourceLine - projection (targetLine (theta 0))) =
        ∑ i : Fin 1, 2 * Real.sin (theta i)
      have hdim : finrank ℂ E2 = 2 := finrank_euclideanSpace_fin
      rw [hdim, kyFanSum_projectionDifference (theta 0) (hzero 0) (hpi 0)]
      simp
  | succ n ih =>
      have hproj :
          projection (phasePlaneModelSource (n + 1)) -
              projection (phasePlaneModelTarget (n + 1) theta) =
            orthogonalBlockSum
              (projection sourceLine - projection (targetLine (theta 0)))
              (projection (phasePlaneModelSource n) -
                projection (phasePlaneModelTarget n (fun i => theta i.succ))) := by
        change projection
              (orthogonalBlockSumSubmodule sourceLine (phasePlaneModelSource n)) -
            projection
              (orthogonalBlockSumSubmodule (targetLine (theta 0))
                (phasePlaneModelTarget n (fun i => theta i.succ))) = _
        rw [projection_orthogonalBlockSumSubmodule,
          projection_orthogonalBlockSumSubmodule, ← orthogonalBlockSum_sub]
      rw [hproj, kyFanSum_orthogonalBlockSum_full]
      have hdim : finrank ℂ E2 = 2 := finrank_euclideanSpace_fin
      rw [hdim, kyFanSum_projectionDifference (theta 0) (hzero 0) (hpi 0)]
      rw [ih (fun i => theta i.succ) (fun i => hzero i.succ)
        (fun i => hpi i.succ)]
      conv_rhs => rw [Fin.sum_univ_succ]

/-- The phase-minimizing unitary itself has exactly the same trace norm,
`2 ∑ᵢ sin θᵢ`, regardless of the number of principal planes. -/
theorem phasePlaneModel_displacement_trace_formula (n : ℕ)
    (theta : Fin (n + 1) → ℝ)
    (hzero : ∀ i, 0 ≤ theta i)
    (hpi : ∀ i, theta i ≤ Real.pi / 2) :
    kyFanSum (finrank ℂ (phasePlaneModel n))
      (LinearMap.id - (phasePlaneModelUnitary n theta).toLinearMap) =
      ∑ i : Fin (n + 1), 2 * Real.sin (theta i) := by
  exact (phasePlaneModel_attains n theta hzero hpi).2.trans
    (phasePlaneModel_projection_trace_formula n theta hzero hpi)

/-- For any number of prescribed (possibly zero or right) angles, an explicit
unitary attains the trace displacement minimum among every transporting
unitary on the complete orthogonal plane model. -/
theorem phasePlaneModel_global_trace_minimizer (n : ℕ) (theta : Fin (n + 1) → ℝ)
    (hzero : ∀ i, 0 ≤ theta i)
    (hpi : ∀ i, theta i ≤ Real.pi / 2) :
    ∃ W : phasePlaneModel n ≃ₗᵢ[ℂ] phasePlaneModel n,
      (phasePlaneModelSource n).map W.toLinearMap = phasePlaneModelTarget n theta ∧
      kyFanSum (finrank ℂ (phasePlaneModel n)) (LinearMap.id - W.toLinearMap) =
        kyFanSum (finrank ℂ (phasePlaneModel n))
          (projection (phasePlaneModelSource n) -
            projection (phasePlaneModelTarget n theta)) ∧
      ∀ Z : phasePlaneModel n ≃ₗᵢ[ℂ] phasePlaneModel n,
        (phasePlaneModelSource n).map Z.toLinearMap = phasePlaneModelTarget n theta →
        kyFanSum (finrank ℂ (phasePlaneModel n)) (LinearMap.id - W.toLinearMap) ≤
          kyFanSum (finrank ℂ (phasePlaneModel n)) (LinearMap.id - Z.toLinearMap) := by
  let W := phasePlaneModelUnitary n theta
  have h := phasePlaneModel_attains n theta hzero hpi
  exact ⟨W, h.1, h.2, fun Z hZ => h.le_competitor Z hZ⟩

/-- The finite-plane minimizer, transported to *any* ambient complex Hilbert
space with a specified principal-plane coordinate equivalence. The hypotheses
only describe the coordinate model; they do not impose acuteness or restrict
which unitary competitors are permitted. -/
theorem exists_global_trace_minimizer_of_phasePlaneModel
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H]
    (U V : Submodule ℂ H) (n : ℕ) (theta : Fin (n + 1) → ℝ)
    (hzero : ∀ i, 0 ≤ theta i) (hpi : ∀ i, theta i ≤ Real.pi / 2)
    (F : phasePlaneModel n ≃ₗᵢ[ℂ] H)
    (hU : (phasePlaneModelSource n).map F.toLinearMap = U)
    (hV : (phasePlaneModelTarget n theta).map F.toLinearMap = V) :
    ∃ W : H ≃ₗᵢ[ℂ] H,
      U.map W.toLinearMap = V ∧
      kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) =
        kyFanSum (finrank ℂ H) (projection U - projection V) ∧
      ∀ Z : H ≃ₗᵢ[ℂ] H, U.map Z.toLinearMap = V →
        kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) ≤
          kyFanSum (finrank ℂ H) (LinearMap.id - Z.toLinearMap) := by
  exact (phasePlaneModel_attains n theta hzero hpi).exists_minimizer_of_unitaryEquivalent
    F U V hU hV

/-! ## Principal-plane model with an arbitrary unchanged orthogonal summand -/

/-- An arbitrary unchanged orthogonal summand may be added to the finite
plane model.  It covers common intersection directions and the exterior
orthogonal complement without changing the exact trace minimum. -/
theorem phasePlaneModel_with_fixed_attains
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [FiniteDimensional ℂ G]
    (C : Submodule ℂ G) (n : ℕ) (theta : Fin (n + 1) → ℝ)
    (hzero : ∀ i, 0 ≤ theta i)
    (hpi : ∀ i, theta i ≤ Real.pi / 2) :
    AttainsProjectionTraceBound
      (orthogonalBlockSumSubmodule (phasePlaneModelSource n) C)
      (orthogonalBlockSumSubmodule (phasePlaneModelTarget n theta) C)
      (LinearIsometryEquiv.withLpProdCongr 2
        (phasePlaneModelUnitary n theta) (LinearIsometryEquiv.refl ℂ G)) := by
  exact attainsProjectionTraceBound_orthogonalBlockSum
    (phasePlaneModelSource n) (phasePlaneModelTarget n theta) C C
    (phasePlaneModelUnitary n theta) (LinearIsometryEquiv.refl ℂ G)
    (phasePlaneModel_attains n theta hzero hpi)
    (AttainsProjectionTraceBound.refl C)

/-- The full trace of the projector difference on the plane model together
with an arbitrary unchanged block is just twice the sum of principal sines. -/
theorem phasePlaneModel_with_fixed_projection_trace_formula
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [FiniteDimensional ℂ G]
    (C : Submodule ℂ G) (n : ℕ) (theta : Fin (n + 1) → ℝ)
    (hzero : ∀ i, 0 ≤ theta i)
    (hpi : ∀ i, theta i ≤ Real.pi / 2) :
    kyFanSum (finrank ℂ (WithLp 2 (phasePlaneModel n × G)))
      (projection (orthogonalBlockSumSubmodule (phasePlaneModelSource n) C) -
        projection (orthogonalBlockSumSubmodule (phasePlaneModelTarget n theta) C)) =
        ∑ i : Fin (n + 1), 2 * Real.sin (theta i) := by
  rw [projection_orthogonalBlockSumSubmodule,
    projection_orthogonalBlockSumSubmodule, ← orthogonalBlockSum_sub,
    kyFanSum_orthogonalBlockSum_full]
  have hzeroC :
      kyFanSum (finrank ℂ G) (projection C - projection C) = 0 := by
    simp [kyFanSum_eq_sum_fin, LinearMap.singularValues_zero]
  rw [hzeroC, add_zero]
  exact phasePlaneModel_projection_trace_formula n theta hzero hpi

/-- The explicit phase unitary and identity block attain the projector trace
norm for the direct sum of the moving principal planes and an arbitrary fixed
subspace. The minimum is among all transporting ambient unitaries. -/
theorem phasePlaneModel_with_fixed_global_trace_minimizer
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [FiniteDimensional ℂ G]
    (C : Submodule ℂ G) (n : ℕ) (theta : Fin (n + 1) → ℝ)
    (hzero : ∀ i, 0 ≤ theta i)
    (hpi : ∀ i, theta i ≤ Real.pi / 2) :
    ∃ W : WithLp 2 (phasePlaneModel n × G) ≃ₗᵢ[ℂ]
        WithLp 2 (phasePlaneModel n × G),
      (orthogonalBlockSumSubmodule (phasePlaneModelSource n) C).map W.toLinearMap =
        orthogonalBlockSumSubmodule (phasePlaneModelTarget n theta) C ∧
      kyFanSum (finrank ℂ (WithLp 2 (phasePlaneModel n × G)))
          (LinearMap.id - W.toLinearMap) =
        kyFanSum (finrank ℂ (WithLp 2 (phasePlaneModel n × G)))
          (projection (orthogonalBlockSumSubmodule (phasePlaneModelSource n) C) -
            projection (orthogonalBlockSumSubmodule (phasePlaneModelTarget n theta) C)) ∧
      ∀ Z : WithLp 2 (phasePlaneModel n × G) ≃ₗᵢ[ℂ]
          WithLp 2 (phasePlaneModel n × G),
        (orthogonalBlockSumSubmodule (phasePlaneModelSource n) C).map Z.toLinearMap =
          orthogonalBlockSumSubmodule (phasePlaneModelTarget n theta) C →
        kyFanSum (finrank ℂ (WithLp 2 (phasePlaneModel n × G)))
            (LinearMap.id - W.toLinearMap) ≤
          kyFanSum (finrank ℂ (WithLp 2 (phasePlaneModel n × G)))
            (LinearMap.id - Z.toLinearMap) := by
  let W := LinearIsometryEquiv.withLpProdCongr 2
    (phasePlaneModelUnitary n theta) (LinearIsometryEquiv.refl ℂ G)
  have h := phasePlaneModel_with_fixed_attains C n theta hzero hpi
  exact ⟨W, h.1, h.2, fun Z hZ => h.le_competitor Z hZ⟩

/-- Exact principal-sine trace formula for a pair obtained from finitely
many complex principal planes and an unchanged complement by an ambient
unitary equivalence.  Unlike the minimizer equality, this records the actual
value of the trace norm, not only its attaining unitary. -/
theorem projection_trace_formula_of_phasePlaneModel_with_fixed
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
    (U V : Submodule ℂ H) (C : Submodule ℂ G)
    (n : ℕ) (theta : Fin (n + 1) → ℝ)
    (hzero : ∀ i, 0 ≤ theta i)
    (hpi : ∀ i, theta i ≤ Real.pi / 2)
    (F : WithLp 2 (phasePlaneModel n × G) ≃ₗᵢ[ℂ] H)
    (hU : (orthogonalBlockSumSubmodule (phasePlaneModelSource n) C).map
      F.toLinearMap = U)
    (hV : (orthogonalBlockSumSubmodule (phasePlaneModelTarget n theta) C).map
      F.toLinearMap = V) :
    kyFanSum (finrank ℂ H) (projection U - projection V) =
      ∑ i : Fin (n + 1), 2 * Real.sin (theta i) := by
  have hproj : projection U - projection V =
      F.toLinearMap ∘ₗ
        (projection (orthogonalBlockSumSubmodule (phasePlaneModelSource n) C) -
          projection (orthogonalBlockSumSubmodule (phasePlaneModelTarget n theta) C)) ∘ₗ
        F.symm.toLinearMap := by
    rw [← hU, ← hV]
    rw [projection_map_conjugate F, projection_map_conjugate F]
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  have hdim : finrank ℂ H =
      finrank ℂ (WithLp 2 (phasePlaneModel n × G)) :=
    F.toLinearEquiv.finrank_eq.symm
  rw [hproj, kyFanSum_conjugate, hdim]
  exact phasePlaneModel_with_fixed_projection_trace_formula C n theta hzero hpi

/-- The finite-plane trace minimizer with an unchanged common/exterior block,
transported to any ambient complex Hilbert space with such a decomposition. -/
theorem exists_global_trace_minimizer_of_phasePlaneModel_with_fixed
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]
    (U V : Submodule ℂ H) (C : Submodule ℂ G)
    (n : ℕ) (theta : Fin (n + 1) → ℝ)
    (hzero : ∀ i, 0 ≤ theta i)
    (hpi : ∀ i, theta i ≤ Real.pi / 2)
    (F : WithLp 2 (phasePlaneModel n × G) ≃ₗᵢ[ℂ] H)
    (hU : (orthogonalBlockSumSubmodule (phasePlaneModelSource n) C).map
      F.toLinearMap = U)
    (hV : (orthogonalBlockSumSubmodule (phasePlaneModelTarget n theta) C).map
      F.toLinearMap = V) :
    ∃ W : H ≃ₗᵢ[ℂ] H,
      U.map W.toLinearMap = V ∧
      kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) =
        kyFanSum (finrank ℂ H) (projection U - projection V) ∧
      ∀ Z : H ≃ₗᵢ[ℂ] H, U.map Z.toLinearMap = V →
        kyFanSum (finrank ℂ H) (LinearMap.id - W.toLinearMap) ≤
          kyFanSum (finrank ℂ H) (LinearMap.id - Z.toLinearMap) := by
  exact AttainsProjectionTraceBound.exists_minimizer_of_unitaryEquivalent
    (phasePlaneModel_with_fixed_attains C n theta hzero hpi)
    F U V hU hV

end
end ComplexTraceOptimality
end DavisKahan.FiniteDimensional
end TauCeti
