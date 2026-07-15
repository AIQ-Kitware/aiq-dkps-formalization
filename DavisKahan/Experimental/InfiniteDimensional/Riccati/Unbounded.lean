/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.Unbounded
import DavisKahan.Experimental.InfiniteDimensional.Riccati.Bounded

/-!
# Strong solutions of unbounded operator Riccati equations

The bounded off-diagonal perturbation is placed on the product domain of the
closed diagonal entries.  A bounded angular operator is a strong Riccati
solution when it transports the first diagonal domain into the second and the
Riccati identity holds there.  The graph calculation is therefore an equality
of domain-aware block vectors, not a purely formal identity of ambient maps.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- Unbounded diagonal block data with bounded off-diagonal coupling. -/
structure UnboundedBlockData where
  A0 : ClosedOperator (𝕜 := 𝕜) (E := E0)
  A1 : ClosedOperator (𝕜 := 𝕜) (E := E1)
  B01 : E1 →L[𝕜] E0
  B10 : E0 →L[𝕜] E1
  selfAdjoint0 : A0.IsSelfAdjoint
  selfAdjoint1 : A1.IsSelfAdjoint
  offDiagonalAdjoint : ∀ x y, ⟪B01 y, x⟫_𝕜 = ⟪y, B10 x⟫_𝕜

/-- A bounded angular operator preserves the unbounded diagonal domains. -/
def PreservesRiccatiDomains
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∀ x : H.A0.domain, X (x : E0) ∈ H.A1.domain

/-- Strong Riccati solution, including the domain condition. -/
def StrongSolvesRiccati
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∃ hdom : PreservesRiccatiDomains H X,
    ∀ x : H.A0.domain,
      H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ -
        X (H.A0.toLinearMap x) -
        X (H.B01 (X (x : E0))) + H.B10 (x : E0) = 0

/-- Ambient coordinate equivalence for the Hilbert direct sum. -/
noncomputable abbrev unboundedBlockCoordinates :
    WithLp 2 (E0 × E1) ≃ₗ[𝕜] E0 × E1 :=
  WithLp.linearEquiv 2 𝕜 (E0 × E1)

/-- Product domain of the two diagonal closed operators. -/
noncomputable def unboundedBlockDomain
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    Submodule 𝕜 (WithLp 2 (E0 × E1)) :=
  { carrier := {z | (unboundedBlockCoordinates (𝕜 := 𝕜) z).1 ∈ H.A0.domain ∧
      (unboundedBlockCoordinates (𝕜 := 𝕜) z).2 ∈ H.A1.domain}
    zero_mem' := by simp
    add_mem' := by
      rintro x y ⟨hx0, hx1⟩ ⟨hy0, hy1⟩
      exact ⟨H.A0.domain.add_mem hx0 hy0, H.A1.domain.add_mem hx1 hy1⟩
    smul_mem' := by
      rintro c x ⟨hx0, hx1⟩
      exact ⟨H.A0.domain.smul_mem c hx0, H.A1.domain.smul_mem c hx1⟩ }

/-- First domain coordinate of a block-domain vector. -/
noncomputable def unboundedDomainFirst
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : unboundedBlockDomain H) : H.A0.domain :=
  ⟨(unboundedBlockCoordinates (𝕜 := 𝕜) (z : WithLp 2 (E0 × E1))).1, z.property.1⟩

/-- Second domain coordinate of a block-domain vector. -/
noncomputable def unboundedDomainSecond
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : unboundedBlockDomain H) : H.A1.domain :=
  ⟨(unboundedBlockCoordinates (𝕜 := 𝕜) (z : WithLp 2 (E0 × E1))).2, z.property.2⟩

/-- Componentwise block action on the product domain. -/
noncomputable def unboundedBlockAction
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    unboundedBlockDomain H →ₗ[𝕜] WithLp 2 (E0 × E1) :=
  (unboundedBlockCoordinates (𝕜 := 𝕜)).symm.toLinearMap.comp
    { toFun := fun z =>
        (H.A0.toLinearMap (unboundedDomainFirst H z) +
            H.B01 (unboundedDomainSecond H z),
          H.B10 (unboundedDomainFirst H z) +
            H.A1.toLinearMap (unboundedDomainSecond H z))
      map_add' := by intro x y; simp [unboundedDomainFirst, unboundedDomainSecond]
      map_smul' := by intro c x; simp [unboundedDomainFirst, unboundedDomainSecond] }

/-- Closed block operator matrix on the Hilbert direct sum. -/
noncomputable def unboundedBlockOperator
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    ClosedOperator (𝕜 := 𝕜) (E := WithLp 2 (E0 × E1)) :=
  { domain := unboundedBlockDomain H
    toLinearMap := unboundedBlockAction H
    dense_domain := by
      rw [dense_iff_closure_eq]
      apply Submodule.top_unique
      intro z hz
      let p := unboundedBlockCoordinates (𝕜 := 𝕜) z
      obtain ⟨x, hx⟩ := H.A0.dense_domain.exists_tendsto p.1
      obtain ⟨y, hy⟩ := H.A1.dense_domain.exists_tendsto p.2
      exact closure_prod_domain_mem H x y hx hy
    closed_graph := by
      -- The diagonal product is closed.  The off-diagonal block map is bounded
      -- on the ambient direct sum, so adding it preserves graph closedness.
      let D := ClosedOperator.product H.A0 H.A1
      let B : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) :=
        blockContinuousLinearMap 0 H.B01 H.B10 0
      simpa [unboundedBlockDomain, unboundedBlockAction, D, B] using
        D.closed_graph_add_bounded B }

/-- The unbounded block operator is self-adjoint. -/
theorem unboundedBlockOperator_isSelfAdjoint
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    (unboundedBlockOperator H).IsSelfAdjoint := by
  let D := ClosedOperator.product H.A0 H.A1
  let B : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) :=
    blockContinuousLinearMap 0 H.B01 H.B10 0
  have hD : D.IsSelfAdjoint :=
    ClosedOperator.product_isSelfAdjoint H.selfAdjoint0 H.selfAdjoint1
  have hB : IsSelfAdjointOperator B := by
    intro x y
    rcases unboundedBlockCoordinates (𝕜 := 𝕜) x with ⟨x0, x1⟩
    rcases unboundedBlockCoordinates (𝕜 := 𝕜) y with ⟨y0, y1⟩
    simp [B, blockContinuousLinearMap, H.offDiagonalAdjoint]
  simpa [unboundedBlockOperator, D, B] using
    ClosedOperator.isSelfAdjoint_addBounded D hD B hB

/-- Bounded graph embedding `u ↦ (u, Xu)`. -/
noncomputable def unboundedGraphEmbedding (X : E0 →L[𝕜] E1) :
    E0 →L[𝕜] WithLp 2 (E0 × E1) :=
  WithLp.continuousLinearEquiv 2 𝕜 (E0 × E1) |>.symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.id 𝕜 E0 |>.prod X

/-- Graph subspace of a bounded angular operator. -/
noncomputable def unboundedBlockGraph (X : E0 →L[𝕜] E1) :
    Submodule 𝕜 (WithLp 2 (E0 × E1)) :=
  LinearMap.range (unboundedGraphEmbedding X).toLinearMap

/-- The graph of a bounded operator is closed. -/
theorem isClosed_unboundedBlockGraph (X : E0 →L[𝕜] E1) :
    IsClosed (unboundedBlockGraph X : Set (WithLp 2 (E0 × E1))) := by
  have hlower : ∀ x : E0, ‖x‖ ≤ ‖unboundedGraphEmbedding X x‖ := by
    intro x
    rw [WithLp.norm_sq_eq, unboundedGraphEmbedding]
    nlinarith [sq_nonneg ‖X x‖, norm_nonneg x]
  exact LinearMap.isClosed_range_of_bound_below
    (unboundedGraphEmbedding X).toLinearMap 1 zero_lt_one
    (by simpa using hlower)

noncomputable instance unboundedBlockGraph_hasOrthogonalProjection
    (X : E0 →L[𝕜] E1) :
    (unboundedBlockGraph X).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.of_isClosed (isClosed_unboundedBlockGraph X)

/-- Invariance of a closed subspace for a closed operator. -/
def ClosedOperator.InvariantSubspace
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (A : ClosedOperator (𝕜 := 𝕜) (E := G)) (U : Submodule 𝕜 G) : Prop :=
  ∀ x : A.domain, (x : G) ∈ U → A.toLinearMap x ∈ U

/-- Reduction includes invariance of both orthogonal summands and preservation
of the operator domain by both projections. -/
def ClosedOperator.ReducesSubspace
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (A : ClosedOperator (𝕜 := 𝕜) (E := G)) (U : Submodule 𝕜 G)
    [U.HasOrthogonalProjection] : Prop :=
  (∀ x : A.domain, U.starProjection (x : G) ∈ A.domain) ∧
  (∀ x : A.domain, Uᗮ.starProjection (x : G) ∈ A.domain) ∧
  A.InvariantSubspace U ∧ A.InvariantSubspace Uᗮ

/-- Unitary equivalence with explicit two-way transport of domains. -/
def ClosedOperator.UnitaryEquivalent
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (A B : ClosedOperator (𝕜 := 𝕜) (E := G))
    (W Winv : G →L[𝕜] G) : Prop :=
  IsUnitaryOperator W ∧ IsUnitaryOperator Winv ∧
  Winv ∘L W = ContinuousLinearMap.id 𝕜 G ∧
  W ∘L Winv = ContinuousLinearMap.id 𝕜 G ∧
  ∃ hWdom : ∀ x : A.domain, W (x : G) ∈ B.domain,
  ∃ hWinvdom : ∀ y : B.domain, Winv (y : G) ∈ A.domain,
    (∀ x : A.domain,
      B.toLinearMap ⟨W (x : G), hWdom x⟩ = W (A.toLinearMap x)) ∧
    (∀ y : B.domain,
      A.toLinearMap ⟨Winv (y : G), hWinvdom y⟩ = Winv (B.toLinearMap y))

/-- Closed first diagonal block `A0 + B01 X`. -/
noncomputable def unboundedRiccatiDiagonal0
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : ClosedOperator (𝕜 := 𝕜) (E := E0) :=
  H.A0.addBounded (H.B01 ∘L X)

/-- Closed second diagonal block `A1 - B10 X*`. -/
noncomputable def unboundedRiccatiDiagonal1
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : ClosedOperator (𝕜 := 𝕜) (E := E1) :=
  H.A1.addBounded (-(H.B10 ∘L star X))

/-- Product of the two closed Riccati diagonal blocks. -/
noncomputable def unboundedBlockDiagonalOperator
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    ClosedOperator (𝕜 := 𝕜) (E := WithLp 2 (E0 × E1)) :=
  ClosedOperator.product
    (unboundedRiccatiDiagonal0 H X)
    (unboundedRiccatiDiagonal1 H X)

/-- Graph invariance is exactly the strong Riccati equation. -/
theorem graph_invariant_iff_strongRiccati
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    (PreservesRiccatiDomains H X ∧
      (unboundedBlockOperator H).InvariantSubspace (unboundedBlockGraph X)) ↔
      StrongSolvesRiccati H X := by
  constructor
  · rintro ⟨hdom, hinv⟩
    refine ⟨hdom, ?_⟩
    intro x
    let gx : (unboundedBlockOperator H).domain :=
      ⟨unboundedGraphEmbedding X (x : E0), by
        exact ⟨x.property, hdom x⟩⟩
    have hgraph : (gx : WithLp 2 (E0 × E1)) ∈ unboundedBlockGraph X :=
      LinearMap.mem_range_self _ (x : E0)
    have hout := hinv gx hgraph
    obtain ⟨v, hv⟩ := hout
    have hfirst : v = H.A0.toLinearMap x + H.B01 (X (x : E0)) := by
      simpa [unboundedBlockOperator, unboundedBlockAction,
        unboundedGraphEmbedding] using
        congrArg (fun z => (unboundedBlockCoordinates (𝕜 := 𝕜) z).1) hv
    have hsecond : X v = H.B10 (x : E0) +
        H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ := by
      simpa [unboundedBlockOperator, unboundedBlockAction,
        unboundedGraphEmbedding] using
        congrArg (fun z => (unboundedBlockCoordinates (𝕜 := 𝕜) z).2) hv
    rw [hfirst] at hsecond
    linear_combination -hsecond
  · rintro ⟨hdom, hric⟩
    refine ⟨hdom, ?_⟩
    intro z hz
    obtain ⟨u, rfl⟩ := hz
    have hu0 : u ∈ H.A0.domain := by
      exact (show unboundedGraphEmbedding X u ∈ unboundedBlockDomain H from z.property).1
    let x : H.A0.domain := ⟨u, hu0⟩
    let v := H.A0.toLinearMap x + H.B01 (X u)
    refine ⟨v, ?_⟩
    apply (unboundedBlockCoordinates (𝕜 := 𝕜)).symm.injective
    ext
    · simp [unboundedBlockOperator, unboundedBlockAction,
        unboundedGraphEmbedding, v, x]
    · have hx := hric x
      simp [unboundedBlockOperator, unboundedBlockAction,
        unboundedGraphEmbedding, v, x] at hx ⊢
      linear_combination hx

/-- Existence of the selected contractive strong solution under separated
spectra and small bounded coupling. -/
theorem exists_strongRiccati_solution
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (s0 s1 : Set ℝ) {d : ℝ} (hd : 0 < d)
    (hcover0 : H.A0.realSpectrum ⊆ s0) (hcover1 : H.A1.realSpectrum ⊆ s1)
    (hsep : ClosedOperator.SpectralSetsSeparated H.A0 H.A1 s0 s1 d)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ∃ X : E0 →L[𝕜] E1,
      StrongSolvesRiccati H X ∧ ‖X‖ < 1 ∧
      (unboundedBlockOperator H).ReducesSubspace (unboundedBlockGraph X) := by
  let L0 := ClosedOperator.product H.A0 H.A1
  let B : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) :=
    blockContinuousLinearMap 0 H.B01 H.B10 0
  let L := unboundedBlockOperator H
  have hL : L.IsSelfAdjoint := unboundedBlockOperator_isSelfAdjoint H
  have hBnorm : ‖B‖ = ‖H.B01‖ := by
    rw [blockOffDiagonal_norm, norm_eq_of_adjoint_pair H.offDiagonalAdjoint]
  obtain ⟨Γ, hΓsep, hΓindex⟩ :=
    exists_separating_contour_for_unbounded_block
      H s0 s1 hd hcover0 hcover1 hsep hsmall
  let Q := ClosedOperator.rieszProjection L hL Γ
  let V := LinearMap.range Q.toLinearMap
  have hredV : L.ReducesSubspace V :=
    ClosedOperator.rieszProjection_reduces L hL Γ hΓsep
  let U0 : Submodule 𝕜 (WithLp 2 (E0 × E1)) :=
    unboundedBlockGraph (0 : E0 →L[𝕜] E1)
  have hacute : IsAcute U0 V := by
    have hsin := unbounded_contour_projection_gap_bound
      L0 L B Γ hΓsep hBnorm hd hsmall
    exact lt_of_le_of_lt hsin (small_coupling_implies_acute hd hsmall)
  obtain ⟨Y, hYang, hgraph, hYuniq⟩ :=
    existsUnique_angularOperator U0 V hacute
  let X : E0 →L[𝕜] E1 := coordinateAngularOperator Y hYang
  have hgraphX : unboundedBlockGraph X = V := by
    exact coordinateGraph_eq_angularGraph hYang hgraph
  have hcontract : ‖X‖ < 1 := by
    exact coordinateAngularOperator_norm_lt_one hYang hacute
  have hdom : PreservesRiccatiDomains H X := by
    intro x
    -- The Riesz projection commutes with `L` on its domain.  Writing its range
    -- as a graph and comparing the two domain coordinates gives `Xx ∈ dom A1`.
    have hQdom := ClosedOperator.rieszProjection_preserves_domain L hL Γ x
    have hcomm := ClosedOperator.rieszProjection_commutes_on_domain L hL Γ x
    exact graph_range_second_coordinate_mem_domain
      hgraphX hQdom hcomm x
  have hinv : L.InvariantSubspace (unboundedBlockGraph X) := by
    simpa [hgraphX] using hredV.2.2.1
  have hstrong : StrongSolvesRiccati H X :=
    (graph_invariant_iff_strongRiccati H X).2 ⟨hdom, hinv⟩
  have hred : L.ReducesSubspace (unboundedBlockGraph X) := by
    simpa [hgraphX] using hredV
  exact ⟨X, hstrong, hcontract, hred⟩

/-- Strong Riccati solutions with a reducing graph yield a unitary block
diagonalization with two-way domain transport. -/
theorem unbounded_blockDiagonalization
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hX : StrongSolvesRiccati H X)
    (hred : (unboundedBlockOperator H).ReducesSubspace
      (unboundedBlockGraph X)) :
    ∃ W Winv : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1),
      ClosedOperator.UnitaryEquivalent
        (unboundedBlockOperator H) (unboundedBlockDiagonalOperator H X)
        W Winv ∧
      W ∘L projection (unboundedBlockGraph 0) =
        projection (unboundedBlockGraph X) ∘L W := by
  let W := riccatiGraphUnitary X
  let Winv := star W
  have hW : IsUnitaryOperator W := normalizedGraphRotation_unitary X
  have hWinv : IsUnitaryOperator Winv := hW.star
  have hleft : Winv ∘L W = ContinuousLinearMap.id 𝕜 _ := by
    simpa [W, Winv] using hW.star_mul_self
  have hright : W ∘L Winv = ContinuousLinearMap.id 𝕜 _ := by
    simpa [W, Winv] using hW.mul_star_self
  have hintertwine : W ∘L projection (unboundedBlockGraph 0) =
      projection (unboundedBlockGraph X) ∘L W := by
    exact normalizedGraphRotation_intertwines X
  obtain ⟨hdomX, hric⟩ := hX
  have hWdom : ∀ z : (unboundedBlockOperator H).domain,
      W (z : WithLp 2 (E0 × E1)) ∈
        (unboundedBlockDiagonalOperator H X).domain := by
    intro z
    -- Decompose by the reducing graph projections.  `hred` places each
    -- component in the block domain; the explicit normalized graph rotation
    -- sends them to the two coordinate domains.
    exact normalizedGraphRotation_maps_reducing_domain
      H X hdomX hred z
  have hWinvdom : ∀ z : (unboundedBlockDiagonalOperator H X).domain,
      Winv (z : WithLp 2 (E0 × E1)) ∈
        (unboundedBlockOperator H).domain := by
    intro z
    exact normalizedGraphRotation_symm_maps_product_domain
      H X hdomX hred z
  have hforward : ∀ z : (unboundedBlockOperator H).domain,
      (unboundedBlockDiagonalOperator H X).toLinearMap
          ⟨W (z : WithLp 2 (E0 × E1)), hWdom z⟩ =
        W ((unboundedBlockOperator H).toLinearMap z) := by
    intro z
    decompose z using hred into zg zgperp
    · -- On the graph, the first diagonal action is `A0 + B01 X`.
      simpa [W, unboundedBlockDiagonalOperator,
        unboundedRiccatiDiagonal0, unboundedRiccatiDiagonal1] using
        graph_action_conjugation H X hdomX hric zg
    · -- On the orthogonal graph, take the adjoint of the strong equation.
      have hricStar := adjoint_strongRiccati H X hdomX hric hred
      simpa [W, unboundedBlockDiagonalOperator,
        unboundedRiccatiDiagonal0, unboundedRiccatiDiagonal1] using
        orthogonalGraph_action_conjugation H X hricStar zgperp
  have hbackward : ∀ z : (unboundedBlockDiagonalOperator H X).domain,
      (unboundedBlockOperator H).toLinearMap
          ⟨Winv (z : WithLp 2 (E0 × E1)), hWinvdom z⟩ =
        Winv ((unboundedBlockDiagonalOperator H X).toLinearMap z) := by
    intro z
    apply hW.injective
    rw [hforward]
    simp [W, Winv, hright]
  refine ⟨W, Winv, ?_, hintertwine⟩
  exact ⟨hW, hWinv, hleft, hright,
    ⟨hWdom, hWinvdom, hforward, hbackward⟩⟩

end DavisKahanExt
end ForMathlib
