/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.Unbounded

/-!
# Foundational definitions for strong unbounded Riccati theory

This module contains the shared data, graph, domain, reduction, and unitary
transport definitions used by the proof leaves.  It intentionally contains no
spectral-selection or diagonalization theorem, so downstream leaves can import
it without creating a cycle through the public API.
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

/-- Graph subspace of a bounded angular operator in the Hilbert direct sum. -/
noncomputable def unboundedBlockGraph (X : E0 →L[𝕜] E1) :
    Submodule 𝕜 (WithLp 2 (E0 × E1)) :=
  LinearMap.range ((WithLp.linearEquiv 2 𝕜 (E0 × E1)).symm.toLinearMap ∘ₗ
    LinearMap.id.prod X.toLinearMap)

noncomputable instance unboundedBlockGraph_hasOrthogonalProjection
    (X : E0 →L[𝕜] E1) :
    (unboundedBlockGraph X).HasOrthogonalProjection := by
  set G : E0 →L[𝕜] WithLp 2 (E0 × E1) :=
    ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).symm :
        (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) ∘L
      (ContinuousLinearMap.id 𝕜 E0).prod X with hG
  have hGmem : ∀ u : E0, G u ∈ unboundedBlockGraph X := fun u => ⟨u, rfl⟩
  have hGfix : ∀ z ∈ unboundedBlockGraph X,
      G (WithLp.fstL 2 𝕜 E0 E1 z) = z := by
    intro z hz
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hz
    rw [← hu]
    rfl
  have hclosed : IsClosed ((unboundedBlockGraph X : Submodule 𝕜 _) :
      Set (WithLp 2 (E0 × E1))) := by
    rw [← isSeqClosed_iff_isClosed]
    intro seq y hseq hlim
    have hfix : ∀ n, seq n = G (WithLp.fstL 2 𝕜 E0 E1 (seq n)) :=
      fun n => (hGfix _ (hseq n)).symm
    have hlim2 : Filter.Tendsto seq Filter.atTop
        (nhds (G (WithLp.fstL 2 𝕜 E0 E1 y))) := by
      refine Filter.Tendsto.congr (fun n => (hfix n).symm) ?_
      exact (((G ∘L WithLp.fstL 2 𝕜 E0 E1)).continuous.tendsto y).comp hlim
    have hy : y = G (WithLp.fstL 2 𝕜 E0 E1 y) :=
      tendsto_nhds_unique hlim hlim2
    rw [hy]
    exact hGmem _
  have : CompleteSpace (unboundedBlockGraph X) := hclosed.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- A closed subspace is invariant under a closed operator on its domain. -/
def ClosedOperator.InvariantSubspace
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (A : ClosedOperator (𝕜 := 𝕜) (E := G)) (U : Submodule 𝕜 G) : Prop :=
  ∀ x : A.domain, (x : G) ∈ U → A.toLinearMap x ∈ U

/-- A closed subspace reduces a closed operator and the domain splits under
its two orthogonal projections. -/
def ClosedOperator.ReducesSubspace
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (A : ClosedOperator (𝕜 := 𝕜) (E := G)) (U : Submodule 𝕜 G)
    [U.HasOrthogonalProjection] : Prop :=
  (∀ x : A.domain, U.starProjection (x : G) ∈ A.domain) ∧
  (∀ x : A.domain, Uᗮ.starProjection (x : G) ∈ A.domain) ∧
  A.InvariantSubspace U ∧ A.InvariantSubspace Uᗮ

/-- Two closed operators on the same Hilbert space are unitarily equivalent
with explicit transport of domains and operator actions. -/
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

end DavisKahanExt
end ForMathlib
