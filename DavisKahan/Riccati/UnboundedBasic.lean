/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ReducingSubspace.Restriction

/-!
# Foundational definitions for strong unbounded Riccati theory

This module contains the shared data, graph, domain, reduction, and unitary
transport definitions used by the proof leaves.  It intentionally contains no
spectral-selection or diagonalization theorem, so downstream leaves can import
it without creating a cycle through the public API.
-/

namespace TauCeti
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

/-- Unbounded diagonal block data in the canonical partial-map representation.
Density, closedness, and self-adjointness remain explicit properties instead
of fields of a local operator bundle. -/
structure UnboundedBlockDataPMap where
  A0 : E0 →ₗ.[𝕜] E0
  A1 : E1 →ₗ.[𝕜] E1
  B01 : E1 →L[𝕜] E0
  B10 : E0 →L[𝕜] E1
  dense0 : Dense (A0.domain : Set E0)
  dense1 : Dense (A1.domain : Set E1)
  closed0 : A0.IsClosed
  closed1 : A1.IsClosed
  selfAdjoint0 : _root_.IsSelfAdjoint A0
  selfAdjoint1 : _root_.IsSelfAdjoint A1
  offDiagonalAdjoint : ∀ x y, ⟪B01 y, x⟫_𝕜 = ⟪y, B10 x⟫_𝕜

/-- View historical Riccati block data through its canonical partial maps. -/
noncomputable def UnboundedBlockData.toPMap
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1) where
  A0 := H.A0.toLinearPMap
  A1 := H.A1.toLinearPMap
  B01 := H.B01
  B10 := H.B10
  dense0 := H.A0.toLinearPMap_dense
  dense1 := H.A1.toLinearPMap_dense
  closed0 := H.A0.toLinearPMap_isClosed
  closed1 := H.A1.toLinearPMap_isClosed
  selfAdjoint0 := H.selfAdjoint0
  selfAdjoint1 := H.selfAdjoint1
  offDiagonalAdjoint := H.offDiagonalAdjoint

/-- A bounded angular operator preserves the unbounded diagonal domains. -/
def PreservesRiccatiDomains
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∀ x : H.A0.domain, X (x : E0) ∈ H.A1.domain

/-- A bounded angular operator preserves the diagonal domains of raw block
data. -/
def PreservesRiccatiPMapDomains
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∀ x : H.A0.domain, X (x : E0) ∈ H.A1.domain

/-- Historical domain preservation agrees definitionally with its raw
partial-map formulation. -/
theorem preservesRiccatiDomains_toPMap_iff
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    PreservesRiccatiDomains H X ↔ PreservesRiccatiPMapDomains H.toPMap X := Iff.rfl

/-- Strong Riccati solution, including the domain condition. -/
def StrongSolvesRiccati
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∃ hdom : PreservesRiccatiDomains H X,
    ∀ x : H.A0.domain,
      H.A1.toLinearMap ⟨X (x : E0), hdom x⟩ -
        X (H.A0.toLinearMap x) -
        X (H.B01 (X (x : E0))) + H.B10 (x : E0) = 0

/-- Strong Riccati solution over canonical partial-map block data. -/
def StrongSolvesRiccatiPMap
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  ∃ hdom : PreservesRiccatiPMapDomains H X,
    ∀ x : H.A0.domain,
      H.A1 ⟨X (x : E0), hdom x⟩ -
        X (H.A0 x) -
        X (H.B01 (X (x : E0))) + H.B10 (x : E0) = 0

/-- Historical strong solutions agree definitionally with their raw
partial-map formulation. -/
theorem strongSolvesRiccati_toPMap_iff
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    StrongSolvesRiccati H X ↔ StrongSolvesRiccatiPMap H.toPMap X := Iff.rfl

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

/-- Two closed operators on the same Hilbert space are unitarily equivalent
with explicit transport of domains and operator actions. -/
abbrev ClosedOperator.UnitaryEquivalent
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (A B : ClosedOperator (𝕜 := 𝕜) (E := G))
    (W Winv : G →L[𝕜] G) : Prop :=
  TauCeti.LinearPMap.UnitaryEquivalent A.toLinearPMap B.toLinearPMap W Winv

end DavisKahanExt
end TauCeti
