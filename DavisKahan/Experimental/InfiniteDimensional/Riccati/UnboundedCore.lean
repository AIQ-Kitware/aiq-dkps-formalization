/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Riccati.UnboundedBasic

/-!
# Product-domain core for unbounded block operators

This leaf constructs the closed direct sum of two closed operators on the
Hilbert direct sum and then adds the bounded off-diagonal coupling.  The
operator domain is kept explicit, and coordinate membership and action are
exposed as separate lemmas for the later strong Riccati reduction.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- The explicit product domain of two closed operators, transported to the
`L²` Hilbert direct sum. -/
noncomputable def closedOperatorDirectSumDomain
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1)) :
    Submodule 𝕜 (WithLp 2 (E0 × E1)) :=
  (A0.domain.prod A1.domain).comap
    (WithLp.linearEquiv 2 𝕜 (E0 × E1)).toLinearMap

@[simp] theorem mem_closedOperatorDirectSumDomain_iff
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1))
    (z : WithLp 2 (E0 × E1)) :
    z ∈ closedOperatorDirectSumDomain A0 A1 ↔
      WithLp.fst z ∈ A0.domain ∧ WithLp.snd z ∈ A1.domain := by
  rfl

/-- The first coordinate of a vector in the product operator domain, carrying
its membership witness in the first operator domain. -/
def closedOperatorDirectSumDomainFst
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1))
    (z : closedOperatorDirectSumDomain A0 A1) : A0.domain :=
  ⟨WithLp.fst (z : WithLp 2 (E0 × E1)),
    (mem_closedOperatorDirectSumDomain_iff A0 A1 z).mp z.property |>.1⟩

/-- The second coordinate of a vector in the product operator domain, carrying
its membership witness in the second operator domain. -/
def closedOperatorDirectSumDomainSnd
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1))
    (z : closedOperatorDirectSumDomain A0 A1) : A1.domain :=
  ⟨WithLp.snd (z : WithLp 2 (E0 × E1)),
    (mem_closedOperatorDirectSumDomain_iff A0 A1 z).mp z.property |>.2⟩

/-- First-coordinate extraction as a linear map between the bundled domains. -/
def closedOperatorDirectSumDomainFstLinearMap
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1)) :
    closedOperatorDirectSumDomain A0 A1 →ₗ[𝕜] A0.domain where
  toFun := closedOperatorDirectSumDomainFst A0 A1
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Second-coordinate extraction as a linear map between the bundled domains. -/
def closedOperatorDirectSumDomainSndLinearMap
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1)) :
    closedOperatorDirectSumDomain A0 A1 →ₗ[𝕜] A1.domain where
  toFun := closedOperatorDirectSumDomainSnd A0 A1
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Componentwise action of the direct sum on its explicit product domain. -/
noncomputable def closedOperatorDirectSumLinearMap
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1)) :
    closedOperatorDirectSumDomain A0 A1 →ₗ[𝕜] WithLp 2 (E0 × E1) :=
  (WithLp.linearEquiv 2 𝕜 (E0 × E1)).symm.toLinearMap.comp
    ((A0.toLinearMap.comp
      (closedOperatorDirectSumDomainFstLinearMap A0 A1)).prod
     (A1.toLinearMap.comp
      (closedOperatorDirectSumDomainSndLinearMap A0 A1)))

@[simp] theorem closedOperatorDirectSumLinearMap_fst
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1))
    (z : closedOperatorDirectSumDomain A0 A1) :
    WithLp.fst (closedOperatorDirectSumLinearMap A0 A1 z) =
      A0.toLinearMap (closedOperatorDirectSumDomainFst A0 A1 z) := by
  rfl

@[simp] theorem closedOperatorDirectSumLinearMap_snd
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1))
    (z : closedOperatorDirectSumDomain A0 A1) :
    WithLp.snd (closedOperatorDirectSumLinearMap A0 A1 z) =
      A1.toLinearMap (closedOperatorDirectSumDomainSnd A0 A1 z) := by
  rfl

private theorem closedOperatorDirectSumDomain_dense
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1)) :
    Dense ((closedOperatorDirectSumDomain A0 A1 :
      Submodule 𝕜 (WithLp 2 (E0 × E1))) : Set (WithLp 2 (E0 × E1))) := by
  have hprod : Dense
      ((A0.domain : Set E0) ×ˢ (A1.domain : Set E1)) :=
    A0.dense_domain.prod A1.dense_domain
  have himage : Dense
      ((WithLp.homeomorphProd 2 E0 E1).symm ''
        ((A0.domain : Set E0) ×ˢ (A1.domain : Set E1))) :=
    (((WithLp.homeomorphProd 2 E0 E1).symm.isDenseEmbedding.dense_image).2 hprod)
  rw [show ((closedOperatorDirectSumDomain A0 A1 :
      Submodule 𝕜 (WithLp 2 (E0 × E1))) : Set (WithLp 2 (E0 × E1))) =
      (WithLp.homeomorphProd 2 E0 E1).symm ''
        ((A0.domain : Set E0) ×ˢ (A1.domain : Set E1)) by
    ext z
    constructor
    · intro hz
      exact ⟨WithLp.ofLp z, hz, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp]
  exact himage

private theorem closedOperatorDirectSumLinearMap_closedGraph
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1)) :
    IsClosed (Set.range fun z : closedOperatorDirectSumDomain A0 A1 =>
      ((z : WithLp 2 (E0 × E1)), closedOperatorDirectSumLinearMap A0 A1 z)) := by
  let coords :
      (WithLp 2 (E0 × E1) × WithLp 2 (E0 × E1)) →
        ((E0 × E0) × (E1 × E1)) :=
    fun p => ((WithLp.fst p.1, WithLp.fst p.2),
      (WithLp.snd p.1, WithLp.snd p.2))
  have hcoords : Continuous coords := by
    fun_prop
  have hclosed : IsClosed
      ((Set.range fun x : A0.domain => ((x : E0), A0.toLinearMap x)) ×ˢ
       (Set.range fun y : A1.domain => ((y : E1), A1.toLinearMap y))) :=
    A0.closed_graph.prod A1.closed_graph
  rw [show Set.range (fun z : closedOperatorDirectSumDomain A0 A1 =>
      ((z : WithLp 2 (E0 × E1)), closedOperatorDirectSumLinearMap A0 A1 z)) =
      coords ⁻¹'
        ((Set.range fun x : A0.domain => ((x : E0), A0.toLinearMap x)) ×ˢ
         (Set.range fun y : A1.domain => ((y : E1), A1.toLinearMap y))) by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨
        ⟨closedOperatorDirectSumDomainFst A0 A1 z, by ext <;> rfl⟩,
        ⟨closedOperatorDirectSumDomainSnd A0 A1 z, by ext <;> rfl⟩⟩
    · rintro ⟨⟨x0, hx0⟩, ⟨x1, hx1⟩⟩
      have hx0_fst : (x0 : E0) = WithLp.fst p.1 := congrArg Prod.fst hx0
      have hx0_snd : A0.toLinearMap x0 = WithLp.fst p.2 := congrArg Prod.snd hx0
      have hx1_fst : (x1 : E1) = WithLp.snd p.1 := congrArg Prod.fst hx1
      have hx1_snd : A1.toLinearMap x1 = WithLp.snd p.2 := congrArg Prod.snd hx1
      let z : closedOperatorDirectSumDomain A0 A1 :=
        ⟨p.1, (mem_closedOperatorDirectSumDomain_iff A0 A1 p.1).2
          ⟨hx0_fst ▸ x0.property, hx1_fst ▸ x1.property⟩⟩
      have hz0 : closedOperatorDirectSumDomainFst A0 A1 z = x0 :=
        Subtype.ext hx0_fst.symm
      have hz1 : closedOperatorDirectSumDomainSnd A0 A1 z = x1 :=
        Subtype.ext hx1_fst.symm
      refine ⟨z, Prod.ext rfl ?_⟩
      apply (WithLp.linearEquiv 2 𝕜 (E0 × E1)).injective
      apply Prod.ext
      · simpa [hz0] using hx0_snd
      · simpa [hz1] using hx1_snd]
  exact hclosed.preimage hcoords

/-- The closed direct sum of two closed operators on the Hilbert direct sum. -/
noncomputable def closedOperatorDirectSum
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1)) :
    ClosedOperator (𝕜 := 𝕜) (E := WithLp 2 (E0 × E1)) where
  domain := closedOperatorDirectSumDomain A0 A1
  toLinearMap := closedOperatorDirectSumLinearMap A0 A1
  dense_domain := closedOperatorDirectSumDomain_dense A0 A1
  closed_graph := closedOperatorDirectSumLinearMap_closedGraph A0 A1

@[simp] theorem closedOperatorDirectSum_domain
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1)) :
    (closedOperatorDirectSum A0 A1).domain =
      closedOperatorDirectSumDomain A0 A1 := rfl

@[simp] theorem mem_closedOperatorDirectSum_domain_iff
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1))
    (z : WithLp 2 (E0 × E1)) :
    z ∈ (closedOperatorDirectSum A0 A1).domain ↔
      WithLp.fst z ∈ A0.domain ∧ WithLp.snd z ∈ A1.domain := by
  rfl

@[simp] theorem closedOperatorDirectSum_apply_fst
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1))
    (z : (closedOperatorDirectSum A0 A1).domain) :
    WithLp.fst ((closedOperatorDirectSum A0 A1).toLinearMap z) =
      A0.toLinearMap (closedOperatorDirectSumDomainFst A0 A1 z) := by
  rfl

@[simp] theorem closedOperatorDirectSum_apply_snd
    (A0 : ClosedOperator (𝕜 := 𝕜) (E := E0))
    (A1 : ClosedOperator (𝕜 := 𝕜) (E := E1))
    (z : (closedOperatorDirectSum A0 A1).domain) :
    WithLp.snd ((closedOperatorDirectSum A0 A1).toLinearMap z) =
      A1.toLinearMap (closedOperatorDirectSumDomainSnd A0 A1 z) := by
  rfl

/-- The bounded off-diagonal coupling on the Hilbert direct sum. -/
noncomputable def unboundedOffDiagonalCoupling
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).symm :
      (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) ∘L
    ((H.B01 ∘L WithLp.sndL 2 𝕜 E0 E1).prod
      (H.B10 ∘L WithLp.fstL 2 𝕜 E0 E1))

@[simp] theorem unboundedOffDiagonalCoupling_fst
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : WithLp 2 (E0 × E1)) :
    WithLp.fst (unboundedOffDiagonalCoupling H z) = H.B01 (WithLp.snd z) := by
  rfl

@[simp] theorem unboundedOffDiagonalCoupling_snd
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : WithLp 2 (E0 × E1)) :
    WithLp.snd (unboundedOffDiagonalCoupling H z) = H.B10 (WithLp.fst z) := by
  rfl

/-- The closed unbounded block operator obtained by adding the bounded
coupling to the closed diagonal direct sum. -/
noncomputable def unboundedBlockOperatorCore
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    ClosedOperator (𝕜 := 𝕜) (E := WithLp 2 (E0 × E1)) :=
  (closedOperatorDirectSum H.A0 H.A1).addBounded
    (unboundedOffDiagonalCoupling H)

@[simp] theorem unboundedBlockOperatorCore_domain
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    (unboundedBlockOperatorCore H).domain =
      closedOperatorDirectSumDomain H.A0 H.A1 := rfl

@[simp] theorem mem_unboundedBlockOperatorCore_domain_iff
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : WithLp 2 (E0 × E1)) :
    z ∈ (unboundedBlockOperatorCore H).domain ↔
      WithLp.fst z ∈ H.A0.domain ∧ WithLp.snd z ∈ H.A1.domain := by
  rfl

@[simp] theorem unboundedBlockOperatorCore_apply_fst
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : (unboundedBlockOperatorCore H).domain) :
    WithLp.fst ((unboundedBlockOperatorCore H).toLinearMap z) =
      H.A0.toLinearMap (closedOperatorDirectSumDomainFst H.A0 H.A1 z) +
        H.B01 (WithLp.snd (z : WithLp 2 (E0 × E1))) := by
  rfl

@[simp] theorem unboundedBlockOperatorCore_apply_snd
    (H : UnboundedBlockData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : (unboundedBlockOperatorCore H).domain) :
    WithLp.snd ((unboundedBlockOperatorCore H).toLinearMap z) =
      H.A1.toLinearMap (closedOperatorDirectSumDomainSnd H.A0 H.A1 z) +
        H.B10 (WithLp.fst (z : WithLp 2 (E0 × E1))) := by
  rfl

end DavisKahanExt
end ForMathlib
