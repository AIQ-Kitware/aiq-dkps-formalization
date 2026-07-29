/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.Riccati.UnboundedBasic

/-!
# Product-domain core for unbounded block operators

This leaf adds the bounded off-diagonal coupling to the direct sum of the two
diagonal partial maps.  The operator domain is kept explicit, and coordinate
membership and action are exposed as separate lemmas for the later strong
Riccati reduction.

The direct sum itself, together with its density and closed-graph facts, is
the canonical `TauCeti.LinearPMap.directSum`; nothing is re-derived here.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

/-- The bounded off-diagonal coupling on the Hilbert direct sum. -/
noncomputable def unboundedOffDiagonalCouplingPMap
    (B01 : E1 →L[𝕜] E0) (B10 : E0 →L[𝕜] E1) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 E0 E1).symm :
      (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1)) ∘L
    ((B01 ∘L WithLp.sndL 2 𝕜 E0 E1).prod
      (B10 ∘L WithLp.fstL 2 𝕜 E0 E1))

omit [CompleteSpace E0] [CompleteSpace E1] in
@[simp] theorem unboundedOffDiagonalCouplingPMap_fst
    (B01 : E1 →L[𝕜] E0) (B10 : E0 →L[𝕜] E1)
    (z : WithLp 2 (E0 × E1)) :
    WithLp.fst (unboundedOffDiagonalCouplingPMap B01 B10 z) =
      B01 (WithLp.snd z) := by
  rfl

omit [CompleteSpace E0] [CompleteSpace E1] in
@[simp] theorem unboundedOffDiagonalCouplingPMap_snd
    (B01 : E1 →L[𝕜] E0) (B10 : E0 →L[𝕜] E1)
    (z : WithLp 2 (E0 × E1)) :
    WithLp.snd (unboundedOffDiagonalCouplingPMap B01 B10 z) =
      B10 (WithLp.fst z) := by
  rfl

/-- The canonical partial-map block operator obtained by adding the bounded
coupling to the diagonal direct sum. -/
noncomputable abbrev unboundedBlockOperatorPMapCore
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    WithLp 2 (E0 × E1) →ₗ.[𝕜] WithLp 2 (E0 × E1) :=
  TauCeti.LinearPMap.addBounded
    (TauCeti.LinearPMap.directSum H.A0 H.A1)
    (unboundedOffDiagonalCouplingPMap H.B01 H.B10)

@[simp] theorem unboundedBlockOperatorPMapCore_domain
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    (unboundedBlockOperatorPMapCore H).domain =
      TauCeti.LinearPMap.directSumDomain H.A0 H.A1 := rfl

@[simp] theorem mem_unboundedBlockOperatorPMapCore_domain_iff
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : WithLp 2 (E0 × E1)) :
    z ∈ (unboundedBlockOperatorPMapCore H).domain ↔
      WithLp.fst z ∈ H.A0.domain ∧ WithLp.snd z ∈ H.A1.domain := by
  rfl

@[simp] theorem unboundedBlockOperatorPMapCore_apply_fst
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : (unboundedBlockOperatorPMapCore H).domain) :
    WithLp.fst (unboundedBlockOperatorPMapCore H z) =
      H.A0 (TauCeti.LinearPMap.directSumDomainFst H.A0 H.A1 z) +
        H.B01 (WithLp.snd (z : WithLp 2 (E0 × E1))) := rfl

@[simp] theorem unboundedBlockOperatorPMapCore_apply_snd
    (H : UnboundedBlockDataPMap (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (z : (unboundedBlockOperatorPMapCore H).domain) :
    WithLp.snd (unboundedBlockOperatorPMapCore H z) =
      H.A1 (TauCeti.LinearPMap.directSumDomainSnd H.A0 H.A1 z) +
        H.B10 (WithLp.fst (z : WithLp 2 (E0 × E1))) := rfl

end DavisKahanExt
end TauCeti
