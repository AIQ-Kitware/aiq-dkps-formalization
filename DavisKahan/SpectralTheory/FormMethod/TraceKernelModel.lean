/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.SpectralTheory.ClosedOperator.Basic
import Mathlib.Tactic

/-!
# A graph-Hilbert model for fourth-order endpoint traces

Endpoint traces are continuous in a Sobolev or graph norm, not in the ambient
`L²` norm.  Consequently the maximal fourth-derivative domain should first be
represented by its own Hilbert space `V`, equipped with a continuous injective
embedding into the ambient Hilbert space `H`.

This file packages that representation and constructs the free boundary
subspace as the joint kernel of four continuous trace maps.  The free subspace
is automatically closed and complete.  It also supplies the algebraic ambient
domain and the fourth derivative transported to that domain.

The remaining analytic tasks are cleanly separated:

* construct the concrete interval graph space `V`;
* prove density of the free embedding;
* prove closedness of the transported graph;
* prove the Green and energy identities by density from the smooth core.
-/

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations
namespace FreeBeam
namespace Abstract

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Maximal fourth-order graph space with continuous endpoint traces. -/
structure FourthOrderTraceModel where
  embed : V →L[ℂ] H
  embed_injective : Function.Injective embed
  fourth : V →L[ℂ] H
  traceSecondLeft : V →L[ℂ] ℂ
  traceThirdLeft : V →L[ℂ] ℂ
  traceSecondRight : V →L[ℂ] ℂ
  traceThirdRight : V →L[ℂ] ℂ

namespace FourthOrderTraceModel

/-- Joint kernel of the four free-end traces. -/
noncomputable def freeSubspace (D : FourthOrderTraceModel (H := H) (V := V)) :
    Submodule ℂ V :=
  D.traceSecondLeft.ker ⊓ D.traceThirdLeft.ker ⊓
    D.traceSecondRight.ker ⊓ D.traceThirdRight.ker

omit [CompleteSpace H] [CompleteSpace V] in
/-- Membership in the free subspace is exactly the four endpoint conditions. -/
theorem mem_freeSubspace_iff
    (D : FourthOrderTraceModel (H := H) (V := V)) (x : V) :
    x ∈ D.freeSubspace ↔
      D.traceSecondLeft x = 0 ∧
      D.traceThirdLeft x = 0 ∧
      D.traceSecondRight x = 0 ∧
      D.traceThirdRight x = 0 := by
  simp [freeSubspace, and_assoc]

omit [CompleteSpace H] [CompleteSpace V] in
/-- The joint trace kernel is closed in the graph Hilbert space. -/
theorem isClosed_freeSubspace
    (D : FourthOrderTraceModel (H := H) (V := V)) :
    IsClosed (D.freeSubspace : Set V) := by
  simpa [freeSubspace] using
    (((D.traceSecondLeft.isClosed_ker.inter D.traceThirdLeft.isClosed_ker).inter
      D.traceSecondRight.isClosed_ker).inter D.traceThirdRight.isClosed_ker)

/-- The free trace kernel inherits completeness. -/
noncomputable instance freeSubspaceCompleteSpace
    (D : FourthOrderTraceModel (H := H) (V := V)) :
    CompleteSpace D.freeSubspace :=
  D.isClosed_freeSubspace.completeSpace_coe

/-- Ambient embedding restricted to the free trace kernel. -/
noncomputable def freeEmbed
    (D : FourthOrderTraceModel (H := H) (V := V)) :
    D.freeSubspace →L[ℂ] H :=
  D.embed.comp (Submodule.subtypeL D.freeSubspace)

/-- Fourth derivative restricted to the free trace kernel. -/
noncomputable def freeFourth
    (D : FourthOrderTraceModel (H := H) (V := V)) :
    D.freeSubspace →L[ℂ] H :=
  D.fourth.comp (Submodule.subtypeL D.freeSubspace)

/-- The free embedding, unfolded. -/
@[simp] theorem freeEmbed_apply
    (D : FourthOrderTraceModel (H := H) (V := V))
    (x : D.freeSubspace) :
    D.freeEmbed x = D.embed (x : V) := rfl

/-- The fourth-order operator on the free model, unfolded. -/
@[simp] theorem freeFourth_apply
    (D : FourthOrderTraceModel (H := H) (V := V))
    (x : D.freeSubspace) :
    D.freeFourth x = D.fourth (x : V) := rfl

omit [CompleteSpace H] [CompleteSpace V] in
/-- The restricted ambient embedding remains injective. -/
theorem freeEmbed_injective
    (D : FourthOrderTraceModel (H := H) (V := V)) :
    Function.Injective D.freeEmbed := by
  intro x y hxy
  apply Subtype.ext
  exact D.embed_injective hxy

/-- Ambient operator domain obtained from the free graph space. -/
noncomputable def freeAmbientDomain
    (D : FourthOrderTraceModel (H := H) (V := V)) :
    Submodule ℂ H :=
  LinearMap.range D.freeEmbed.toLinearMap

/-- Linear equivalence from the free graph space onto its ambient image. -/
noncomputable def freeRangeEquiv
    (D : FourthOrderTraceModel (H := H) (V := V)) :
    D.freeSubspace ≃ₗ[ℂ] D.freeAmbientDomain :=
  LinearEquiv.ofInjective D.freeEmbed.toLinearMap D.freeEmbed_injective

/-- Recover the graph-space representative of an ambient domain vector. -/
noncomputable def freeAmbientInverse
    (D : FourthOrderTraceModel (H := H) (V := V)) :
    D.freeAmbientDomain →ₗ[ℂ] D.freeSubspace :=
  D.freeRangeEquiv.symm.toLinearMap

/-- Fourth derivative transported to the ambient domain. -/
noncomputable def freeFourthAmbient
    (D : FourthOrderTraceModel (H := H) (V := V)) :
    D.freeAmbientDomain →ₗ[ℂ] H :=
  D.freeFourth.toLinearMap.comp D.freeAmbientInverse

/-- The ambient inverse undoes the free embedding. -/
@[simp] theorem freeAmbientInverse_freeEmbed
    (D : FourthOrderTraceModel (H := H) (V := V))
    (x : D.freeSubspace) :
    D.freeAmbientInverse
      ⟨D.freeEmbed x,
        LinearMap.mem_range_self D.freeEmbed.toLinearMap x⟩ = x := by
  change D.freeRangeEquiv.symm (D.freeRangeEquiv x) = x
  exact D.freeRangeEquiv.symm_apply_apply x

/-- The ambient fourth-order operator agrees with the model one through the embedding. -/
@[simp] theorem freeFourthAmbient_freeEmbed
    (D : FourthOrderTraceModel (H := H) (V := V))
    (x : D.freeSubspace) :
    D.freeFourthAmbient
      ⟨D.freeEmbed x,
        LinearMap.mem_range_self D.freeEmbed.toLinearMap x⟩ =
      D.freeFourth x := by
  change D.freeFourth
      (D.freeAmbientInverse
        ⟨D.freeEmbed x,
          LinearMap.mem_range_self D.freeEmbed.toLinearMap x⟩) =
    D.freeFourth x
  rw [D.freeAmbientInverse_freeEmbed]

omit [CompleteSpace H] [CompleteSpace V] in
/-- Density of a concrete smooth free core inside the ambient Hilbert space is
 enough to prove density of the transported free operator domain. -/
theorem dense_freeAmbientDomain_of_dense_subset_range
    (D : FourthOrderTraceModel (H := H) (V := V))
    {S : Set H} (hS : Dense S)
    (hsub : S ⊆ Set.range D.freeEmbed) :
    Dense (D.freeAmbientDomain : Set H) := by
  apply hS.mono
  intro x hx
  obtain ⟨y, rfl⟩ := hsub hx
  exact LinearMap.mem_range_self D.freeEmbed.toLinearMap y

omit [CompleteSpace H] [CompleteSpace V] in
/-- A dense free embedding gives a dense ambient operator domain. -/
theorem dense_freeAmbientDomain
    (D : FourthOrderTraceModel (H := H) (V := V))
    (hdense : DenseRange D.freeEmbed) :
    Dense (D.freeAmbientDomain : Set H) := by
  simpa [freeAmbientDomain, DenseRange, LinearMap.coe_range] using hdense

/-- Once graph closedness has been proved, the trace model produces the
 project's bundled closed operator directly. -/
noncomputable def toClosedOperator
    (D : FourthOrderTraceModel (H := H) (V := V))
    (hdense : Dense (D.freeAmbientDomain : Set H))
    (hclosed : IsClosed (Set.range fun x : D.freeAmbientDomain =>
      ((x : H), D.freeFourthAmbient x))) :
    DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H) where
  domain := D.freeAmbientDomain
  toLinearMap := D.freeFourthAmbient
  dense_domain := hdense
  closed_graph := hclosed

/-- The domain of the derived closed operator. -/
@[simp] theorem toClosedOperator_domain
    (D : FourthOrderTraceModel (H := H) (V := V))
    (hdense : Dense (D.freeAmbientDomain : Set H))
    (hclosed : IsClosed (Set.range fun x : D.freeAmbientDomain =>
      ((x : H), D.freeFourthAmbient x))) :
    (D.toClosedOperator hdense hclosed).domain = D.freeAmbientDomain := rfl

/-- Its action, which is the model's fourth-order operator. -/
@[simp] theorem toClosedOperator_apply
    (D : FourthOrderTraceModel (H := H) (V := V))
    (hdense : Dense (D.freeAmbientDomain : Set H))
    (hclosed : IsClosed (Set.range fun x : D.freeAmbientDomain =>
      ((x : H), D.freeFourthAmbient x)))
    (x : D.freeAmbientDomain) :
    (D.toClosedOperator hdense hclosed).toLinearMap x =
      D.freeFourthAmbient x := rfl

end FourthOrderTraceModel

end

end Abstract
end FreeBeam
end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti