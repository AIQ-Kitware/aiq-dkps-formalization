/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

module

public import DavisKahan.SpectralTheory.FormMethod.CoerciveFormResolvent
public import DavisKahan.SpectralTheory.FormMethod.CompactGraphEmbedding
public import Mathlib.Tactic

/-!
# Compact form embeddings give compact resolvents

Rellich compactness enters the form method through the embedding `j : V → H`.
If `j` is compact, so is the variational resolvent `j A⁻¹ j*`.
The associated unbounded operator then has compact graph embedding.
-/

public section

open Set Filter Topology
open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

omit [CompleteSpace H] in
/-- A compact form embedding makes the variational resolvent compact. -/
theorem CoerciveFormData.isCompactOperator_resolvent
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V))
    (hcompact : IsCompactOperator D.embed) :
    IsCompactOperator D.resolvent :=
  InnerProductSpace.isCompactOperator_formSolutionOperator D.sesqForm D.sesqForm_isUnit hcompact

omit [CompleteSpace H] in
/-- A compact form embedding gives compact graph embedding for the associated
positive self-adjoint operator. -/
theorem CoerciveFormData.associatedOperator_graph_compact
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V))
    (hcompact : IsCompactOperator D.embed) :
    SequentiallyCompactGraphEmbedding D.associatedOperator := by
  rw [D.associatedOperator_eq_inverse]
  exact inverse_graph_embedding_compact
    D.resolvent D.resolvent_injective
    (D.isCompactOperator_resolvent hcompact)

/-- For the form realization, compactness of the ambient resolvent and the
inverse graph embedding are equivalent. -/
theorem CoerciveFormData.graph_compact_iff_resolvent_compact
    (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    SequentiallyCompactGraphEmbedding D.associatedOperator ↔
      IsCompactOperator D.resolvent := by
  rw [D.associatedOperator_eq_inverse]
  exact inverse_graph_compact_iff
    D.resolvent D.resolvent_injective

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
