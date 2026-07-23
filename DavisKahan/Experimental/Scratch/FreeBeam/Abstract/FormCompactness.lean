/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.CoerciveFormResolvent
import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.CompactGraphEmbedding
import Mathlib.Tactic

/-!
# Compact form embeddings give compact resolvents

Rellich compactness enters the form method through the embedding `j : V → H`.
If `j` sends bounded sequences in the form space to sequences with ambiently
Cauchy subsequences, then the variational resolvent `j A⁻¹ j*` is compact in
the same sequential sense.  Consequently the associated unbounded operator
has compact graph embedding.
-/

open Set Filter Topology
open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace Scratch
namespace FreeBeam
namespace Abstract

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Sequential compactness of a continuous embedding on bounded sequences. -/
def SequentiallyCompactEmbedding (j : V →L[ℂ] H) : Prop :=
  ∀ u : ℕ → V,
    (∃ C : ℝ, ∀ n, ‖u n‖ ≤ C) →
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      CauchySeq (fun n => j (u (phi n)))

/-- A bounded operator maps bounded sequences to bounded sequences. -/
theorem bounded_sequence_comp
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : H →L[ℂ] W) (x : ℕ → H)
    {C : ℝ} (hC : ∀ n, ‖x n‖ ≤ C) :
    ∃ D : ℝ, ∀ n, ‖T (x n)‖ ≤ D := by
  refine ⟨‖T‖ * max C 0, ?_⟩
  intro n
  exact (T.le_opNorm (x n)).trans
    (mul_le_mul_of_nonneg_left
      ((hC n).trans (le_max_left _ _)) (norm_nonneg T))

/-- Compactness of the form embedding implies compactness of the ambient
variational resolvent. -/
theorem CoerciveFormData.resolvent_sequentiallyCompact
    (D : CoerciveFormData (H := H) (V := V))
    (hcompact : SequentiallyCompactEmbedding D.embed) :
    SequentiallyCompactOperator D.resolvent := by
  intro f hf
  obtain ⟨C, hC⟩ := hf
  have hubounded : ∃ B : ℝ, ∀ n, ‖D.solutionOperator (f n)‖ ≤ B :=
    bounded_sequence_comp D.solutionOperator f hC
  obtain ⟨phi, hphi, hcauchy⟩ :=
    hcompact (fun n => D.solutionOperator (f n)) hubounded
  exact ⟨phi, hphi, hcauchy⟩

/-- A compact form embedding gives compact graph embedding for the associated
positive self-adjoint operator. -/
theorem CoerciveFormData.associatedOperator_graph_compact
    (D : CoerciveFormData (H := H) (V := V))
    (hcompact : SequentiallyCompactEmbedding D.embed) :
    SequentiallyCompactGraphEmbedding D.associatedOperator := by
  exact inverse_graph_embedding_compact
    D.resolvent D.resolvent_isSelfAdjoint D.resolvent_injective
    (D.resolvent_sequentiallyCompact hcompact)

/-- For the form realization, compactness of the ambient resolvent and the
inverse graph embedding are equivalent. -/
theorem CoerciveFormData.graph_compact_iff_resolvent_compact
    (D : CoerciveFormData (H := H) (V := V)) :
    SequentiallyCompactGraphEmbedding D.associatedOperator ↔
      SequentiallyCompactOperator D.resolvent := by
  exact inverse_graph_compact_iff
    D.resolvent D.resolvent_isSelfAdjoint D.resolvent_injective

end

end Abstract
end FreeBeam
end Scratch
end Experimental
end DavisKahan
end ForMathlib
