/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, roadmap topic T09.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track — additions to `Mathlib/Analysis/OperatorIdeal/`.

Formalized by Claude Opus 5 (claude-opus-5[1m]).

Approximation numbers, linear independence and spans are unchanged by the
transport of a Hilbert space along an isomorphism of `RCLike` fields; hence the
min--max lower-bound property holds at every `RCLike` field.
-/
module

public import ForTauCeti.Analysis.RCLike.ScalarTransport
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.CanonicalGauge

public section

/-! # Approximation numbers under a scalar transport

`TauCeti.ScalarTransport` renames the scalar field of a Hilbert space without
touching its vectors, its norm, or its topology.  Everything an approximation
number sees is therefore unchanged, and this file says so:
`ScalarTransport.approximationNumber_clm`.

The unmerged transport laws remain. Converse min–max localization is supplied
directly by accepted `TauCeti.HasMinMaxLowerBound.of_completeSpace`; the former
field-classification argument and its capability instance have been removed.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: none.  Written directly here, 2026-09-01.
* Extraction class: **new**, written for scalar-transport invariance. The
  former converse min–max application is superseded by accepted Tau Ceti APIs.
* Namespace: `TauCeti.ScalarTransport` for the transport lemmas.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none**.
-/

open scoped InnerProductSpace

universe u w v v'

namespace TauCeti
namespace ScalarTransport

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type v'} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The transport does not change an approximation number: it is an infimum of
operator norms over the maps of bounded rank, and the transport is a
rank-preserving, norm-preserving bijection of those. -/
theorem approximationNumber_clm (T : E →L[𝕜] F) (n : ℕ) :
    (clm (e := e) T).approximationNumber n = T.approximationNumber n := by
  rw [ContinuousLinearMap.approximationNumber_eq_iInf,
    ContinuousLinearMap.approximationNumber_eq_iInf]
  refine (Equiv.iInf_congr (Equiv.subtypeEquiv (clmEquiv (e := e)) fun R => ?_) fun R => ?_).symm
  · rw [show ((clmEquiv (e := e)) R : ScalarTransport e E →L[𝕂] ScalarTransport e F) =
      clm (e := e) R from rfl, rank_clm_eq]
  · rw [Equiv.subtypeEquiv_apply]
    exact (clm_norm (e := e) (T - (R : E →L[𝕜] F))).symm

/-- Linear independence is unchanged: the two scalar actions differ by `e`. -/
theorem linearIndependent_of_iff {ι : Type*} (v : ι → E) :
    LinearIndependent 𝕂 (fun i => of (e := e) (v i)) ↔ LinearIndependent 𝕜 v := by
  classical
  constructor
  · intro h
    refine linearIndependent_iff'.mpr fun s g hg i hi => ?_
    have := linearIndependent_iff'.mp h s (fun j => e (g j)) ?_ i hi
    · simpa using congrArg e.toRingEquiv.symm this
    · have : ∀ j, e (g j) • of (e := e) (v j) = of (e := e) (g j • v j) := by
        intro j
        rw [smul_def, e.toRingEquiv.symm_apply_apply]
        rfl
      simp only [this]
      exact congrArg (of (e := e)) hg
  · intro h
    refine linearIndependent_iff'.mpr fun s g hg i hi => ?_
    have hgs : ∀ j, g j • of (e := e) (v j) =
        of (e := e) ((e.toRingEquiv.symm (g j)) • v j) := fun j => rfl
    have := linearIndependent_iff'.mp h s (fun j => e.toRingEquiv.symm (g j)) ?_ i hi
    · simpa using congrArg e.toRingEquiv this
    · simp only [hgs] at hg
      exact hg

/-- Spans are unchanged: the transported span has the original carrier. -/
theorem span_of {ι : Type*} (v : ι → E) :
    Submodule.span 𝕂 (Set.range fun i => of (e := e) (v i)) =
      submodule (e := e) (Submodule.span 𝕜 (Set.range v)) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact mem_submodule.mpr (Submodule.subset_span ⟨i, rfl⟩)
  · have key : ∀ y : E, y ∈ Submodule.span 𝕜 (Set.range v) →
        of (e := e) y ∈ Submodule.span 𝕂 (Set.range fun i => of (e := e) (v i)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
          have hc : of (e := e) (c • a) = e c • of (e := e) a := by
            rw [smul_def, e.toRingEquiv.symm_apply_apply]; rfl
          exact hc ▸ Submodule.smul_mem _ _ ha
    exact fun x hx => key (out x) hx

end ScalarTransport

end TauCeti
