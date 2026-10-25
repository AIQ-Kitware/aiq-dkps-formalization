/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.RingTheory.SimpleModule.Rank
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite-dimensional projection parameters as subspaces

Orthogonal projections correspond to their ranges, and the subspaces
split by dimension. A one-dimensional space has exactly the zero and
identity projections. These are algebraic equivalences; no manifold
topology is assigned to the rank strata here.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- An orthogonal projection on a finite-dimensional inner-product space
is specified uniquely by its range. -/
def starProjectionSubmoduleEquiv : {P : E →L[𝕜] E // IsStarProjection P} ≃ Submodule 𝕜 E where
  toFun P := P.val.range
  invFun M := ⟨M.starProjection, isStarProjection_starProjection⟩
  left_inv P := Subtype.ext
    (isStarProjection_iff_eq_starProjection_range.mp P.property).choose_spec.symm
  right_inv M := Submodule.range_starProjection M

/-- Subspaces of a finite-dimensional space are the disjoint union of
their dimension strata, with dimensions bounded by the ambient one. -/
def submoduleRankStratificationEquiv :
    Submodule 𝕜 E ≃
      Σ r : Fin (Module.finrank 𝕜 E + 1), {M : Submodule 𝕜 E // Module.finrank 𝕜 M = r.val} := by
  let rankIndex (M : Submodule 𝕜 E) : Fin (Module.finrank 𝕜 E + 1) :=
    ⟨Module.finrank 𝕜 M, Nat.lt_succ_of_le (Submodule.finrank_le M)⟩
  exact (Equiv.sigmaFiberEquiv rankIndex).symm.trans
    (Equiv.sigmaCongrRight fun _ => Equiv.subtypeEquivRight fun _ => Fin.ext_iff)

/-- Rank-stratified subspaces give all orthogonal projection parameters. -/
def starProjectionRankEquiv :
    {P : E →L[𝕜] E // IsStarProjection P} ≃
      Σ r : Fin (Module.finrank 𝕜 E + 1), {M : Submodule 𝕜 E // Module.finrank 𝕜 M = r.val} :=
  starProjectionSubmoduleEquiv.trans submoduleRankStratificationEquiv

/-- A one-dimensional inner-product space has exactly two orthogonal
projections, parametrized by a Boolean. -/
theorem exists_bool_equiv_starProjections_of_finrank_eq_one
    (hdim : Module.finrank 𝕜 E = 1) :
    ∃ e : Bool ≃ {P : E →L[𝕜] E // IsStarProjection P},
      (e false).val = 0 ∧ (e true).val = 1 := by
  classical
  let : IsSimpleModule 𝕜 E := isSimpleModule_iff_finrank_eq_one.mpr hdim
  let : Nontrivial E := IsSimpleModule.nontrivial 𝕜 E
  let f : Bool → {P : E →L[𝕜] E // IsStarProjection P} :=
    fun b => if b then ⟨1, IsStarProjection.one _⟩ else ⟨0, IsStarProjection.zero _⟩
  have hinj : Function.Injective f := by
    intro b b' heq
    cases b <;> cases b' <;> simp_all [f]
  have hsurj : Function.Surjective f := by
    intro P
    have hP : P.val = P.val.range.starProjection :=
      (isStarProjection_iff_eq_starProjection_range.mp P.property).choose_spec
    rcases eq_bot_or_eq_top P.val.range with hbot | htop
    · refine ⟨false, Subtype.ext ?_⟩
      change 0 = P.val
      calc
        0 = (⊥ : Submodule 𝕜 E).starProjection := by simp
        _ = P.val.range.starProjection :=
          (congrArg (fun M : Submodule 𝕜 E => M.starProjection) hbot).symm
        _ = P.val := hP.symm
    · refine ⟨true, Subtype.ext ?_⟩
      change 1 = P.val
      calc
        1 = (⊤ : Submodule 𝕜 E).starProjection := Submodule.starProjection_top'.symm
        _ = P.val.range.starProjection :=
          (congrArg (fun M : Submodule 𝕜 E => M.starProjection) htop).symm
        _ = P.val := hP.symm
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, rfl, rfl⟩

/-- There are exactly two orthogonal projections in dimension one. -/
theorem natCard_starProjections_of_finrank_eq_one
    (hdim : Module.finrank 𝕜 E = 1) :
    Nat.card {P : E →L[𝕜] E // IsStarProjection P} = 2 := by
  obtain ⟨e, _⟩ := exists_bool_equiv_starProjections_of_finrank_eq_one hdim
  rw [← Nat.card_congr e]
  simp [Nat.card_eq_fintype_card]

end TauCeti
