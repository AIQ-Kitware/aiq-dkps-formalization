/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
Adapted from: Spectra (https://github.com/adambornemann-glitch/Spectra),
  `Spectra/Operator/KatoRellich.lean` and `Spectra/Operator/Bounded.lean` at
  commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`, Copyright (c) 2026 Spectra
  Formalization Project, Apache 2.0.  See `## Provenance` below.
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Two elementary constructions on partial linear maps

* `TauCeti.LinearPMap.perturb A V`: add a map defined on `dom A` to `A`, keeping
  the domain.  This is the domain-preserving perturbation that Kato--Rellich
  arguments start from, before any relative-boundedness hypothesis appears.
* `TauCeti.LinearPMap.isSelfAdjoint_toPMap_top`: a bounded self-adjoint operator,
  viewed as a partial map on all of `H`, is self-adjoint in the `LinearPMap`
  sense.

Neither has any spectral content; they are here so that the Davis--Kahan bridges
that used them do not need a spectral-theory dependency for bookkeeping.

## Provenance

* **Original repository:** Spectra, commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
* **Original declarations:** `Spectra.Operator.perturbedOp` (with
  `perturbedOp_domain`, `perturbedOp_apply`) in `Spectra/Operator/KatoRellich.lean`;
  the self-adjointness obligation inside `Spectra.Operator.SelfAdjointOperator.ofBounded`
  in `Spectra/Operator/Bounded.lean`.
* **Original authors / copyright / licence:** Copyright (c) 2026 Spectra
  Formalization Project, Apache 2.0.  Apache 2.0 §4(b): **modified** — see below.
  §4(c): notices retained here and in the file header.
* **Extraction class:** *adapted* for `perturb` (the definition is Spectra's,
  renamed); *generalized* for the self-adjointness lemma.
* **Semantic differences:**
  1. `perturb` is stated over `RCLike 𝕜`, not just `ℂ`, and drops the ambient
     `[CompleteSpace H]` that Spectra's section carried and its statement did
     not use.
  2. Spectra's `ofBounded` produces its bundled `SelfAdjointOperator` structure.
     Only the self-adjointness *fact* is ported, over the raw `LinearPMap`,
     because the DKPS `U1` migration is removing bundled closed-operator
     wrappers rather than adding one (`dev/tauceti/u1-linearpmap-migration.md`).
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Add a map defined on `dom A` to `A`, keeping the domain unchanged. -/
def perturb (A : H →ₗ.[𝕜] H) (V : A.domain →ₗ[𝕜] H) : H →ₗ.[𝕜] H where
  domain := A.domain
  toFun := A.toFun + V

@[simp] theorem perturb_domain (A : H →ₗ.[𝕜] H) (V : A.domain →ₗ[𝕜] H) :
    (perturb A V).domain = A.domain := rfl

@[simp] theorem perturb_apply (A : H →ₗ.[𝕜] H) (V : A.domain →ₗ[𝕜] H)
    (ψ : A.domain) : perturb A V ψ = A ψ + V ψ := rfl

section Bounded

variable [CompleteSpace H]

/-- A bounded self-adjoint operator is self-adjoint as a partial map on `⊤`. -/
theorem isSelfAdjoint_toPMap_top {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint ((T : H →ₗ[𝕜] H).toPMap ⊤) := by
  have hdense : Dense ((⊤ : Submodule 𝕜 H) : Set H) := by
    rw [Submodule.top_coe]; exact dense_univ
  have hTadj : ContinuousLinearMap.adjoint T = T :=
    (ContinuousLinearMap.star_eq_adjoint T).symm.trans hT
  rw [_root_.LinearPMap.isSelfAdjoint_def,
    ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense T hdense, hTadj]

/-- The everywhere-defined bounded perturbation of `A`, restricted to `dom A`. -/
def boundedPerturbation (A : H →ₗ.[𝕜] H) (T : H →L[𝕜] H) : A.domain →ₗ[𝕜] H :=
  (T.comp (Submodule.subtypeL A.domain)).toLinearMap

omit [CompleteSpace H] in
@[simp] theorem boundedPerturbation_apply (A : H →ₗ.[𝕜] H) (T : H →L[𝕜] H)
    (x : A.domain) : boundedPerturbation A T x = T (x : H) := rfl

/-- **Bounded Kato--Rellich.**  A bounded self-adjoint perturbation of a
self-adjoint partial map is self-adjoint, on the same domain.

Spectra obtains this as the `a = 0` corollary of the full Kato--Rellich theorem,
which needs relative bounds and von Neumann's criterion.  The bounded case does
not: because `T` is everywhere defined and continuous, `x ↦ ⟪y, T x⟫` is
automatically continuous, so `A + T` and `A` have *the same* adjoint domain, and
symmetry finishes it. -/
theorem isSelfAdjoint_perturb_bounded {A : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A)
    {T : H →L[𝕜] H} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (perturb A (boundedPerturbation A T)) := by
  set B := perturb A (boundedPerturbation A T) with hB
  have hdense : Dense (A.domain : Set H) := hA.dense_domain
  have hsymA : A.IsFormalAdjoint A := by
    have h := _root_.LinearPMap.adjoint_isFormalAdjoint (T := A) hdense
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at h
  have hTadj : ContinuousLinearMap.adjoint T = T :=
    (ContinuousLinearMap.star_eq_adjoint T).symm.trans hT
  have hTsym : ∀ u v : H, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜 := by
    intro u v
    rw [← ContinuousLinearMap.adjoint_inner_left, hTadj]
  -- `B` is symmetric
  have hsymB : B.IsFormalAdjoint B := by
    intro x y
    change ⟪A x + T (x : H), (y : H)⟫_𝕜 = ⟪(x : H), A y + T (y : H)⟫_𝕜
    rw [inner_add_left, inner_add_right, hsymA x y, hTsym (x : H) (y : H)]
  -- `T` contributes a continuous term, so `B` and `A` have the same adjoint domain
  have hsub : ∀ y : H, y ∈ (_root_.LinearPMap.adjoint B).domain → y ∈ A.domain := by
    intro y hy
    rw [_root_.LinearPMap.mem_adjoint_domain_iff] at hy
    have hTcont : Continuous fun x : A.domain => ⟪y, T (x : H)⟫_𝕜 :=
      ((innerSL 𝕜 y).comp (T.comp (Submodule.subtypeL A.domain))).continuous
    have hAcont : Continuous ((innerₛₗ 𝕜 y).comp A.toFun) := by
      have hsplit : (fun x : A.domain => ((innerₛₗ 𝕜 y).comp A.toFun) x)
          = fun x : A.domain =>
              ((innerₛₗ 𝕜 y).comp B.toFun) x - ⟪y, T (x : H)⟫_𝕜 := by
        funext x
        change ⟪y, A x⟫_𝕜 = ⟪y, A x + T (x : H)⟫_𝕜 - ⟪y, T (x : H)⟫_𝕜
        rw [inner_add_right]
        abel
      have hcont : Continuous fun x : A.domain => ((innerₛₗ 𝕜 y).comp A.toFun) x := by
        rw [hsplit]; exact hy.sub hTcont
      exact hcont
    have hmemA : y ∈ (_root_.LinearPMap.adjoint A).domain :=
      (_root_.LinearPMap.mem_adjoint_domain_iff (T := A) y).mpr hAcont
    rwa [_root_.LinearPMap.isSelfAdjoint_def.mp hA] at hmemA
  -- symmetry gives `B ≤ B†`; the domain inclusion above makes it an equality
  have hle : B ≤ _root_.LinearPMap.adjoint B :=
    _root_.LinearPMap.IsFormalAdjoint.le_adjoint (T := B) (S := B) hdense hsymB
  have hdomeq : B.domain = (_root_.LinearPMap.adjoint B).domain :=
    le_antisymm hle.1 (fun y hy => hsub y hy)
  rw [_root_.LinearPMap.isSelfAdjoint_def]
  exact (_root_.LinearPMap.eq_of_le_of_domain_eq hle hdomeq).symm

end Bounded

end LinearPMap
end TauCeti
