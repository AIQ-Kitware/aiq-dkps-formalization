/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Algebra.Star.Unitary

/-!
# Intertwiners of spectrally separated operators

An `X` intertwining two partial maps intertwines everything built from them:
first their resolvents, and from there their spectral projections, so that
disjoint spectra force `X = 0`.

This is Spectra-removal lane **SR-E**
(`dev/tauceti/spectra-removal-parallel-lanes.md`), replacing the donor constant
`generatorIntertwiner_eq_zero_of_disjoint_spectrum`.

## Status

This module carries the intertwining chain up to and including the **continuous**
functional calculus:

1. `resolvent_intertwines` — needs nothing beyond the definition of `resolventSet`;
2. `cayley_intertwines` — immediate at `z = -i`;
3. `cfcHom_intertwines` / `cfcHom_cayley_intertwines` — Stone--Weierstrass.

What remains is the **Borel** step: upgrading `cfcHom_cayley_intertwines` to
`BorelCalculus.borelCalculus`, and from there to `specProjection`.  That is a
monotone-class argument on the sesquilinear `pair` form defining
`borelCalculus`, i.e. it must be run through the diagonal measures rather than
the operators.  It is the one genuinely open piece and is written up in the lane
document.

Once `specProjection` intertwining exists the endgame is short: for disjoint
closed spectra pick a Borel `B ⊇ σ(A)` missing `σ(B)`, and
`X = E_A(B) X = X E_B(B) = 0` by lane SR-B's
`specProjection_eq_zero_of_subset_resolventSet`.

## Provenance

* Replaces `vendor/Spectra/Spectra/SpectralTheory/SeparatedIntertwiner.lean`.
  Proved natively rather than relocated: the donor's route runs through
  `borelMeasure` and the Born-rule support estimate, spanning 44 Spectra files,
  none of which `ForTauCeti` may import.
* Spectra influence: none.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **An intertwiner intertwines the resolvents.**

If `X` carries `B` to `A` — `A (X y) = X (B y)` on `dom B` — and `z` is a
resolvent point of both, then `X R_B = R_A X`.

Only the two defining properties of a resolvent are used: that `R_A` inverts
`A - z` on the domain, and that `R_B` lands in `dom B` and inverts `B - z`
there.  Neither self-adjointness nor closedness is needed. -/
theorem resolvent_intertwines
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {X : F →L[𝕜] E} {z : 𝕜}
    {RA : E →L[𝕜] E} {RB : F →L[𝕜] F}
    (hRA : ∀ ψ : A.domain, RA (A ψ - z • (ψ : E)) = (ψ : E))
    (hRB : ∀ φ : F, ∃ h : RB φ ∈ B.domain, B ⟨RB φ, h⟩ - z • RB φ = φ)
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y)) :
    X ∘L RB = RA ∘L X := by
  refine ContinuousLinearMap.ext fun φ => ?_
  obtain ⟨hmem, hBinv⟩ := hRB φ
  -- Push `X` through `B ⟨RB φ⟩ - z • RB φ = φ` and rewrite with the
  -- intertwining relation, turning it into a statement about `A`.
  have hXpush : A ⟨X (RB φ), hmaps ⟨RB φ, hmem⟩⟩ - z • X (RB φ) = X φ := by
    have := congrArg X hBinv
    rw [map_sub, map_smul] at this
    rw [hint ⟨RB φ, hmem⟩]
    exact this
  -- `RA` inverts `A - z` at that domain vector, which is exactly the claim.
  have := hRA ⟨X (RB φ), hmaps ⟨RB φ, hmem⟩⟩
  rw [hXpush] at this
  simpa using this.symm

/-- `resolvent`-specialised form of `resolvent_intertwines`. -/
theorem resolvent_intertwines' {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X : F →L[𝕜] E} {z : 𝕜}
    (hzA : z ∈ resolventSet A) (hzB : z ∈ resolventSet B)
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y)) :
    X ∘L resolvent B hzB = resolvent A hzA ∘L X :=
  resolvent_intertwines (fun ψ => resolvent_apply_sub_smul hzA ψ)
    (fun φ => ⟨resolvent_mem_domain hzB φ, sub_smul_resolvent hzB φ⟩) hmaps hint

section Complex

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **An intertwiner intertwines the Cayley transforms.**

Immediate from `resolvent_intertwines'` at `z = -i`, since
`cayley hA = 1 - 2i • R_A(-i)`.  This is the step that carries the intertwining
into the bounded world, where the Borel calculus lives. -/
theorem cayley_intertwines {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {X : F →L[ℂ] E}
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y)) :
    X ∘L cayley hB = cayley hA ∘L X := by
  have hres := resolvent_intertwines' (A := A) (B := B) (X := X)
    (negI_mem_resolventSet hA) (negI_mem_resolventSet hB) hmaps hint
  refine ContinuousLinearMap.ext fun φ => ?_
  have hr := congrArg (fun T : F →L[ℂ] E => T φ) hres
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at hr
  simp only [cayley, ContinuousLinearMap.coe_comp, Function.comp_apply,
    sub_apply, one_apply_eq_self, smul_apply, map_sub, map_smul, hr]

/-- Restriction of a symbol along an inclusion of compact sets, as a star algebra
homomorphism.  Bundling it this way is what lets the induction below move `+`,
`*` and `star` across the restriction for free. -/
noncomputable def symbolRestrict {K s : Set ℂ} (h : s ⊆ K) :
    C(K, ℂ) →⋆ₐ[ℂ] C(s, ℂ) :=
  ContinuousMap.compStarAlgHom' ℂ ℂ ⟨Set.inclusion h, continuous_inclusion h⟩

theorem continuous_symbolRestrict {K s : Set ℂ} (h : s ⊆ K) :
    Continuous (symbolRestrict h) :=
  ContinuousMap.continuous_precomp _

/-- **An intertwiner intertwines the continuous functional calculi.**

If `X v = u X` and `X v⋆ = u⋆ X` for star-normal `u`, `v`, then `X` intertwines
`g u` and `g v` for every continuous symbol `g`.

The symbol is taken on a *common* compact `K` containing both spectra and
restricted to each: `cfcHom hu` and `cfcHom hv` eat functions on `_root_.spectrum ℂ u`
and `_root_.spectrum ℂ v` respectively, which are different spaces, so there is no
common domain on which to state the conclusion otherwise.

The proof is Stone--Weierstrass, via `ContinuousMap.induction_on_of_compact`:
the claim holds for constants and for `id`/`star id` (the two hypotheses), is
preserved by `+` and `*`, and defines a closed set of symbols. -/
theorem cfcHom_intertwines
    {u : E →L[ℂ] E} {v : F →L[ℂ] F} (hu : IsStarNormal u) (hv : IsStarNormal v)
    {X : F →L[ℂ] E}
    (hint : X ∘L v = u ∘L X) (hstar : X ∘L star v = star u ∘L X)
    {K : Set ℂ} (hK : IsCompact K)
    (huK : _root_.spectrum ℂ u ⊆ K) (hvK : _root_.spectrum ℂ v ⊆ K) (g : C(K, ℂ)) :
    X ∘L cfcHom hv (symbolRestrict hvK g)
      = cfcHom hu (symbolRestrict huK g) ∘L X := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  induction g using ContinuousMap.induction_on_of_compact with
  | const r =>
      have h1 : symbolRestrict hvK (ContinuousMap.const K r)
          = algebraMap ℂ (C(_root_.spectrum ℂ v, ℂ)) r := rfl
      have h2 : symbolRestrict huK (ContinuousMap.const K r)
          = algebraMap ℂ (C(_root_.spectrum ℂ u, ℂ)) r := rfl
      rw [h1, h2, AlgHomClass.commutes, AlgHomClass.commutes]
      ext y
      simp [Algebra.algebraMap_eq_smul_one]
  | id =>
      have h1 : symbolRestrict hvK (ContinuousMap.restrict K (ContinuousMap.id ℂ))
          = ContinuousMap.restrict _ (ContinuousMap.id ℂ) := rfl
      have h2 : symbolRestrict huK (ContinuousMap.restrict K (ContinuousMap.id ℂ))
          = ContinuousMap.restrict _ (ContinuousMap.id ℂ) := rfl
      rw [h1, h2, cfcHom_id, cfcHom_id]
      exact hint
  | star_id =>
      have h1 : symbolRestrict hvK (star (ContinuousMap.restrict K (ContinuousMap.id ℂ)))
          = star (ContinuousMap.restrict _ (ContinuousMap.id ℂ)) := rfl
      have h2 : symbolRestrict huK (star (ContinuousMap.restrict K (ContinuousMap.id ℂ)))
          = star (ContinuousMap.restrict _ (ContinuousMap.id ℂ)) := rfl
      rw [h1, h2, map_star, map_star, cfcHom_id, cfcHom_id]
      exact hstar
  | add f g hf hg =>
      rw [map_add, map_add, map_add, map_add, ContinuousLinearMap.comp_add,
        ContinuousLinearMap.add_comp, hf, hg]
  | mul f g hf hg =>
      rw [map_mul, map_mul, map_mul, map_mul]
      ext y
      exact (congrArg (fun T : F →L[ℂ] E => T (cfcHom hv (symbolRestrict hvK g) y)) hf
        |>.trans (congrArg
          (fun T : F →L[ℂ] E => cfcHom hu (symbolRestrict huK f) (T y)) hg))
  | frequently f hf =>
      have hc1 : Continuous
          (fun g : C(K, ℂ) => X ∘L cfcHom hv (symbolRestrict hvK g)) :=
        (ContinuousLinearMap.compL ℂ F F E X).continuous.comp
          ((cfcHom_continuous hv).comp (continuous_symbolRestrict hvK))
      have hc2 : Continuous
          (fun g : C(K, ℂ) => cfcHom hu (symbolRestrict huK g) ∘L X) :=
        ((ContinuousLinearMap.compL ℂ F E E).flip X).continuous.comp
          ((cfcHom_continuous hu).comp (continuous_symbolRestrict huK))
      rw [← Set.mem_setOf (p := fun g : C(K, ℂ) =>
          X ∘L cfcHom hv (symbolRestrict hvK g)
            = cfcHom hu (symbolRestrict huK g) ∘L X),
        ← (isClosed_eq hc1 hc2).closure_eq]
      exact mem_closure_of_frequently_of_tendsto hf Filter.tendsto_id

/-- For unitaries, intertwining the operators already intertwines their adjoints:
`star v = v⁻¹` and `star u = u⁻¹`, so `X v = u X` inverts to `X v⋆ = u⋆ X`. -/
theorem star_intertwines_of_mem_unitary
    {u : E →L[ℂ] E} {v : F →L[ℂ] F}
    (hu : u ∈ unitary (E →L[ℂ] E)) (hv : v ∈ unitary (F →L[ℂ] F))
    {X : F →L[ℂ] E} (hint : X ∘L v = u ∘L X) :
    X ∘L star v = star u ∘L X := by
  -- `X` lives between two different spaces, so this is composition, not ring
  -- multiplication; the unitary relations are transported to `∘L` first.
  have hv1 : v ∘L star v = 1 := by
    simpa [ContinuousLinearMap.mul_def] using Unitary.mul_star_self_of_mem hv
  have hu1 : star u ∘L u = 1 := by
    simpa [ContinuousLinearMap.mul_def] using Unitary.star_mul_self_of_mem hu
  have key : u ∘L (X ∘L star v) = X := by
    rw [← ContinuousLinearMap.comp_assoc, ← hint, ContinuousLinearMap.comp_assoc,
      hv1]
    simp [ContinuousLinearMap.one_def]
  calc X ∘L star v = star u ∘L (u ∘L (X ∘L star v)) := by
        rw [← ContinuousLinearMap.comp_assoc, hu1, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp]
    _ = star u ∘L X := by rw [key]

/-- **An intertwiner intertwines the continuous functional calculi of the Cayley
transforms.**

This is `cfcHom_intertwines` with every hypothesis discharged: the Cayley
transforms are unitary (hence star-normal, and the `star` hypothesis is
automatic), their spectra are compact, and `cayley_intertwines` supplies the
intertwining relation itself. -/
theorem cfcHom_cayley_intertwines {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {X : F →L[ℂ] E}
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y))
    {K : Set ℂ} (hK : IsCompact K)
    (huK : _root_.spectrum ℂ (cayley hA) ⊆ K) (hvK : _root_.spectrum ℂ (cayley hB) ⊆ K)
    (g : C(K, ℂ)) :
    X ∘L cfcHom (isStarNormal_cayley hB) (symbolRestrict hvK g)
      = cfcHom (isStarNormal_cayley hA) (symbolRestrict huK g) ∘L X :=
  cfcHom_intertwines _ _ (cayley_intertwines hA hB hmaps hint)
    (star_intertwines_of_mem_unitary (cayley_mem_unitary hA) (cayley_mem_unitary hB)
      (cayley_intertwines hA hB hmaps hint)) hK huK hvK g

end Complex

end LinearPMap
end TauCeti
