/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.MeasureTheory.RadonNikodymL2
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.Equiv

/-!
# Composing `L²` classes with a measure-preserving map

For a measure-preserving `f : α → β` the map `F ↦ F ∘ f` is a linear isometry
`L²(ν) →ₗᵢ[ℂ] L²(μ)`, and it **commutes with multiplication operators**: the symbol `G` on the
target becomes the symbol `G ∘ f` on the source.  When `f` has a measure-preserving
almost-everywhere inverse the isometry is a unitary.

Mathlib supplies the pullback isometry. The measurable-embedding construction
uses TauCeti’s range characterization, and the multiplication and conjugation
intertwiners follow from the almost-everywhere representative formulas.

## Why this is the shape spectral multiplicity theory needs

A multiplication model is a *measure* together with the coordinate symbol, so the two ways a
model can be changed without changing the operator are: replacing the measure by an equivalent
one (`ForTauCeti/MeasureTheory/RadonNikodymL2.lean`), and **relabelling the underlying space by
a measurable map that fixes the symbol**.  The second is this file.  Together they are exactly
the moves used to bring a direct sum of multiplication models into multiplicity normal form:
the relabelling permutes the fibres of the index coordinate and leaves the spectral coordinate
alone, so `G ∘ f = G` and the intertwining law becomes a plain commutation.

## Main results

* `TauCeti.compLp_mulLp`: **the intertwining law**.
* `TauCeti.mulLp_congr_ae`: the multiplication operator only depends on the symbol almost
  everywhere -- needed because two models may present the same operator with symbols truncated
  at different bounds.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none**.
-/

public section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {f : α → β}

section Congr

/-- **The multiplication operator depends on its symbol only almost everywhere.**

Two symbols that agree `ρ`-almost everywhere -- for instance the same function truncated at two
different bounds, both larger than the essential supremum -- define the same bounded operator on
`L²(ρ)`. -/
theorem mulLp_congr_ae (ρ : Measure α) {g g' : α → ℂ} (hg : Measurable g) (hg' : Measurable g')
    {C C' : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (hgC' : ∀ x, ‖g' x‖ ≤ C') (h : g =ᵐ[ρ] g') :
    Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ hg hgC) =
      Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ hg' hgC') := by
  have hclass : boundedSymbolLp ρ hg hgC = boundedSymbolLp ρ hg' hgC' :=
    Lp.ext ((coeFn_boundedSymbolLp ρ hg hgC).trans
      (h.trans (coeFn_boundedSymbolLp ρ hg' hgC').symm))
  rw [hclass]

end Congr

section Comp

/-- The pullback along a measurable embedding is surjective for its pushforward measure. -/
theorem surjective_compLp_of_measurableEmbedding {e : α → β} (he : MeasurableEmbedding e)
    (ρ : Measure α) :
    Function.Surjective (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ e
      (he.measurable.measurePreserving ρ)) := by
  intro F
  have hF : AEStronglyMeasurable[MeasurableSpace.comap e inferInstance] F ρ := by
    rw [he.comap_eq]
    exact Lp.aestronglyMeasurable F
  exact (Lp.mem_range_compMeasurePreservingₗᵢ_iff ℂ (he.measurable.measurePreserving ρ) F).2 hF

/-- **Transport along a measurable embedding.**  For a measurable embedding `e`, composition with
`e` is a unitary `L²(map e ρ) ≃ₗᵢ[ℂ] L²(ρ)`.

The measurable embedding identifies the source measurable space with the comap of the target
space, so every source class satisfies the native pullback range criterion. This unitary moves
the scalar spectral measures off the
`spectrum` subtype and onto `ℂ`, where the models of two different operators can be compared. -/
@[expose]
noncomputable def embLpEquiv {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α) :
    Lp ℂ 2 (Measure.map e ρ) ≃ₗᵢ[ℂ] Lp ℂ 2 ρ :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ e (he.measurable.measurePreserving ρ))
    (surjective_compLp_of_measurableEmbedding he ρ)

/-- The pushforward unitary acts by the native pullback along the embedding. -/
@[simp]
theorem embLpEquiv_apply {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    (F : Lp ℂ 2 (Measure.map e ρ)) :
    embLpEquiv he ρ F = Lp.compMeasurePreservingₗᵢ ℂ e (he.measurable.measurePreserving ρ) F :=
  rfl

/-- **The intertwining law.**  Composition with `f` carries multiplication by `G` on `L²(ν)` to
multiplication by `G ∘ f` on `L²(μ)`.

When `f` fixes the coordinate the symbol is unchanged -- `G ∘ f = G` -- and the law becomes the
statement that the unitary commutes with the multiplication operator. -/
theorem compLp_mulLp (hf : MeasurePreserving f μ ν) {G : β → ℂ} (hG : Measurable G) {C : ℝ}
    (hGC : ∀ y, ‖G y‖ ≤ C) (F : Lp ℂ 2 ν) :
    Lp.compMeasurePreservingₗᵢ ℂ f hf (Lp.multiplicationOperator (boundedSymbolLp ν hG hGC) F)
      = Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp μ (hG.comp hf.measurable) (fun
        x => hGC (f x))) (Lp.compMeasurePreservingₗᵢ ℂ f hf F) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (Lp.multiplicationOperator (boundedSymbolLp ν hG hGC) F) hf,
    hf.quasiMeasurePreserving.ae (coeFn_mulLp ν hG hGC F),
    coeFn_mulLp μ (hG.comp hf.measurable) (fun x => hGC (f x))
      (Lp.compMeasurePreservingₗᵢ ℂ f hf F),
    Lp.coeFn_compMeasurePreserving F hf] with x h1 h2 h3 h4
  simp only [← Lp.compMeasurePreservingₗᵢ_apply ℂ hf, Function.comp_apply] at h1 h3 h4
  rw [h1, h2, h3, h4]

/-- **The pushforward unitary intertwines the multiplication operators.**  The symbol on the
source is the symbol on the target composed with the embedding. -/
theorem embLpEquiv_mulLp {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α) {G : β → ℂ}
    (hG : Measurable G) {C : ℝ} (hGC : ∀ y, ‖G y‖ ≤ C) (F : Lp ℂ 2 (Measure.map e ρ)) :
    embLpEquiv he ρ (Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp (Measure.map e ρ)
      hG hGC) F)
      = Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ (hG.comp he.measurable) (fun
        x => hGC (e x))) (embLpEquiv he ρ F) :=
  compLp_mulLp (he.measurable.measurePreserving ρ) hG hGC F

/-- The inverse of the pushforward unitary intertwines the multiplication operators the other
way. -/
theorem embLpEquiv_symm_mulLp {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    {G : β → ℂ} (hG : Measurable G) {C : ℝ} (hGC : ∀ y, ‖G y‖ ≤ C) (F : Lp ℂ 2 ρ) :
    (embLpEquiv he ρ).symm (Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp ρ (hG.comp
      he.measurable) (fun x => hGC (e x))) F)
      = Lp.multiplicationOperator (E := ℂ) (p := 2) (boundedSymbolLp (Measure.map e ρ) hG hGC)
        ((embLpEquiv he ρ).symm F) := by
  refine (embLpEquiv he ρ).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, embLpEquiv_mulLp,
    LinearIsometryEquiv.apply_symm_apply]

end Comp

section Star

/-- **Relabelling is `star`-equivariant.**  Composition acts on the argument and `star` acts on
the value, so the two commute with nothing to prove beyond moving the representatives past each
other.

This is what carries the real (`star`-fixed) part of an `L²` space along the relabelling step of
the multiplicity model: `TauCeti.starFixedSubmodule` is a `star`-fixed set, so an equivariant
isometry maps it into the corresponding one. -/
theorem star_compLp (hf : MeasurePreserving f μ ν) (F : Lp ℂ 2 ν) :
    star (Lp.compMeasurePreservingₗᵢ ℂ f hf F) = Lp.compMeasurePreservingₗᵢ ℂ f hf (star F) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (Lp.compMeasurePreservingₗᵢ ℂ f hf F),
    Lp.coeFn_compMeasurePreserving F hf, Lp.coeFn_compMeasurePreserving (star F) hf,
    hf.quasiMeasurePreserving.ae (Lp.coeFn_star F)] with x h1 h2 h3 h4
  simp only [← Lp.compMeasurePreservingₗᵢ_apply ℂ hf, Function.comp_apply] at h2 h3
  calc ((star (Lp.compMeasurePreservingₗᵢ ℂ f hf F) : Lp ℂ 2 μ) : α → ℂ) x
      = star ((F : β → ℂ) (f x)) := by rw [h1, Pi.star_apply, h2]
    _ = ((star F : Lp ℂ 2 ν) : β → ℂ) (f x) := by rw [h4, Pi.star_apply]
    _ = ((Lp.compMeasurePreservingₗᵢ ℂ f hf (star F) : Lp ℂ 2 μ) : α → ℂ) x := h3.symm

/-- **The pushforward unitary is `star`-equivariant.** -/
theorem star_embLpEquiv {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    (F : Lp ℂ 2 (Measure.map e ρ)) :
    star (embLpEquiv he ρ F) = embLpEquiv he ρ (star F) :=
  star_compLp (he.measurable.measurePreserving ρ) F

/-- **The inverse of the pushforward unitary is `star`-equivariant**, which follows from
`star_embLpEquiv` by applying the unitary to both sides. -/
theorem star_embLpEquiv_symm {e : α → β} (he : MeasurableEmbedding e) (ρ : Measure α)
    (F : Lp ℂ 2 ρ) :
    star ((embLpEquiv he ρ).symm F) = (embLpEquiv he ρ).symm (star F) := by
  refine (embLpEquiv he ρ).injective ?_
  rw [LinearIsometryEquiv.apply_symm_apply, ← star_embLpEquiv,
    LinearIsometryEquiv.apply_symm_apply]

end Star

end TauCeti
