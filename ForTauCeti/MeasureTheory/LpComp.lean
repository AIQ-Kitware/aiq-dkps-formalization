/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.MeasureTheory.RadonNikodymL2

/-!
# Composing `L²` classes with a measure-preserving map

For a measure-preserving `f : α → β` the map `F ↦ F ∘ f` is a linear isometry
`L²(ν) →ₗᵢ[ℂ] L²(μ)`, and it **commutes with multiplication operators**: the symbol `G` on the
target becomes the symbol `G ∘ f` on the source.  When `f` has a measure-preserving
almost-everywhere inverse the isometry is a unitary.

Mathlib supplies the underlying additive map as `MeasureTheory.Lp.compMeasurePreserving`
together with `MeasureTheory.Lp.norm_compMeasurePreserving`; what is added here is the
`ℂ`-linear isometry packaging, the two-sided-inverse criterion, and the intertwining law with
`TauCeti.mulLp`.

## Why this is the shape spectral multiplicity theory needs

A multiplication model is a *measure* together with the coordinate symbol, so the two ways a
model can be changed without changing the operator are: replacing the measure by an equivalent
one (`ForTauCeti/MeasureTheory/RadonNikodymL2.lean`), and **relabelling the underlying space by
a measurable map that fixes the symbol**.  The second is this file.  Together they are exactly
the moves used to bring a direct sum of multiplication models into multiplicity normal form:
the relabelling permutes the fibres of the index coordinate and leaves the spectral coordinate
alone, so `G ∘ f = G` and the intertwining law becomes a plain commutation.

## Main results

* `TauCeti.compLp`: the linear isometry `L²(ν) →ₗᵢ[ℂ] L²(μ)`.
* `TauCeti.compLpEquiv`: the unitary, from a two-sided almost-everywhere inverse.
* `TauCeti.compLp_mulLp`: **the intertwining law**.
* `TauCeti.mulLp_congr_ae`: the multiplication operator only depends on the symbol almost
  everywhere -- needed because two models may present the same operator with symbols truncated
  at different bounds.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
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
    mulLp ρ hg hgC = mulLp ρ hg' hgC' := by
  refine ContinuousLinearMap.ext fun F => Lp.ext ?_
  filter_upwards [coeFn_mulLp ρ hg hgC F, coeFn_mulLp ρ hg' hgC' F, h] with x h1 h2 h3
  rw [h1, h2, h3]

end Congr

section Comp

/-- **Composition with a measure-preserving map, as a linear isometry** `L²(ν) →ₗᵢ[ℂ] L²(μ)`.

Mathlib's `MeasureTheory.Lp.compMeasurePreserving` is an `AddMonoidHom`; this adds
`ℂ`-homogeneity and the norm identity. -/
noncomputable def compLp (f : α → β) (hf : MeasurePreserving f μ ν) :
    Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := Lp.compMeasurePreserving f hf
  map_add' F G := map_add (Lp.compMeasurePreserving (E := ℂ) (p := 2) f hf) F G
  map_smul' c F := by
    simp only [RingHom.id_apply]
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • F) hf,
      Lp.coeFn_smul c (Lp.compMeasurePreserving (E := ℂ) (p := 2) f hf F),
      Lp.coeFn_compMeasurePreserving F hf,
      hf.quasiMeasurePreserving.ae (Lp.coeFn_smul c F)] with x h1 h2 h3 h4
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 ⊢
    rw [h1, h2, h3]
    exact h4
  norm_map' F := Lp.norm_compMeasurePreserving F hf

/-- The composition isometry, on representatives. -/
theorem coeFn_compLp (hf : MeasurePreserving f μ ν) (F : Lp ℂ 2 ν) :
    (compLp f hf F : α → ℂ) =ᵐ[μ] fun x => F (f x) :=
  Lp.coeFn_compMeasurePreserving F hf

/-- **Composition with an almost-everywhere two-sided inverse undoes the composition.** -/
theorem compLp_compLp {g : β → α} (hf : MeasurePreserving f μ ν) (hg : MeasurePreserving g ν μ)
    (hgf : ∀ᵐ y ∂ν, f (g y) = y) (F : Lp ℂ 2 ν) :
    compLp g hg (compLp f hf F) = F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_compLp hg (compLp f hf F),
    hg.quasiMeasurePreserving.ae (coeFn_compLp hf F), hgf] with y h1 h2 h3
  rw [h1, h2, h3]

/-- **The composition unitary.**  A measurable map with a measure-preserving almost-everywhere
two-sided inverse induces a unitary of the `L²` spaces.

Neither map need be injective: what is required is only that the two composites agree with the
identity almost everywhere, which is what an essentially bijective relabelling supplies. -/
@[expose]
noncomputable def compLpEquiv (f : α → β) (g : β → α) (hf : MeasurePreserving f μ ν)
    (hg : MeasurePreserving g ν μ) (hfg : ∀ᵐ x ∂μ, g (f x) = x) (hgf : ∀ᵐ y ∂ν, f (g y) = y) :
    Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := compLp f hf
  invFun := compLp g hg
  left_inv F := compLp_compLp hf hg hgf F
  right_inv G := compLp_compLp hg hf hfg G
  map_add' := (compLp f hf).map_add
  map_smul' := (compLp f hf).map_smul
  norm_map' := (compLp f hf).norm_map

@[simp]
theorem compLpEquiv_apply (f : α → β) (g : β → α) (hf : MeasurePreserving f μ ν)
    (hg : MeasurePreserving g ν μ) (hfg : ∀ᵐ x ∂μ, g (f x) = x) (hgf : ∀ᵐ y ∂ν, f (g y) = y)
    (F : Lp ℂ 2 ν) : compLpEquiv f g hf hg hfg hgf F = compLp f hf F := rfl

/-- **The intertwining law.**  Composition with `f` carries multiplication by `G` on `L²(ν)` to
multiplication by `G ∘ f` on `L²(μ)`.

When `f` fixes the coordinate the symbol is unchanged -- `G ∘ f = G` -- and the law becomes the
statement that the unitary commutes with the multiplication operator. -/
theorem compLp_mulLp (hf : MeasurePreserving f μ ν) {G : β → ℂ} (hG : Measurable G) {C : ℝ}
    (hGC : ∀ y, ‖G y‖ ≤ C) (F : Lp ℂ 2 ν) :
    compLp f hf (mulLp ν hG hGC F)
      = mulLp μ (hG.comp hf.measurable) (fun x => hGC (f x)) (compLp f hf F) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_compLp hf (mulLp ν hG hGC F),
    hf.quasiMeasurePreserving.ae (coeFn_mulLp ν hG hGC F),
    coeFn_mulLp μ (hG.comp hf.measurable) (fun x => hGC (f x)) (compLp f hf F),
    coeFn_compLp hf F] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4]

end Comp

end TauCeti
