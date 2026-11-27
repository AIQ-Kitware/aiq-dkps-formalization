/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.MeasureTheory.LpComp
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero

/-!
# `L²` of a measure splits over a countable measurable partition

Extension by zero,

```text
F ↦ s.indicator F,
```

is a linear isometry `L²(μ|_s) →ₗᵢ[ℂ] L²(μ)` for every measurable `s`.  Over a countable
measurable partition of the space these isometries have pairwise orthogonal ranges spanning a
dense subspace, so

```text
L²(μ)  ≅  ⊕ₙ L²(μ|_{Bₙ})
```

as a Hilbert sum, and the isomorphism commutes with multiplication by any bounded measurable
symbol.

This is the one Hilbert-space step in the multiplicity construction.  Everything after it --
dominating a countable family of measures, passing to level sets, and rearranging the fibres --
is carried out on *measures*, where it is elementary, and transported back through this
decomposition together with the Radon--Nikodym unitary of
`ForTauCeti/MeasureTheory/RadonNikodymL2.lean` and the relabelling unitary of
`ForTauCeti/MeasureTheory/LpComp.lean`.

## Main results

* `TauCeti.inner_extendLp_eq_zero_of_disjoint`: orthogonality of the ranges over disjoint sets.
* `TauCeti.isHilbertSum_extendLp`: **the decomposition**, as a `MeasureTheory.IsHilbertSum`.
* `TauCeti.extendLp_mulLp`: extension by zero intertwines the multiplication operators.

The extension is TauCeti's extension by zero to `μ.restrict univ`,
followed by the native isometric cast to `μ`. To prove density, a vector
orthogonal to every extension range has zero restriction to each piece of
the partition and therefore vanishes almost everywhere.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none**.
-/

public section

open MeasureTheory

open scoped ENNReal InnerProductSpace

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}

-- Within the partition proofs, the ambient extension always uses the same two native maps.
local notation "extend₀[" μ ", " hs "]" => fun F =>
  castLpₗᵢ (𝕜 := ℂ) Measure.restrict_univ
    (extendByZeroLpₗᵢ ℂ μ (MeasurableSet.nullMeasurableSet hs) (Set.subset_univ _) F)

section Orthogonality

/-- **Extensions from disjoint sets are orthogonal.**  Their representatives have disjoint
supports, so the integrand of the inner product vanishes pointwise. -/
theorem inner_extendLp_eq_zero_of_disjoint (μ : Measure α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : Disjoint s t) (F : Lp ℂ 2 (μ.restrict s))
    (G : Lp ℂ 2 (μ.restrict t)) : ⟪extend₀[μ, hs] F, extend₀[μ, ht] G⟫_ℂ = 0 := by
  rw [L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [coeFn_castLpₗᵢ_extendByZeroLpₗᵢ ℂ hs.nullMeasurableSet F,
    coeFn_castLpₗᵢ_extendByZeroLpₗᵢ ℂ ht.nullMeasurableSet G] with x h1 h2
  rw [Pi.zero_apply, h1, h2]
  by_cases hxs : x ∈ s
  · have hxt : x ∉ t := Set.disjoint_left.mp hst hxs
    simp [hxt]
  · simp [hxs]

end Orthogonality

section Partition

variable {ι : Type*} [Countable ι] {B : ι → Set α}

/-- **`L²` of a measure is the Hilbert sum of the `L²` spaces of its restrictions to the pieces
of a countable measurable partition.**

The partition hypotheses are the weakest possible: the pieces are measurable and pairwise
disjoint, and what they miss is null. -/
theorem isHilbertSum_extendLp (μ : Measure α) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise fun i j => Disjoint (B i) (B j)) (hcover : μ (⋃ i, B i)ᶜ = 0) :
    IsHilbertSum ℂ (fun i => Lp ℂ 2 (μ.restrict (B i))) (fun i =>
      (castLpₗᵢ (𝕜 := ℂ) Measure.restrict_univ).toLinearIsometry.comp
        (extendByZeroLpₗᵢ ℂ μ (hB i).nullMeasurableSet (Set.subset_univ _))) := by
  refine IsHilbertSum.mk (𝕜 := ℂ) (fun i j hij F G => ?_) ?_
  · exact inner_extendLp_eq_zero_of_disjoint μ (hB i) (hB j) (hdisj hij) F G
  · refine (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
    rw [Submodule.eq_bot_iff]
    intro g hg
    have hgi : ∀ i, (g : α → ℂ) =ᵐ[μ.restrict (B i)] 0 := by
      intro i
      refine L2.ae_restrict_eq_zero_of_forall_inner_eq_zero (𝕜 := ℂ) (hB i) g fun φ hφ => ?_
      refine (Submodule.mem_orthogonal _ g).mp hg _ ?_
      exact le_iSup (fun i => LinearMap.range
        ((castLpₗᵢ (𝕜 := ℂ) Measure.restrict_univ).toLinearIsometry.comp
          (extendByZeroLpₗᵢ ℂ μ (hB i).nullMeasurableSet (Set.subset_univ _))).toLinearMap) i
        ⟨LpToLpRestrictCLM α ℂ ℂ μ 2 (B i) φ,
          castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM_of_ae_compl_eq_zero ℂ
            (hB i).nullMeasurableSet hφ⟩
    have hnull : ∀ i, μ (B i ∩ {x | (g : α → ℂ) x ≠ 0}) = 0 := by
      intro i
      have hi := hgi i
      rw [Filter.EventuallyEq, ae_iff, Measure.restrict_apply' (hB i), Set.inter_comm] at hi
      exact hi
    refine Lp.ext ?_
    refine (Filter.EventuallyEq.trans ?_ (Lp.coeFn_zero ℂ 2 μ).symm)
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null
      (show {x | ¬ (g : α → ℂ) x = (0 : α → ℂ) x}
        ⊆ (⋃ i, B i)ᶜ ∪ ⋃ i, B i ∩ {x | (g : α → ℂ) x ≠ 0} from fun x hx => ?_) ?_
    · by_cases hxU : x ∈ ⋃ i, B i
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi, by simpa using hx⟩)
      · exact Or.inl hxU
    · exact measure_union_null hcover (measure_iUnion_null hnull)

end Partition

section Multiplication

/-- **Extension by zero intertwines the multiplication operators.**  The symbol is the same
function on both sides; restricting it to `s` is what the restricted measure sees. -/
theorem extendLp_mulLp (μ : Measure α) (hs : MeasurableSet s) {g : α → ℂ} (hg : Measurable g)
    {C : ℝ} (hgC : ∀ x, ‖g x‖ ≤ C) (F : Lp ℂ 2 (μ.restrict s)) :
    extend₀[μ, hs] (Lp.multiplicationOperator (boundedSymbolLp (μ.restrict s) hg hgC) F) =
      Lp.multiplicationOperator (boundedSymbolLp μ hg hgC) (extend₀[μ, hs] F) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_castLpₗᵢ_extendByZeroLpₗᵢ ℂ hs.nullMeasurableSet
    (Lp.multiplicationOperator (boundedSymbolLp (μ.restrict s) hg hgC) F),
    (ae_eq_restrict_iff_indicator_ae_eq₀ hs.nullMeasurableSet).1
      (coeFn_mulLp (μ.restrict s) hg hgC F),
    coeFn_mulLp μ hg hgC (extend₀[μ, hs] F),
    coeFn_castLpₗᵢ_extendByZeroLpₗᵢ ℂ hs.nullMeasurableSet F] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  by_cases hxs : x ∈ s <;> simp [hxs]

end Multiplication

section Star

omit [MeasurableSpace α] in
/-- Pointwise conjugation passes through an indicator, because it fixes zero. -/
theorem star_indicator_apply (s : Set α) (u : α → ℂ) (x : α) :
    star (s.indicator u x) = s.indicator (star u) x := by
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxs, Pi.star_apply]
  · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem hxs, star_zero]

/-- **Extension by zero is `star`-equivariant.**  Conjugation fixes the zero that the extension
inserts, so it commutes with the indicator. -/
theorem star_extendLp (μ : Measure α) (hs : MeasurableSet s) (F : Lp ℂ 2 (μ.restrict s)) :
    star (extend₀[μ, hs] F) = extend₀[μ, hs] (star F) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (extend₀[μ, hs] F),
    coeFn_castLpₗᵢ_extendByZeroLpₗᵢ ℂ hs.nullMeasurableSet F,
    coeFn_castLpₗᵢ_extendByZeroLpₗᵢ ℂ hs.nullMeasurableSet (star F),
    (ae_eq_restrict_iff_indicator_ae_eq₀ hs.nullMeasurableSet).1 (Lp.coeFn_star F)]
    with x h1 h2 h3 h4
  calc ((star (extend₀[μ, hs] F) : Lp ℂ 2 μ) : α → ℂ) x
      = star (s.indicator (F : α → ℂ) x) := by rw [h1, Pi.star_apply, h2]
    _ = s.indicator (star (F : α → ℂ)) x := star_indicator_apply s _ x
    _ = s.indicator ((star F : Lp ℂ 2 (μ.restrict s)) : α → ℂ) x := (h4 ▸ rfl)
    _ = ((extend₀[μ, hs] (star F) : Lp ℂ 2 μ) : α → ℂ) x := h3.symm

/-- **Restriction is `star`-equivariant**: both sides are represented by the same function. -/
theorem star_restrictLp (μ : Measure α) (s : Set α) (g : Lp ℂ 2 μ) :
    star (LpToLpRestrictCLM α ℂ ℂ μ 2 s g) = LpToLpRestrictCLM α ℂ ℂ μ 2 s (star g) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (LpToLpRestrictCLM α ℂ ℂ μ 2 s g), LpToLpRestrictCLM_coeFn ℂ s g,
    LpToLpRestrictCLM_coeFn ℂ s (star g), ae_restrict_of_ae (Lp.coeFn_star g)] with x h1 h2 h3 h4
  calc ((star (LpToLpRestrictCLM α ℂ ℂ μ 2 s g) : Lp ℂ 2 (μ.restrict s)) : α → ℂ) x
      = star ((g : α → ℂ) x) := by rw [h1, Pi.star_apply, h2]
    _ = ((star g : Lp ℂ 2 μ) : α → ℂ) x := by rw [h4, Pi.star_apply]
    _ = ((LpToLpRestrictCLM α ℂ ℂ μ 2 s (star g) : Lp ℂ 2 (μ.restrict s)) : α → ℂ) x := h3.symm

end Star

end TauCeti
