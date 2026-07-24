/-
# Gram rigidity (Mathlib candidate 01)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/

import Mathlib

/-!
## Comparator maintenance rule

The proof holes in this module are deliberate challenge placeholders. Do not
discharge them in this repository and do not count them as formalization debt.
Implementations belong in the project modules imported by the paired
`Leaderboard.lean`; Comparator verifies that those implementations match these
statements and use only the permitted kernel dependencies.
-/


open scoped InnerProductSpace
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Module (finrank)
open _root_.Matrix

namespace TauCeti
open scoped InnerProductSpace

section
variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The inner product of two finite linear combinations, expanded over the family's
Gram data. -/
theorem inner_linearCombination_linearCombination (v : ι → E) (a b : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 v a, Finsupp.linearCombination 𝕜 v b⟫_𝕜
      = a.sum fun i s => b.sum fun j t => starRingEnd 𝕜 s * t * ⟪v i, v j⟫_𝕜 := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]

end

section
variable {E R' : Type*} [SeminormedAddCommGroup E] [Ring R'] [Module R' E]
  {p q : Submodule R' E}

@[simp]
theorem LinearIsometryEquiv.ofEq_apply_mk (h : p = q) (x : E) (hx : x ∈ p) :
    LinearIsometryEquiv.ofEq p q h ⟨x, hx⟩ = ⟨x, h ▸ hx⟩ :=
  rfl

end

section GramSupport
variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace LinearMap

variable {M : Type*} [AddCommGroup M] [Module 𝕜 M]
variable (S : M →ₗ[𝕜] E) (T : M →ₗ[𝕜] F) (h : ∀ x y, ⟪S x, S y⟫_𝕜 = ⟪T x, T y⟫_𝕜)
include h

/-- Linear maps with equal pullback inner products have equal kernels. -/
theorem ker_eq_ker_of_inner_eq : LinearMap.ker S = LinearMap.ker T := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← inner_self_eq_zero (𝕜 := 𝕜), h x x,
    inner_self_eq_zero]

/-- **Isometric first isomorphism theorem.** -/
noncomputable def rangeEquivOfInnerEq : LinearMap.range S ≃ₗᵢ[𝕜] LinearMap.range T :=
  (S.quotKerEquivRange.symm.trans <| (Submodule.quotEquivOfEq _ _
      (ker_eq_ker_of_inner_eq S T h)).trans T.quotKerEquivRange).isometryOfInner fun x y => by
    obtain ⟨-, x, rfl⟩ := x
    obtain ⟨-, y, rfl⟩ := y
    simp [h x y]

@[simp]
theorem rangeEquivOfInnerEq_apply (x : M) (hx : S x ∈ LinearMap.range S) :
    (rangeEquivOfInnerEq S T h ⟨S x, hx⟩ : F) = T x := by
  simp [rangeEquivOfInnerEq]

end LinearMap

section
variable {φ : ι → E} {ψ : ι → F} (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜)
include h

/-- Families with equal pairwise inner products have linear-combination maps with equal
pullback inner products. -/
theorem inner_linearCombination_eq_of_inner_eq (c c' : ι →₀ 𝕜) :
    ⟪Finsupp.linearCombination 𝕜 φ c, Finsupp.linearCombination 𝕜 φ c'⟫_𝕜
      = ⟪Finsupp.linearCombination 𝕜 ψ c, Finsupp.linearCombination 𝕜 ψ c'⟫_𝕜 := by
  simp [inner_linearCombination_linearCombination, h]

/-- Families with equal pairwise inner products have linear-combination maps with equal
kernels. -/
theorem ker_linearCombination_eq_of_inner_eq :
    LinearMap.ker (Finsupp.linearCombination 𝕜 φ)
      = LinearMap.ker (Finsupp.linearCombination 𝕜 ψ) :=
  LinearMap.ker_eq_ker_of_inner_eq _ _ (inner_linearCombination_eq_of_inner_eq h)

variable (φ ψ)

/-- A linear isometry equivalence `span 𝕜 (range φ) ≃ₗᵢ span 𝕜 (range ψ)` sending each
`φ i` to `ψ i`. -/
noncomputable def linearIsometryEquivSpanOfInnerEq :
    (Submodule.span 𝕜 (Set.range φ)) ≃ₗᵢ[𝕜] (Submodule.span 𝕜 (Set.range ψ)) :=
  (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜).symm).trans
    ((LinearMap.rangeEquivOfInnerEq _ _ (inner_linearCombination_eq_of_inner_eq h)).trans
      (LinearIsometryEquiv.ofEq _ _ (Finsupp.range_linearCombination 𝕜)))

@[simp]
theorem linearIsometryEquivSpanOfInnerEq_apply_linearCombination (c : ι →₀ 𝕜)
    (hc : Finsupp.linearCombination 𝕜 φ c ∈ Submodule.span 𝕜 (Set.range φ)) :
    (linearIsometryEquivSpanOfInnerEq φ ψ h ⟨Finsupp.linearCombination 𝕜 φ c, hc⟩ : F)
      = Finsupp.linearCombination 𝕜 ψ c := by
  simp [linearIsometryEquivSpanOfInnerEq]

@[simp]
theorem linearIsometryEquivSpanOfInnerEq_apply (i : ι)
    (hi : φ i ∈ Submodule.span 𝕜 (Set.range φ)) :
    (linearIsometryEquivSpanOfInnerEq φ ψ h ⟨φ i, hi⟩ : F) = ψ i := by
  simpa using linearIsometryEquivSpanOfInnerEq_apply_linearCombination φ ψ h
    (Finsupp.single i 1) (by simpa using Submodule.subset_span (Set.mem_range_self (f := φ) i))

end

/-- In a finite-dimensional ambient space, two families with equal pairwise inner products
are related by a linear isometry equivalence of the whole space. -/
theorem exists_linearIsometryEquiv_map_eq_of_inner_eq [FiniteDimensional 𝕜 E] {φ ψ : ι → E}
    (h : ∀ i j, ⟪φ i, φ j⟫_𝕜 = ⟪ψ i, ψ j⟫_𝕜) :
    ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  let L : (Submodule.span 𝕜 (Set.range φ)) →ₗᵢ[𝕜] E :=
    (Submodule.span 𝕜 (Set.range ψ)).subtypeₗᵢ.comp
      (linearIsometryEquivSpanOfInnerEq φ ψ h).toLinearIsometry
  exact ⟨L.extend.toLinearIsometryEquiv rfl, fun i => by
    simpa [L] using L.extend_apply ⟨φ i, Submodule.subset_span ⟨i, rfl⟩⟩⟩

end GramSupport

-- The unused `F` (with its instances) mirrors the ForMathlib source's
-- `variable {𝕜 E F ι}` so the exported universe parameters match the solution
-- (the comparator compares universe signatures without alpha-normalizing).
variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E]

namespace Matrix

open _root_.Matrix

/--
**Gram rigidity, `Matrix.gram` form.** Two families of vectors in a
finite-dimensional inner product space have equal Gram matrices if and only if
a linear isometry equivalence of the ambient space maps one family to the other.
-/
theorem gram_eq_gram_iff_exists_linearIsometryEquiv_map_eq {φ ψ : ι → E} :
    gram 𝕜 φ = gram 𝕜 ψ ↔ ∃ W : E ≃ₗᵢ[𝕜] E, ∀ i, W (φ i) = ψ i := by
  constructor
  · intro hg
    exact exists_linearIsometryEquiv_map_eq_of_inner_eq fun i j => by
      simpa using congrFun₂ hg i j
  · rintro ⟨W, hW⟩
    ext i j
    simp [gram_apply, ← hW i, ← hW j, LinearIsometryEquiv.inner_map_map]

end Matrix
end TauCeti