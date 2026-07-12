/-
# Countable restrict-cover measurability (pending: minor)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as open obligations;
`Leaderboard.lean` imports the project and supplies the proofs. Only the leaf
(top-level) theorems are listed -- `#print axioms` on a leaf transitively certifies its
whole proof tree.
-/
import Mathlib

namespace ForMathlib

open MeasureTheory Set

/-- **Measurability from a countable restrict-cover** (countable version of
`measurable_of_restrict_of_restrict_compl`). -/
theorem measurable_of_iUnion_restrict {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    {g : Ω → A} {s : ℕ → Set Ω}
    (hs : ∀ k, MeasurableSet (s k)) (hcov : (⋃ k, s k) = univ)
    (hg : ∀ k, Measurable ((s k).restrict g)) : Measurable g := by
  intro t ht
  have hcov' : g ⁻¹' t = ⋃ k, s k ∩ g ⁻¹' t := by
    rw [← Set.iUnion_inter, hcov, Set.univ_inter]
  rw [hcov']
  refine MeasurableSet.iUnion fun k => ?_
  have hk : MeasurableSet (Subtype.val ⁻¹' (g ⁻¹' t) : Set (s k)) := hg k ht
  have him := (hs k).subtype_image hk
  rwa [Subtype.image_preimage_val] at him

end ForMathlib
