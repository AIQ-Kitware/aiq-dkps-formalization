/- Checked applications accompanying the closing lecture slides.
The imports own the mathematics; these examples introduce no new API. -/
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten

noncomputable section

-- slide-begin
open scoped ENNReal
open TauCeti.UnitarilyInvariantSeminorm
variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (A : E →ₗ[ℝ] E) (p : ℝ≥0∞) [Fact (1 ≤ p)]

example (hp : p ≠ ∞) :
    schatten ℝ E E p A =
      (A.singularValues.sum
        fun _ s ↦ s ^ p.toReal)
        ^ (1 / p.toReal) :=
  schatten_apply_of_ne_top p hp A

example (U V : E ≃ₗᵢ[ℝ] E) :
    LinearMap.singularValues
      ((U : E →ₗ[ℝ] E) ∘ₗ
        (A ∘ₗ (V : E →ₗ[ℝ] E)))
      = A.singularValues := by
  rw [LinearMap.singularValues_linearIsometryEquiv_comp,
    LinearMap.singularValues_comp_linearIsometryEquiv]
-- slide-end
