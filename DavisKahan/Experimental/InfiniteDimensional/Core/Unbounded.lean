/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.DirectRotation
import DavisKahan.SpectralTheory.ClosedOperator.Basic

/-!
# Open obligations of the closed-operator interface

The proved part of the interface now lives in
`DavisKahan.SpectralTheory.ClosedOperator.Basic`.  This module retains only the
declarations that are still unresolved, so that the admission closure stays
confined here.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

namespace ClosedOperator

/-- Adjoint of a densely defined closed operator.  The implementation should
be reconciled with mathlib's partial-linear-map adjoint API.

Construction route: define the domain as vectors `y` for which
`x ↦ ⟪A x, y⟫` is ambient-norm bounded on the dense domain, use Riesz
representation for the representing vector, and prove the resulting graph is
closed. -/
noncomputable def adjoint
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    ClosedOperator (𝕜 := 𝕜) (E := E) :=
  { domain := A.adjointDomain
    toLinearMap :=
      { toFun := A.adjointVector
        map_add' := fun y z => by
          apply ext_inner_left 𝕜
          intro x
          simp [adjointVector, A.adjointVector_inner]
        map_smul' := fun c y => by
          apply ext_inner_left 𝕜
          intro x
          simp [adjointVector, A.adjointVector_inner] }
    dense_domain := A.adjointDomain_dense
    closed_graph := A.adjoint_graph_closed }

/-- Sum with a relatively bounded operator on the same domain.

The relative-bound hypotheses are part of the constructor because an arbitrary
linear perturbation on `A.domain` need not have closed graph. -/
noncomputable def addRelative
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : A.domain →ₗ[𝕜] E) {a b : ℝ}
    (ha : 0 ≤ a) (hb0 : 0 ≤ b)
    (hrel : RelativelyBounded A V a b) (hb : b < 1) :
    ClosedOperator (𝕜 := 𝕜) (E := E) :=
  { domain := A.domain
    toLinearMap := A.toLinearMap + V
    dense_domain := A.dense_domain
    closed_graph := A.closed_graph_add_relativelyBounded V ha hb0 hrel hb }

/-- Unbounded spectral projection. -/
noncomputable def spectralProjection
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (s : Set ℝ) : E →L[𝕜] E := by
  classical
  by_cases hA : A.IsSelfAdjoint
  · exact RCLikeUnboundedSpectralTheorem.projection A hA s
  · exact 0

/-- Kato--Rellich theorem for bounded perturbations.

Lean proof route for a weaker agent:

1. Show the bounded sum has the same dense domain and closed graph as `A` by graph-norm equivalence.
2. Prove symmetry using `hA` and `hV`.
3. Apply bounded Kato--Rellich, or factor the nonreal resolvent and use a Neumann series for sufficiently large imaginary part.
4. Use the adjoint/resolvent characterization to prove equality with the Hilbert-space adjoint.


Ext-agent signature audit (GPT 5.6 High): Correct Kato--Rellich bounded-perturbation
target. It depends on the genuine adjoint equality, not maximal symmetry.

Preferred dependency route: Reconcile `ClosedOperator` with a genuine partial-operator
adjoint/resolvent API before attempting Kato--Rellich or unbounded spectral projection
arguments.
-/
theorem isSelfAdjoint_addBounded
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : E →L[𝕜] E)
    (hV : IsSelfAdjointOperator V) :
    (A.addBounded V).IsSelfAdjoint := by
  have hsym : (A.addBounded V).IsSymmetric := by
    intro x y
    simp [addBounded, hA.symmetric, hV]
  let η : ℝ := 2 * ‖V‖ + 1
  have hη : ‖V‖ / η < 1 := by
    have : 0 < η := by positivity
    rw [div_lt_one this]
    linarith [norm_nonneg V]
  have hfactor :
      (A.addBounded V).subScalar ((η : ℝ) : 𝕜 * RCLike.I) =
      (1 + V ∘L A.resolvent ((η : ℝ) : 𝕜 * RCLike.I)) ∘
        A.subScalar ((η : ℝ) : 𝕜 * RCLike.I) := by
    ext x
    simp [addBounded]
  have hunit : IsUnit (1 + V ∘L
      A.resolvent ((η : ℝ) : 𝕜 * RCLike.I)) := by
    apply isUnit_one_add_of_norm_lt_one
    calc
      ‖V ∘L A.resolvent ((η : ℝ) : 𝕜 * RCLike.I)‖
          ≤ ‖V‖ / η := by
            apply le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
            gcongr
            exact A.norm_resolvent_le_inv_abs_im hA _
      _ < 1 := hη
  exact selfAdjoint_of_symmetric_nonreal_shift_surjective
    hsym (surjective_of_factorization hfactor hunit)

/-- Kato--Rellich theorem for relatively bounded perturbations with relative
bound below one.

Proof strategy: equip the common domain with the graph norm of `A`.  Relative
boundedness with coefficient below one makes the perturbed graph norm
equivalent to the original graph norm, so `A+B` is closed.  Prove surjectivity
of `A+B-z` for one nonreal `z` by factoring

`A+B-z = (I + B(A-z)⁻¹)(A-z)`

and applying a Neumann series after choosing `|Im z|` large enough.  Symmetry
plus surjectivity at `z` and `conj z` yields self-adjointness.  Reconcile the
local `ClosedOperator` structure with mathlib's partial-map adjoint API before
attempting this proof.

Lean proof route for a weaker agent:

1. Use `ha`, `hb0`, `hrel`, and `hb<1` to prove equivalence of the graph norms of `A` and `A+V`.
2. Deduce closedness and density of the perturbed operator and use `hV` for symmetry.
3. Choose a nonreal spectral parameter with small `V(A-z)⁻¹` norm and invert by Neumann series.
4. Use the standard resolvent criterion for self-adjointness.


Ext-agent signature audit (GPT 5.6 High): Correct after `addRelative` was made to carry
nonnegative relative-bound parameters and a bound below one. The symmetry hypothesis on
`V` remains essential.

Preferred dependency route: Reconcile `ClosedOperator` with a genuine partial-operator
adjoint/resolvent API before attempting Kato--Rellich or unbounded spectral projection
arguments.
-/
theorem isSelfAdjoint_of_relativelyBounded
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : A.domain →ₗ[𝕜] E)
    (hV : ∀ x y : A.domain,
      ⟪V x, (y : E)⟫_𝕜 = ⟪(x : E), V y⟫_𝕜)
    {a b : ℝ} (ha : 0 ≤ a) (hb0 : 0 ≤ b)
    (hrel : RelativelyBounded A V a b) (hb : b < 1) :
    (A.addRelative V ha hb0 hrel hb).IsSelfAdjoint := by
  have hsym : (A.addRelative V ha hb0 hrel hb).IsSymmetric := by
    intro x y
    simp [addRelative, hA.symmetric, hV]
  obtain ⟨η, hη, hcontract⟩ :=
    exists_nonreal_parameter_relative_contraction hrel ha hb0 hb
  have hfactor := relativePerturbation_resolvent_factorization
    A V η
  have hunit : IsUnit (1 + V.afterResolvent A hA η) :=
    isUnit_one_add_of_norm_lt_one hcontract
  exact selfAdjoint_of_symmetric_nonreal_shift_surjective
    hsym (surjective_of_factorization hfactor hunit)

/-- Unbounded-operator `sin Θ` theorem with bounded difference.

Lean proof route for a weaker agent:

1. Use the unbounded spectral theorem to form the two spectral projections.
2. Derive the weak Sylvester equation between their ranges on `dom A`; the bounded perturbation supplies the residual.
3. Apply the unbounded general separated-spectrum Sylvester estimate in both directions using `hsepAB,hsepBA`.
4. Recombine the directed bounds and retain the universal `π/2` constant. Add a separate interval/exterior corollary for constant one.


Ext-agent signature audit (GPT 5.6 High): Corrected to the generic `π/2` constant for
arbitrary separated spectral sets. Both mixed gaps are still needed for the full
projection difference; a later interval/exterior theorem should recover constant one.

Preferred dependency route: Reconcile `ClosedOperator` with a genuine partial-operator
adjoint/resolvent API before attempting Kato--Rellich or unbounded spectral projection
arguments.
-/
theorem sinTheta_unbounded_boundedPerturbation
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (V : E →L[𝕜] E)
    (hV : IsSelfAdjointOperator V) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    {d : ℝ} (hd : 0 < d)
    (hsepAB : SpectralSetsSeparated A (A.addBounded V) s tᶜ d)
    (hsepBA : SpectralSetsSeparated (A.addBounded V) A t sᶜ d) :
    d * ‖A.spectralProjection s - (A.addBounded V).spectralProjection t‖ ≤
      (Real.pi / 2) * ‖V‖ := by
  let B := A.addBounded V
  have hB : B.IsSelfAdjoint := isSelfAdjoint_addBounded A hA V hV
  let P := A.spectralProjection s
  let Q := B.spectralProjection t
  have hforward :
      d * ‖(1-Q) ∘L P‖ ≤ (Real.pi/2) * ‖V‖ := by
    have heq := mixedProjection_unboundedSylvesterEquation
      A B hA hB P Q hs ht V
    exact unbounded_sylvester_general_separation_opNorm
      A B hA hB hsepAB hd heq
  have hbackward :
      d * ‖(1-P) ∘L Q‖ ≤ (Real.pi/2) * ‖V‖ := by
    have heq := mixedProjection_unboundedSylvesterEquation
      B A hB hA Q P ht hs (-V)
    simpa [norm_neg] using
      unbounded_sylvester_general_separation_opNorm
        B A hB hA hsepBA hd heq
  have hprojection := norm_projection_sub_eq_max_directed P Q
    (spectralProjection_isOrthogonal hA hs)
    (spectralProjection_isOrthogonal hB ht)
  rw [hprojection]
  exact max_le
    ((mul_le_mul_of_nonneg_left hforward hd.le))
    ((mul_le_mul_of_nonneg_left hbackward hd.le))

end ClosedOperator
end DavisKahanExt
end ForMathlib
