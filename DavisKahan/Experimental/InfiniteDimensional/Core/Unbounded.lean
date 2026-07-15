/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.DirectRotation

/-!
# Closed and unbounded self-adjoint operators

The operator is a linear map on a dense submodule with closed graph.  Its
adjoint is defined by ambient representability of the form
`x ↦ ⟪A x, y⟫`.  Bounded and relatively bounded perturbations retain the
same domain.  Spectral projections are totalized only for API compatibility:
the valid self-adjoint branch uses the unbounded spectral theorem and the
invalid branch is zero.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

structure ClosedOperator where
  domain : Submodule 𝕜 E
  toLinearMap : domain →ₗ[𝕜] E
  dense_domain : Dense (domain : Set E)
  closed_graph : IsClosed (Set.range fun x : domain => ((x : E), toLinearMap x))

namespace ClosedOperator

def Extends (A B : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  ∃ hdom : A.domain ≤ B.domain,
    ∀ x : A.domain,
      B.toLinearMap ⟨(x : E), hdom x.property⟩ = A.toLinearMap x

def IsSymmetric (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  ∀ x y : A.domain,
    ⟪A.toLinearMap x, (y : E)⟫_𝕜 =
      ⟪(x : E), A.toLinearMap y⟫_𝕜

/-- Domain of the Hilbert-space adjoint. -/
def adjointDomain (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    Submodule 𝕜 E :=
  { carrier := {y | ∃ C : ℝ, 0 ≤ C ∧ ∀ x : A.domain,
      ‖⟪A.toLinearMap x, y⟫_𝕜‖ ≤ C * ‖(x : E)‖}
    zero_mem' := by simp
    add_mem' := by
      rintro y z ⟨Cy, hCy, hy⟩ ⟨Cz, hCz, hz⟩
      refine ⟨Cy+Cz, add_nonneg hCy hCz, ?_⟩
      intro x
      calc
        ‖⟪A.toLinearMap x, y+z⟫_𝕜‖
            ≤ ‖⟪A.toLinearMap x, y⟫_𝕜‖ +
              ‖⟪A.toLinearMap x, z⟫_𝕜‖ := by
                simpa [inner_add_right] using norm_add_le _ _
        _ ≤ (Cy+Cz) * ‖(x:E)‖ := by nlinarith [hy x, hz x]
    smul_mem' := by
      rintro c y ⟨C, hC, hy⟩
      refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
      intro x
      simpa [inner_smul_right, norm_mul, mul_assoc] using
        mul_le_mul_of_nonneg_left (hy x) (norm_nonneg c) }

/-- Adjoint vector represented by Riesz on the dense domain. -/
noncomputable def adjointVector
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (y : A.adjointDomain) : E := by
  classical
  let f : A.domain →L[𝕜] 𝕜 :=
    A.boundedInnerFunctional y y.property
  exact InnerProductSpace.toDual 𝕜 E |>.symm
    (f.extendFromDense A.dense_domain)

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

def IsSelfAdjoint (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  A.adjoint = A

noncomputable def graphNorm (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : ℝ :=
  Real.sqrt (‖(x : E)‖ ^ 2 + ‖A.toLinearMap x‖ ^ 2)

noncomputable def addBounded (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : E →L[𝕜] E) : ClosedOperator (𝕜 := 𝕜) (E := E) :=
  { domain := A.domain
    toLinearMap := A.toLinearMap + V.toLinearMap.comp A.domain.subtype
    dense_domain := A.dense_domain
    closed_graph := A.closed_graph_add_bounded V }

def RelativelyBounded (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : A.domain →ₗ[𝕜] E) (a b : ℝ) : Prop :=
  ∀ x, ‖V x‖ ≤ a * ‖(x : E)‖ + b * ‖A.toLinearMap x‖

/-- Real spectrum, obtained from the complexification of the closed operator. -/
noncomputable def realSpectrum
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Set ℝ :=
  {λ | ((λ : ℝ) : ℂ) ∈
    RCLikeComplexification.closedOperatorSpectrum A}

def SpectralSetsSeparated
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : ClosedOperator (𝕜 := 𝕜) (E := F))
    (s t : Set ℝ) (d : ℝ) : Prop :=
  ∀ a ∈ A.realSpectrum, a ∈ s →
    ∀ b ∈ B.realSpectrum, b ∈ t → d ≤ |a - b|

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

/-- Total compatibility spectral projection. -/
noncomputable def spectralProjection
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (s : Set ℝ) : E →L[𝕜] E := by
  classical
  by_cases hA : A.IsSelfAdjoint
  · exact RCLikeUnboundedSpectralTheorem.projection A hA s
  · exact 0

@[simp] theorem spectralProjection_of_selfAdjoint
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ) :
    A.spectralProjection s =
      RCLikeUnboundedSpectralTheorem.projection A hA s := by
  simp [spectralProjection, hA]

/-- Kato--Rellich for bounded self-adjoint perturbations. -/
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

/-- Kato--Rellich for symmetric relatively bounded perturbations of relative
bound strictly below one. -/
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

/-- Unbounded-operator `sin Θ` theorem with bounded difference and arbitrary
separated spectral sets. -/
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
