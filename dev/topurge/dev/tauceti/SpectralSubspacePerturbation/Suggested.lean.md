# Provisional Lean signatures

These signatures are discussion aids.  The roadmap prose is authoritative,
and names should be adapted to current Mathlib and Tau Ceti conventions before
submission.

## Approximation numbers

```lean
noncomputable def approximationNumber
    (T : E →L[𝕜] F) (n : ℕ) : ℝ

theorem approximationNumber_zero :
    approximationNumber T 0 = ‖T‖

theorem approximationNumber_adjoint :
    approximationNumber T.adjoint n = approximationNumber T n

theorem approximationNumber_comp_le
    (A : F →L[𝕜] G) (B : D →L[𝕜] E) :
    approximationNumber (A.comp (T.comp B)) n ≤
      ‖A‖ * approximationNumber T n * ‖B‖
```

## Rectangular symmetric ideals

```lean
structure RectangularSymmetricIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  Mem : (E →L[𝕜] F) → Prop
  gauge : (E →L[𝕜] F) → ℝ≥0∞
  comp_left_mem : Mem T → Mem (A.comp T)
  comp_right_mem : Mem T → Mem (T.comp B)
  gauge_comp_left_le : gauge (A.comp T) ≤ ‖A‖₊ * gauge T
  gauge_comp_right_le : gauge (T.comp B) ≤ gauge T * ‖B‖₊
```

## Closed Sylvester equations

```lean
structure ClosedSylvesterEquation
    (A : ClosedOperator 𝕜 E) (B : ClosedOperator 𝕜 F)
    (X : F →L[𝕜] E) (C : F →L[𝕜] E) : Prop where
  mapsDomain : X '' B.domain ≤ A.domain
  equation : ∀ x : B.domain, A (X x) - X (B x) = C x

def PairwiseSpectrumGap
    (A : ClosedOperator ℂ E) (B : ClosedOperator ℂ F)
    (δ : ℝ) : Prop :=
  ∀ a ∈ spectrum A, ∀ b ∈ spectrum B, δ ≤ |a - b|
```

## Operator angles

```lean
noncomputable def directedCosine
    (U V : Submodule ℂ E) : E →L[ℂ] E

noncomputable def directedSine
    (U V : Submodule ℂ E) : E →L[ℂ] E

theorem directedSine_sq_add_directedCosine_sq :
    directedSine U V ^ 2 + directedCosine U V ^ 2 = U.starProjection

theorem norm_directedSine_eq_gap :
    ‖directedSine U V‖ = directedGap U V
```

## Perturbation theorems

```lean
theorem finite_sinTheta
    (hgap : IntervalExteriorGap A B U V δ)
    (N : RectangularUnitarilyInvariantNorm 𝕜) :
    δ * N (directedSine U V) ≤ N (B - A)

theorem closed_sinTheta
    (hEq : ClosedSylvesterEquation A₀ A₁ X residual)
    (hgap : PairwiseSpectrumGap A₀ A₁ δ)
    (hframe : LowerFrameBound X ε) :
    δ * ε * gauge (directedSine exact trial) ≤ gauge residual
```

## Hilbert--Schmidt pairwise-gap theorem

```lean
theorem hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap
    (hEq : ClosedSylvesterEquation A B X C)
    (hgap : PairwiseSpectrumGap A B δ)
    (hδ : 0 < δ) :
    δ * hilbertSchmidtNorm X ≤ hilbertSchmidtNorm C
```
