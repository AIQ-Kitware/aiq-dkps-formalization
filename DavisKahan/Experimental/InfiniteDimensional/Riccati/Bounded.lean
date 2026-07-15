/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.GraphSubspace

/-!
# Bounded block operator matrices and Riccati equations
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]

structure BlockOperatorData where
  A0 : E0 →L[𝕜] E0
  A1 : E1 →L[𝕜] E1
  B01 : E1 →L[𝕜] E0
  B10 : E0 →L[𝕜] E1
  selfAdjoint0 : IsSelfAdjointOperator A0
  selfAdjoint1 : IsSelfAdjointOperator A1
  offDiagonalAdjoint : ∀ x y, ⟪B01 y, x⟫_𝕜 = ⟪y, B10 x⟫_𝕜

/-- Bounded block operator on the Hilbert direct sum. -/
noncomputable def blockOperator
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) := by
  let L : E0 × E1 →ₗ[𝕜] E0 × E1 :=
    { toFun := fun x =>
        (H.A0 x.1 + H.B01 x.2, H.B10 x.1 + H.A1 x.2)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp }
  have hL : ∀ x, ‖L x‖ ≤
      (‖H.A0‖ + ‖H.A1‖ + ‖H.B01‖ + ‖H.B10‖) * ‖x‖ := by
    intro x
    exact blockOperator_product_norm_bound H x
  exact WithLp.conjugateContinuousLinearMap 2
    (LinearMap.mkContinuous L _ hL)

/-- Graph of a bounded operator in the Hilbert direct sum. -/
noncomputable def blockGraph (X : E0 →L[𝕜] E1) :
    Submodule 𝕜 (WithLp 2 (E0 × E1)) :=
  (LinearMap.range ((WithLp.linearEquiv 2 𝕜 (E0 × E1)).symm.toLinearMap ∘ₗ
    LinearMap.id.prod X.toLinearMap)).topologicalClosure

noncomputable def blockDiagonalOperator
    (D0 : E0 →L[𝕜] E0) (D1 : E1 →L[𝕜] E1) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) :=
  WithLp.conjugateContinuousLinearMap 2 (D0.prod D1)

def riccatiDefect
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : E0 →L[𝕜] E1 :=
  H.A1 ∘L X - X ∘L H.A0 - X ∘L H.B01 ∘L X + H.B10

def SolvesRiccati
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) : Prop :=
  riccatiDefect H X = 0

/-- The block operator is self-adjoint. -/
theorem blockOperator_isSelfAdjoint
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1)) :
    IsSelfAdjointOperator (blockOperator H) := by
  intro x y
  rcases WithLp.toLp x with ⟨x0,x1⟩
  rcases WithLp.toLp y with ⟨y0,y1⟩
  simp [blockOperator, H.selfAdjoint0, H.selfAdjoint1,
    H.offDiagonalAdjoint]

/-- Graph reduction is equivalent to the Riccati equation. -/
theorem graph_reduces_iff_solvesRiccati
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    (X : E0 →L[𝕜] E1) :
    Reduces (blockOperator H) (blockGraph X) ↔ SolvesRiccati H X := by
  have hclosed : IsClosed (blockGraph X : Set _) :=
    Submodule.isClosed_topologicalClosure
  rw [reduces_iff_invariant_of_isSymmetric
    (blockOperator_isSelfAdjoint H) hclosed]
  constructor
  · intro hinv
    apply ContinuousLinearMap.ext
    intro u
    have hmem := hinv (blockGraphVector X u) (blockGraphVector_mem X u)
    obtain ⟨v, hv⟩ := blockGraph_coordinate_unique X hmem
    have hfirst : v = H.A0 u + H.B01 (X u) := by
      simpa [blockOperator, blockGraphVector] using congrArg blockFirst hv
    have hsecond : X v = H.B10 u + H.A1 (X u) := by
      simpa [blockOperator, blockGraphVector] using congrArg blockSecond hv
    simp [riccatiDefect, hfirst, hsecond]
  · intro hric
    intro z hz
    obtain ⟨u, rfl⟩ := blockGraph_dense_range_representation X hz
    refine blockGraphVector_mem X (H.A0 u + H.B01 (X u)) |>.cast ?_
    apply WithLp.ext
    · simp [blockOperator, blockGraphVector]
    · have hu := congrArg (fun T : E0 →L[𝕜] E1 => T u) hric
      simpa [riccatiDefect, blockOperator, blockGraphVector] using hu

/-- The selected contractive Riccati branch exists below the conservative
small-coupling threshold. -/
theorem exists_riccati_solution_of_gap
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d)
    (hgap : IntervalExteriorSeparated H.A0 ⊤ H.A1 ⊤ left right d)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ∃ X : E0 →L[𝕜] E1,
      SolvesRiccati H X ∧ ‖X‖ < 1 ∧
      ‖X‖ ≤ Real.tan (Real.arctan (2 * ‖H.B01‖ / d) / 2) := by
  let L0 := blockDiagonalOperator H.A0 H.A1
  let L := blockOperator H
  let U0 : Submodule 𝕜 (WithLp 2 (E0 × E1)) := firstCoordinateSubspace
  obtain ⟨Γ, hΓ⟩ :=
    exists_uniform_block_gap_contour H hd hgap hsmall
  let Q := rieszProjection L Γ
  have hQred : Reduces L (LinearMap.range Q.toLinearMap) :=
    rieszProjection_reduces L (blockOperator_isSelfAdjoint H) Γ hΓ.endpoint
  have hacute : IsAcute U0 (LinearMap.range Q.toLinearMap) := by
    exact block_continuedProjection_acute H hd hgap hsmall Γ hΓ
  obtain ⟨Xambient, hXang, hgraph, huniq⟩ :=
    existsUnique_angularOperator U0 (LinearMap.range Q.toLinearMap) hacute
  let X : E0 →L[𝕜] E1 :=
    coordinateAngularOperator Xambient hXang
  have hgraph' : blockGraph X = LinearMap.range Q.toLinearMap :=
    coordinateGraph_eq hgraph
  have hric : SolvesRiccati H X := by
    rw [← graph_reduces_iff_solvesRiccati]
    simpa [hgraph'] using hQred
  have hcontract : ‖X‖ < 1 :=
    coordinateAngularOperator_norm_lt_one hXang
      (continuedBlockAngle_lt_pi_div_four hsmall hΓ)
  have hbound := norm_riccati_solution_scalar_majorant
    H hd hgap hsmall hric hcontract
  exact ⟨X, hric, hcontract, hbound⟩

/-- Sharp a priori estimate for the selected contractive solution. -/
theorem norm_riccati_solution_le
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d)
    (hgap : IntervalExteriorSeparated H.A0 ⊤ H.A1 ⊤ left right d)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X : E0 →L[𝕜] E1} (hX : SolvesRiccati H X)
    (hXc : ‖X‖ < 1) :
    ‖X‖ ≤ Real.tan (Real.arctan (2 * ‖H.B01‖ / d) / 2) := by
  let b := ‖H.B01‖
  have hB10 : ‖H.B10‖ = b := by
    exact norm_eq_of_adjoint_pair H.offDiagonalAdjoint
  have hquadratic : d * ‖X‖ + b * ‖X‖^2 ≤ b := by
    have hSylv : H.A1 ∘L X - X ∘L H.A0 =
        X ∘L H.B01 ∘L X - H.B10 := by
      have := hX
      simp [SolvesRiccati, riccatiDefect] at this
      linear_combination this
    exact intervalExterior_riccati_quadratic_estimate
      H.selfAdjoint0 H.selfAdjoint1 hgap hd hSylv hXc hB10
  have hroot := smaller_root_bound_of_quadratic
    (norm_nonneg X) (norm_nonneg H.B01) hd hquadratic
  simpa [b, tan_half_arctan_two_mul_div] using hroot

/-- Uniqueness in the contractive ball. -/
theorem unique_contractive_riccati_solution
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d)
    (hgap : IntervalExteriorSeparated H.A0 ⊤ H.A1 ⊤ left right d)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X Y : E0 →L[𝕜] E1}
    (hX : SolvesRiccati H X) (hY : SolvesRiccati H Y)
    (hXc : ‖X‖ < 1) (hYc : ‖Y‖ < 1) :
    X = Y := by
  let Z := X-Y
  have hZeq :
      (H.A1 - X ∘L H.B01) ∘L Z -
        Z ∘L (H.A0 + H.B01 ∘L Y) = 0 := by
    have hx := hX
    have hy := hY
    simp [SolvesRiccati, riccatiDefect] at hx hy
    linear_combination hx - hy
  have hsep : 0 < d - ‖H.B01‖ * (‖X‖ + ‖Y‖) := by
    have : ‖X‖ + ‖Y‖ < 2 := by linarith
    nlinarith [hsmall, norm_nonneg H.B01]
  have hbound := sylvester_unique_of_perturbed_ordered_gap
    H.selfAdjoint0 H.selfAdjoint1 hgap hd X Y hXc hYc hsmall hZeq hsep
  have hZzero : Z = 0 := by simpa using hbound
  exact sub_eq_zero.mp hZzero

/-- Canonical unitary graph rotation. -/
noncomputable def riccatiGraphUnitary (X : E0 →L[𝕜] E1) :
    WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1) := by
  let C0 := RCLikeContinuousFunctionalCalculus.invSqrt
    (1 + star X ∘L X)
  let C1 := RCLikeContinuousFunctionalCalculus.invSqrt
    (1 + X ∘L star X)
  exact blockContinuousLinearMap C0 (-star X ∘L C1)
    (X ∘L C0) C1

/-- The Riccati graph rotation block diagonalizes the self-adjoint block
operator. -/
theorem blockDiagonalization_of_riccati
    (H : BlockOperatorData (𝕜 := 𝕜) (E0 := E0) (E1 := E1))
    {X : E0 →L[𝕜] E1} (hX : SolvesRiccati H X) :
    ∃ W Winv : WithLp 2 (E0 × E1) →L[𝕜] WithLp 2 (E0 × E1),
      ∃ D0 : E0 →L[𝕜] E0, ∃ D1 : E1 →L[𝕜] E1,
      IsUnitaryOperator W ∧ IsUnitaryOperator Winv ∧
      Winv ∘L W = ContinuousLinearMap.id 𝕜 (WithLp 2 (E0 × E1)) ∧
      W ∘L Winv = ContinuousLinearMap.id 𝕜 (WithLp 2 (E0 × E1)) ∧
      Winv ∘L blockOperator H ∘L W = blockDiagonalOperator D0 D1 := by
  let W := riccatiGraphUnitary X
  let Winv := star W
  let D0 := H.A0 + H.B01 ∘L X
  let D1 := H.A1 - H.B10 ∘L star X
  have hWunit : IsUnitaryOperator W := by
    exact normalizedGraphRotation_unitary X
  have hWinv : IsUnitaryOperator Winv := hWunit.star
  have hleft : Winv ∘L W = 1 := hWunit.star_mul_self
  have hright : W ∘L Winv = 1 := hWunit.mul_star_self
  have hdiag : Winv ∘L blockOperator H ∘L W =
      blockDiagonalOperator D0 D1 := by
    apply blockContinuousLinearMap_ext <;>
      simp [W, Winv, D0, D1, riccatiGraphUnitary,
        SolvesRiccati, riccatiDefect] at hX ⊢ <;>
      linear_combination hX
  exact ⟨W, Winv, D0, D1, hWunit, hWinv,
    by simpa using hleft, by simpa using hright, hdiag⟩

end DavisKahanExt
end ForMathlib
