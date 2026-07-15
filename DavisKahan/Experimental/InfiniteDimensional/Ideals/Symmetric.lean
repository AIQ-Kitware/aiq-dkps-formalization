/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.OperatorAngle
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Rectangular

/-!
# Symmetric norm ideals

Infinite-dimensional unitarily invariant norm statements live on compact
operator ideals, not on all bounded operators.  This file records the ideal
API needed to lift operator-norm Davis--Kahan estimates to Schatten, trace,
Hilbert--Schmidt, and general symmetric ideals.

Literature writeup: local TeX, Section 9.
-/


/-! ## Construction plan

Build this layer bottom-up from compact operators.

1. Use mathlib's compact continuous-linear maps and prove existence of singular
   values through the positive compact operator `T⋆T`.
2. Define the operator norm and Ky Fan gauges directly from the singular-value
   sequence; prove ideal inequalities and unitary invariance.
3. Define Schatten classes by summability of powers of singular values, with
   trace class and Hilbert--Schmidt as special cases.
4. Package each displayed norm only after completeness and the ideal property
   are available.  Prove finite-rank density before transferring finite
   Davis--Kahan estimates by approximation.
-/


/-! ## Weak-agent execution plan: symmetric ideals

Do not attempt the general `SymmetricNormIdeal` endpoint first.  Build a ladder
whose early stages can compile independently:

1. finite-rank continuous operators, with singular values defined by
   restriction to the finite-dimensional range/domain support;
2. compact operators and their singular-value sequence, using the compact
   positive spectral theorem for `T.adjoint ∘L T`;
3. Ky Fan gauges and the two ideal inequalities;
4. Schatten membership and norm for a fixed `p`;
5. completeness and finite-rank density;
6. the abstract symmetric-gauge ideal package.

Each ideal should be represented by a subtype carrying `mem`; define its norm
on the subtype instead of a total gauge plus repeated membership hypotheses.
Keep a coercion to bounded operators and prove composition/adjoint closure as
subtype constructors.  This will make later Sylvester statements readable.

The finite-to-compact transfer should approximate `T` by spectral truncations
of `|T|`, prove the Davis--Kahan inequality on each finite-rank truncation, and
pass to the ideal norm using completeness.  Do not assume operator-norm
convergence implies convergence in an arbitrary ideal norm.

Before general symmetric ideals, finish Hilbert--Schmidt and trace class as
test cases.  They expose missing summability and adjoint APIs without the full
symmetric-gauge representation theorem.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A symmetric norm ideal of bounded operators on a Hilbert space. -/
structure SymmetricNormIdeal where
  mem : (E →L[𝕜] E) → Prop
  gauge : (E →L[𝕜] E) → ℝ
  zero_mem : mem 0
  add_mem : ∀ {A B}, mem A → mem B → mem (A + B)
  smul_mem : ∀ (c : 𝕜) {A}, mem A → mem (c • A)
  ideal_mem : ∀ (L R : E →L[𝕜] E) {A}, mem A → mem (L ∘L A ∘L R)
  adjoint_mem : ∀ {A}, mem A → mem A.adjoint
  nonneg : ∀ {A}, mem A → 0 ≤ gauge A
  gauge_zero : gauge 0 = 0
  gauge_eq_zero : ∀ {A}, mem A → gauge A = 0 → A = 0
  triangle : ∀ {A B}, mem A → mem B →
    gauge (A + B) ≤ gauge A + gauge B
  gauge_smul : ∀ (c : 𝕜) {A}, mem A →
    gauge (c • A) = ‖c‖ * gauge A
  gauge_adjoint : ∀ {A}, mem A → gauge A.adjoint = gauge A
  unitary_invariant : ∀ (U Uinv A : E →L[𝕜] E),
    IsUnitaryOperator U → IsUnitaryOperator Uinv →
    Uinv ∘L U = ContinuousLinearMap.id 𝕜 E →
    U ∘L Uinv = ContinuousLinearMap.id 𝕜 E →
    mem A → gauge (U ∘L A ∘L Uinv) = gauge A
  ideal_bound : ∀ (L R : E →L[𝕜] E) {A}, mem A →
    gauge (L ∘L A ∘L R) ≤ ‖L‖ * gauge A * ‖R‖
  gauge_complete : ∀ u : ℕ → (E →L[𝕜] E),
    (∀ n, mem (u n)) →
    (∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
      gauge (u m - u n) < ε) →
    ∃ A, mem A ∧ ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
      gauge (u n - A) < ε

namespace SymmetricNormIdeal

open ForMathlib.DavisKahan.Experimental.ExactSinTheta

/-- Restrict a coherent rectangular family to endomorphisms of one Hilbert
space.  Unitary invariance follows from the two-sided ideal estimate in both
directions. -/
noncomputable def ofRectangular
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜)) :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) := by
  classical
  refine
    { mem := N.Mem
      gauge := N.gauge
      zero_mem := N.zero_mem
      add_mem := N.add_mem
      smul_mem := N.smul_mem
      ideal_mem := fun L R A hA => N.comp_mem L R hA
      adjoint_mem := N.adjoint_mem
      nonneg := N.gauge_nonneg
      gauge_zero := N.gauge_zero
      gauge_eq_zero := N.gauge_eq_zero
      triangle := N.gauge_add_le
      gauge_smul := N.gauge_smul
      gauge_adjoint := N.gauge_adjoint
      unitary_invariant := ?_
      ideal_bound := fun L R A hA => N.gauge_comp_le L R hA
      gauge_complete := N.gauge_complete }
  intro U Uinv A hU hUinv hleft hright hA
  have hmem : N.Mem (U ∘L A ∘L Uinv) := N.comp_mem U Uinv hA
  have hUnorm : ‖U‖ = 1 := hU.opNorm_eq_one
  have hUinvnorm : ‖Uinv‖ = 1 := hUinv.opNorm_eq_one
  apply le_antisymm
  · calc
      N.gauge (U ∘L A ∘L Uinv)
          ≤ ‖U‖ * N.gauge A * ‖Uinv‖ := N.gauge_comp_le U Uinv hA
      _ = N.gauge A := by rw [hUnorm, hUinvnorm, one_mul, mul_one]
  · have hreconstruct :
        Uinv ∘L (U ∘L A ∘L Uinv) ∘L U = A := by
      simp only [ContinuousLinearMap.comp_assoc]
      rw [hleft, hright]
      simp
    calc
      N.gauge A
          = N.gauge (Uinv ∘L (U ∘L A ∘L Uinv) ∘L U) := by rw [hreconstruct]
      _ ≤ ‖Uinv‖ * N.gauge (U ∘L A ∘L Uinv) * ‖U‖ :=
        N.gauge_comp_le Uinv U hmem
      _ = N.gauge (U ∘L A ∘L Uinv) := by
        rw [hUnorm, hUinvnorm, one_mul, mul_one]

/-- The operator norm ideal. -/
noncomputable def operatorNorm : SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofRectangular RectangularSymmetricIdealFamily.operatorNorm

/-- Compact-operator ideal equipped with the operator norm. -/
noncomputable def compactOperator :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofRectangular RectangularSymmetricIdealFamily.compactOperatorNorm

/-- Schatten `p` ideal. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofRectangular (RectangularSymmetricIdealFamily.schatten p hp)

/-- Trace-class ideal. -/
noncomputable def traceClass : SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofRectangular RectangularSymmetricIdealFamily.traceClass

/-- Hilbert--Schmidt ideal. -/
noncomputable def hilbertSchmidt : SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofRectangular RectangularSymmetricIdealFamily.hilbertSchmidt

/-- Ky Fan `k` ideal norm for positive `k`. -/
noncomputable def kyFan (k : ℕ) (hk : 0 < k) :
    SymmetricNormIdeal (𝕜 := 𝕜) (E := E) :=
  ofRectangular (RectangularSymmetricIdealFamily.kyFan k hk)

/-- Unitary conjugation preserves both membership and gauge. -/
theorem gauge_unitary_conjugation
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U Uinv A : E →L[𝕜] E) (hA : I.mem A)
    (hU : IsUnitaryOperator U) (hUinv : IsUnitaryOperator Uinv)
    (hleft : Uinv ∘L U = ContinuousLinearMap.id 𝕜 E)
    (hright : U ∘L Uinv = ContinuousLinearMap.id 𝕜 E) :
    I.mem (U ∘L A ∘L Uinv) ∧
      I.gauge (U ∘L A ∘L Uinv) = I.gauge A :=
  ⟨I.ideal_mem U Uinv hA,
    I.unitary_invariant U Uinv A hU hUinv hleft hright hA⟩

private theorem reflection_unitary
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsUnitaryOperator (reflectionOperator U) := by
  refine ⟨?_, ?_⟩
  · simpa [ContinuousLinearMap.star_eq_adjoint,
      (Submodule.reflectionOperator_isSelfAdjoint U).star_eq] using
      reflectionOperator_involutive U
  · simpa [ContinuousLinearMap.star_eq_adjoint,
      (Submodule.reflectionOperator_isSelfAdjoint U).star_eq] using
      reflectionOperator_involutive U

/-- Pinching is contractive for every symmetric norm ideal. -/
theorem gauge_diagonalPart_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (hA : I.mem A) :
    I.mem (diagonalPart U A) ∧
      I.gauge (diagonalPart U A) ≤ I.gauge A := by
  let J := reflectionOperator U
  have hJ : IsUnitaryOperator J := reflection_unitary U
  have hJinv : J ∘L J = ContinuousLinearMap.id 𝕜 E :=
    reflectionOperator_involutive U
  have hconjMem : I.mem (J ∘L A ∘L J) := I.ideal_mem J J hA
  have hconjGauge : I.gauge (J ∘L A ∘L J) = I.gauge A :=
    I.unitary_invariant J J A hJ hJ hJinv hJinv hA
  have hformula : (2 : 𝕜) • diagonalPart U A = A + J ∘L A ∘L J :=
    two_smul_diagonalPart_eq_add_reflectionConjugate U A
  have hsumMem : I.mem (A + J ∘L A ∘L J) := I.add_mem hA hconjMem
  have hhalf : ((2 : 𝕜)⁻¹) • ((2 : 𝕜) • diagonalPart U A) =
      diagonalPart U A := by module
  have hdiagMem : I.mem (diagonalPart U A) := by
    rw [← hhalf, hformula]
    exact I.smul_mem _ hsumMem
  refine ⟨hdiagMem, ?_⟩
  have hscaled := I.gauge_smul (2 : 𝕜) hdiagMem
  rw [hformula, norm_ofNat] at hscaled
  have htriangle := I.triangle hA hconjMem
  rw [hconjGauge] at htriangle
  nlinarith

/-- Off-diagonal extraction is contractive for every symmetric norm ideal. -/
theorem gauge_offDiagonalPart_le
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : E →L[𝕜] E) (hA : I.mem A) :
    I.mem (offDiagonalPart U A) ∧
      I.gauge (offDiagonalPart U A) ≤ I.gauge A := by
  let J := reflectionOperator U
  have hJ : IsUnitaryOperator J := reflection_unitary U
  have hJinv : J ∘L J = ContinuousLinearMap.id 𝕜 E :=
    reflectionOperator_involutive U
  have hconjMem : I.mem (J ∘L A ∘L J) := I.ideal_mem J J hA
  have hnegConjMem : I.mem (-(J ∘L A ∘L J)) := by
    simpa using I.smul_mem (-1 : 𝕜) hconjMem
  have hconjGauge : I.gauge (J ∘L A ∘L J) = I.gauge A :=
    I.unitary_invariant J J A hJ hJ hJinv hJinv hA
  have hformula : (2 : 𝕜) • offDiagonalPart U A = A - J ∘L A ∘L J :=
    two_smul_offDiagonalPart_eq_sub_reflectionConjugate U A
  have hdiffMem : I.mem (A - J ∘L A ∘L J) := by
    simpa [sub_eq_add_neg] using I.add_mem hA hnegConjMem
  have hhalf : ((2 : 𝕜)⁻¹) • ((2 : 𝕜) • offDiagonalPart U A) =
      offDiagonalPart U A := by module
  have hoffMem : I.mem (offDiagonalPart U A) := by
    rw [← hhalf, hformula]
    exact I.smul_mem _ hdiffMem
  refine ⟨hoffMem, ?_⟩
  have hscaled := I.gauge_smul (2 : 𝕜) hoffMem
  rw [hformula, norm_ofNat] at hscaled
  have htriangle : I.gauge (A - J ∘L A ∘L J) ≤
      I.gauge A + I.gauge (J ∘L A ∘L J) := by
    simpa [sub_eq_add_neg, I.gauge_smul (-1 : 𝕜) hconjMem] using
      I.triangle hA hnegConjMem
  rw [hconjGauge] at htriangle
  nlinarith

end SymmetricNormIdeal
end DavisKahanExt
end ForMathlib
