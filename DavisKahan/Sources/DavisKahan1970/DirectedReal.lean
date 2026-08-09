/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.WholeSpaceReal
import DavisKahan.TanTheta.Theorem63InfiniteTrial
import DavisKahan.OperatorIdeal.ComplexificationApproximation
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport

/-!
# Directed Section 2 bounds over real Hilbert spaces

This module transports the directed Section 2 tangent theorem from the complex
Hilbert-space implementation back to real Hilbert spaces. The transport is at
the finite-Ky-Fan level, where approximation numbers are exactly preserved by
complexification; source unitarily invariant norms are recovered afterward by
Fan dominance.

The infinite-dimensional tangent representative is constructed over the real
trial space itself. This uses the scalar-generic prescribed-approximation-number
construction in ForTauCeti rather than comparing scalar-fixed ideal families
across the real and complex fields.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Experimental.ExactSinTheta
open TauCeti.DavisKahan.Experimental.ExactSinTheta.ComplexificationApproximation
open TauCeti.DavisKahan.Experimental.ExactTanTheta
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Experimental.Foundation.RealComplexification

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local instance instCompleteSpaceCoeOfHasOrthogonalProjectionDirectedReal
    {k : Type*} [RCLike k] {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace k G] [CompleteSpace G]
    (Z : Submodule k G) [Z.HasOrthogonalProjection] : CompleteSpace Z :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection Z).completeSpace_coe

/-! ## Real trial blocks and complexification transport -/

/-- Real directed sine block used by the Theorem 6.3 tangent estimate. -/
noncomputable def theorem63DirectedSineBlockReal
    (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] : Z →L[ℝ] E :=
  V.orthogonal.starProjection.comp Z.subtypeL

/-- Real Rayleigh--Ritz residual, in complementary-projection form. -/
noncomputable def theorem63ResidualReal
    (T : E →L[ℝ] E) (Z : Submodule ℝ E)
    [Z.HasOrthogonalProjection] : Z →L[ℝ] E :=
  (Z.orthogonal.starProjection.comp T).comp Z.subtypeL

/-- The real residual is the usual action-minus-compression residual. -/
theorem theorem63ResidualReal_eq_action_sub_compression
    (T : E →L[ℝ] E) (Z : Submodule ℝ E)
    [Z.HasOrthogonalProjection] :
    theorem63ResidualReal T Z =
      T.comp Z.subtypeL - Z.subtypeL.comp (compressOperatorReal Z T) := by
  apply ContinuousLinearMap.ext
  intro z
  change Z.orthogonal.starProjection (T (z : E)) =
    T (z : E) - Z.subtypeL (Z.orthogonalProjectionOnto (T (z : E)))
  rw [Submodule.starProjection_orthogonal_apply]
  rfl

/-- Through the canonical subspace adapter, the complex directed sine block is
exactly the complexification of the real directed sine block. -/
theorem theorem63DirectedSineBlock_complexify_equiv
    (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (theorem63DirectedSineBlock (complexifySubmodule Z) (complexifySubmodule V)).comp
        (complexifySubmoduleEquiv Z).toContinuousLinearEquiv.toContinuousLinearMap =
      complexify (theorem63DirectedSineBlockReal Z V) := by
  apply ContinuousLinearMap.ext
  intro w
  change (complexifySubmodule V).orthogonal.starProjection
      (((complexifySubmoduleEquiv Z w : complexifySubmodule Z) : RealComplexification E)) =
    complexify (V.orthogonal.starProjection.comp Z.subtypeL) w
  rw [starProjection_complexifySubmodule_orthogonal,
    coe_complexifySubmoduleEquiv_eq_complexify_subtypeL,
    RealComplexification.complexify_comp]
  rfl

/-- Through the same adapter, the complex Ritz residual is the complexification
of the real Ritz residual. -/
theorem theorem63Residual_complexify_equiv
    (T : E →L[ℝ] E) (Z : Submodule ℝ E)
    [Z.HasOrthogonalProjection] :
    (theorem63Residual (complexify T) (complexifySubmodule Z)).comp
        (complexifySubmoduleEquiv Z).toContinuousLinearEquiv.toContinuousLinearMap =
      complexify (theorem63ResidualReal T Z) := by
  rw [theorem63Residual_eq_complementaryProjection]
  apply ContinuousLinearMap.ext
  intro w
  change (complexifySubmodule Z).orthogonal.starProjection
      ((complexify T)
        (((complexifySubmoduleEquiv Z w : complexifySubmodule Z) : RealComplexification E))) =
    complexify ((Z.orthogonal.starProjection.comp T).comp Z.subtypeL) w
  rw [starProjection_complexifySubmodule_orthogonal,
    coe_complexifySubmoduleEquiv_eq_complexify_subtypeL,
    RealComplexification.complexify_comp,
    RealComplexification.complexify_comp]
  rfl

/-- Approximation singular values of the directed sine block are preserved by
real complexification and the canonical trial-subspace coordinate change. -/
theorem approximationSingularValue_theorem63DirectedSineBlock_complexify
    (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (n : Nat) :
    approximationSingularValue n
        (theorem63DirectedSineBlock (complexifySubmodule Z) (complexifySubmodule V)) =
      approximationSingularValue n (theorem63DirectedSineBlockReal Z V) := by
  let U := LinearIsometryEquiv.refl Complex (RealComplexification E)
  let W := complexifySubmoduleEquiv Z
  have hcoord :
      (U.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (complexify (theorem63DirectedSineBlockReal Z V))).comp
          W.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        theorem63DirectedSineBlock (complexifySubmodule Z) (complexifySubmodule V) := by
    apply ContinuousLinearMap.ext
    intro z
    let w := W.symm z
    have hw : W w = z := W.apply_symm_apply z
    have h := congrArg (fun L => L w)
      (theorem63DirectedSineBlock_complexify_equiv Z V)
    simpa [U, W, w, hw] using h.symm
  have hsame := SameApproximationSingularValues.of_isometricEquiv_comp U W hcoord
  exact (hsame n).symm.trans
    (approximationSingularValue_complexify (theorem63DirectedSineBlockReal Z V) n)

/-- Approximation singular values of the real Ritz residual are likewise
preserved under the complexified Theorem 6.3 configuration. -/
theorem approximationSingularValue_theorem63Residual_complexify
    (T : E →L[ℝ] E) (Z : Submodule ℝ E)
    [Z.HasOrthogonalProjection] (n : Nat) :
    approximationSingularValue n
        (theorem63Residual (complexify T) (complexifySubmodule Z)) =
      approximationSingularValue n (theorem63ResidualReal T Z) := by
  let U := LinearIsometryEquiv.refl Complex (RealComplexification E)
  let W := complexifySubmoduleEquiv Z
  have hcoord :
      (U.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (complexify (theorem63ResidualReal T Z))).comp
          W.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        theorem63Residual (complexify T) (complexifySubmodule Z) := by
    apply ContinuousLinearMap.ext
    intro z
    let w := W.symm z
    have hw : W w = z := W.apply_symm_apply z
    have h := congrArg (fun L => L w)
      (theorem63Residual_complexify_equiv T Z)
    simpa [U, W, w, hw] using h.symm
  have hsame := SameApproximationSingularValues.of_isometricEquiv_comp U W hcoord
  exact (hsame n).symm.trans
    (approximationSingularValue_complexify (theorem63ResidualReal T Z) n)

/-- The finite Ky Fan residual gauge is exactly preserved by the real-to-complex
Theorem 6.3 transport. -/
theorem kyFanApproximationGauge_theorem63Residual_complexify
    (T : E →L[ℝ] E) (Z : Submodule ℝ E)
    [Z.HasOrthogonalProjection] (k : Nat) :
    kyFanApproximationGauge k
        (theorem63Residual (complexify T) (complexifySubmodule Z)) =
      kyFanApproximationGauge k (theorem63ResidualReal T Z) := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  exact Finset.sum_congr rfl fun n _ =>
    approximationSingularValue_theorem63Residual_complexify T Z n

/-! ## Real infinite-trial tangent theorem -/

/-- The complex infinite-trial Ky Fan theorem descends without loss to a real
Hilbert space. This is the scalar-transport core; no scalar-fixed ideal family
is compared across fields. -/
theorem theorem6_3_all_kyFan_core_infiniteTrial_real
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (V Z : Submodule ℝ E) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z, ⟪compressOperatorReal Z T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (k : Nat) :
    delta * Finset.sum (Finset.range k) (fun n =>
      Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlockReal Z V)))) <=
      kyFanApproximationGauge k (theorem63ResidualReal T Z) := by
  have hTC : (complexify T).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((complexify_isSelfAdjoint_iff T).2 hT)
  have hVC : (complexify T).Reduces (complexifySubmodule V) :=
    (complexify_reduces_iff T V).2 hV
  have hcore := theorem6_3_all_kyFan_core_infiniteTrial
    (complexify T) (complexifySubmodule V) (complexifySubmodule Z)
    hTC hVC hdelta
    (fun z => by
      simpa [theorem63Compression, TauCeti.DavisKahanExt.compressOperator] using
        re_inner_compressOperator_le Z T hCompressionUpper z)
    (fun y hy => by
      rw [← complexifySubmodule_orthogonal V] at hy
      exact le_re_inner_of_mem_complexifySubmodule hUnwantedLower hy)
    k
  simpa only [
    approximationSingularValue_theorem63DirectedSineBlock_complexify,
    kyFanApproximationGauge_theorem63Residual_complexify] using hcore

/-- Under the real source gap every directed sine approximation value is below
one, so the real tangent sequence has no pole. -/
theorem approximationSingularValue_sineBlock_lt_one_infiniteTrial_real
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (V Z : Submodule ℝ E) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z, ⟪compressOperatorReal Z T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (n : Nat) :
    approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1 := by
  have hTC : (complexify T).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      ((complexify_isSelfAdjoint_iff T).2 hT)
  have hVC : (complexify T).Reduces (complexifySubmodule V) :=
    (complexify_reduces_iff T V).2 hV
  have hlt := approximationSingularValue_sineBlock_lt_one_infiniteTrial
    (complexify T) (complexifySubmodule V) (complexifySubmodule Z)
    hTC hVC hdelta
    (fun z => by
      simpa [theorem63Compression, TauCeti.DavisKahanExt.compressOperator] using
        re_inner_compressOperator_le Z T hCompressionUpper z)
    (fun y hy => by
      rw [← complexifySubmodule_orthogonal V] at hy
      exact le_re_inner_of_mem_complexifySubmodule hUnwantedLower hy)
    n
  simpa only [approximationSingularValue_theorem63DirectedSineBlock_complexify] using hlt

/-- A real tangent representative has exactly the approximation numbers
prescribed by the paper's directed angle. -/
def HasTheorem63DirectedTangentApproximationNumbersInfiniteReal
    (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (tanTheta0 : Z →L[ℝ] E) : Prop :=
  ∀ n, approximationSingularValue n tanTheta0 =
    Real.tan (Real.arcsin
      (approximationSingularValue n (theorem63DirectedSineBlockReal Z V)))

/-- Inclusion of a closed real trial subspace preserves every approximation
singular value of an endomorphism of that subspace. -/
theorem approximationSingularValue_subtypeL_comp_real
    (Z : Submodule ℝ E) [Z.HasOrthogonalProjection]
    (A : Z →L[ℝ] Z) (k : Nat) :
    approximationSingularValue k (Z.subtypeL.comp A) =
      approximationSingularValue k A := by
  have hmem : ∀ x : Z, (Z.subtypeL.comp A) x ∈ Z :=
    fun x => (A x).property
  have hcomp : Z.orthogonalProjectionOnto.comp (Z.subtypeL.comp A) = A := by
    ext x
    change Z.starProjection ((A x : E)) = ((A x : E))
    exact Submodule.starProjection_eq_self_iff.mpr (A x).property
  calc
    approximationSingularValue k (Z.subtypeL.comp A) =
        approximationSingularValue k
          (Z.orthogonalProjectionOnto.comp (Z.subtypeL.comp A)) :=
      (approximationSingularValue_orthogonalProjectionOnto_comp_eq Z
        (Z.subtypeL.comp A) hmem k).symm
    _ = approximationSingularValue k A := by rw [hcomp]

/-- On an infinite-dimensional real trial space, the tangent representative
with the paper's complete singular-value sequence exists as a real operator. -/
theorem exists_hasTheorem63DirectedTangentApproximationNumbersInfiniteReal
    (Z V : Submodule ℝ E) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hinf : Not (FiniteDimensional ℝ Z))
    (hlt : ∀ n,
      approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1) :
    Exists (fun tanTheta0 : Z →L[ℝ] E =>
      HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0) := by
  let d : Nat → ℝ := fun n => Real.tan (Real.arcsin
    (approximationSingularValue n (theorem63DirectedSineBlockReal Z V)))
  have h0 : forall n, 0 <= d n := fun n =>
    TanArcsin.tanArcsin_nonneg (approximationSingularValue_nonneg _ _)
  have hanti : Antitone d := by
    intro m n hmn
    exact TanArcsin.tanArcsin_le_tanArcsin
      (approximationSingularValue_nonneg _ _)
      (approximationSingularValue_antitone (theorem63DirectedSineBlockReal Z V) hmn)
      (hlt m)
  obtain ⟨D0, hD0⟩ :=
    TauCeti.ApproximationNumber.exists_approximationNumber_eq_of_antitone
      (E := Z) hinf d h0 hanti
  refine ⟨Z.subtypeL ∘L D0, fun n => ?_⟩
  rw [approximationSingularValue_subtypeL_comp_real Z D0 n]
  exact hD0 n

/-- Real directed half of the Section 2 tan-theta theorem at every source
unitarily invariant norm, for an arbitrary infinite-dimensional trial space.

The complex Theorem 6.3 proof supplies the Ky Fan inequalities; exact
complexification transport reads them back over the reals; the tangent
representative is then constructed over the real trial space and Fan dominance
supplies the source norm. Finite-dimensional real trial spaces are already
covered by the scalar-generic finite Theorem 6.3. -/
theorem tanTheta_directed_paperUINorm_real_infinite
    (N : PaperUnitaryInvariantNorm)
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T)
    (V Z : Submodule ℝ E) [V.HasOrthogonalProjection] [Z.HasOrthogonalProjection]
    (hinf : Not (FiniteDimensional ℝ Z))
    (hV : T.Reduces V) {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : Z, ⟪compressOperatorReal Z T z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (hResidual : N.Mem (theorem63ResidualReal T Z)) :
    Exists (fun tanTheta0 : Z →L[ℝ] E =>
      And (HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0)
        (And (N.Mem tanTheta0)
          (delta * N.gauge tanTheta0 <= N.gauge (theorem63ResidualReal T Z)))) := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V hinf
      (fun n => approximationSingularValue_sineBlock_lt_one_infiniteTrial_real
        T hT V Z hV hdelta hCompressionUpper hUnwantedLower n)
  have hky : ∀ k : Nat,
      delta * kyFanApproximationGauge k tanTheta0 <=
        kyFanApproximationGauge k (theorem63ResidualReal T Z) := by
    intro k
    have hcore := theorem6_3_all_kyFan_core_infiniteTrial_real
      T hT V Z hV hdelta hCompressionUpper hUnwantedLower k
    have htanKy : kyFanApproximationGauge k tanTheta0 =
        Finset.sum (Finset.range k) (fun n =>
          Real.tan (Real.arcsin
            (approximationSingularValue n (theorem63DirectedSineBlockReal Z V)))) := by
      unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
      exact Finset.sum_congr rfl fun n _ => htan n
    rw [htanKy]
    exact hcore
  obtain ⟨hmem, hbound⟩ := N.mul_gauge_le_of_all_mul_kyFan_le hdelta hResidual hky
  exact ⟨tanTheta0, htan, hmem, hbound⟩

end
end DavisKahan1970
end TauCeti
