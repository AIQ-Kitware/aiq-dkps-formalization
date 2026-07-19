/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidt
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidtFiniteRank
import Spectra.Spaces.Tensor.HilbertSchmidt
import Spectra.QuantumMechanics.Channels.TraceClass.Basic

/-!
# Basis and tensor models of the paper square norm

The source square norm is defined in the main development by the complete
approximation-number sequence.  The spectral proof of the second generalized
sine theorem needs the equivalent Hilbert-space model.  This file proves the
coordinate bridge:

* the column-square sum is independent of the Hilbert basis;
* it equals the sum of squared approximation singular values;
* finite energy is equivalent to representation by a unique vector of
  `E tensor Conj F`;
* the tensor norm is exactly the paper square norm.

The key comparison uses finite basis projections.  For every finite set of
basis vectors, finite-dimensional Eckart--Young and the Frobenius identity
identify the two cutoff energies.  Strong convergence of the projections and
monotone convergence then identify their suprema.  No compactness assumption
is made; compactness follows afterwards from finite square energy.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal

noncomputable section

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Extended column-square energy in a chosen Hilbert basis of the domain. -/
def paperHilbertSchmidtBasisEnergy {ι : Type*}
    (b : HilbertBasis ι ℂ F) (A : F →L[ℂ] E) : ENNReal :=
  ∑' i, (‖A (b i)‖₊ : ENNReal) ^ 2

/-- Adjoint cross-swap for rectangular operators. -/
theorem paperHilbertSchmidtBasisEnergy_adjoint_swap
    {ι κ : Type*} (bF : HilbertBasis ι ℂ F)
    (bE : HilbertBasis κ ℂ E) (A : F →L[ℂ] E) :
    paperHilbertSchmidtBasisEnergy bF A =
      paperHilbertSchmidtBasisEnergy bE A.adjoint := by
  have hsym : ∀ i j,
      ‖⟪bE j, A (bF i)⟫_ℂ‖₊ =
        ‖⟪bF i, A.adjoint (bE j)⟫_ℂ‖₊ := by
    intro i j
    rw [← ContinuousLinearMap.adjoint_inner_left,
      ← inner_conj_symm (bF i) (A.adjoint (bE j)), RCLike.nnnorm_conj]
  calc
    paperHilbertSchmidtBasisEnergy bF A
        = ∑' i, ∑' j,
            (‖⟪bE j, A (bF i)⟫_ℂ‖₊ : ENNReal) ^ 2 := by
          simp_rw [paperHilbertSchmidtBasisEnergy,
            Spectra.QuantumMechanics.Channels.tsum_enorm_inner_sq bE]
    _ = ∑' j, ∑' i,
          (‖⟪bE j, A (bF i)⟫_ℂ‖₊ : ENNReal) ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i,
          (‖⟪bF i, A.adjoint (bE j)⟫_ℂ‖₊ : ENNReal) ^ 2 :=
        tsum_congr fun j => tsum_congr fun i =>
          congrArg (fun x : NNReal => (x : ENNReal) ^ 2) (hsym i j)
    _ = paperHilbertSchmidtBasisEnergy bE A.adjoint := by
          simp_rw [paperHilbertSchmidtBasisEnergy,
            Spectra.QuantumMechanics.Channels.tsum_enorm_inner_sq bF]

/-- The rectangular column-square energy does not depend on the domain basis. -/
theorem paperHilbertSchmidtBasisEnergy_indep
    {ι κ : Type*} (b c : HilbertBasis ι ℂ F)
    (d : HilbertBasis κ ℂ E) (A : F →L[ℂ] E) :
    paperHilbertSchmidtBasisEnergy b A =
      paperHilbertSchmidtBasisEnergy c A := by
  rw [paperHilbertSchmidtBasisEnergy_adjoint_swap b d A,
    ← paperHilbertSchmidtBasisEnergy_adjoint_swap c d A]

/-- Projection onto the span of a finite set of Hilbert-basis vectors. -/
noncomputable def paperBasisProjection {ι : Type*}
    (b : HilbertBasis ι ℂ F) (s : Finset ι) : F →L[ℂ] F :=
  (Submodule.span ℂ (b '' (s : Set ι))).starProjection

/-- The finite basis projection is an orthogonal projection. -/
theorem paperBasisProjection_isOrthogonalProjection {ι : Type*}
    (b : HilbertBasis ι ℂ F) (s : Finset ι) :
    IsOrthogonalProjectionMap (paperBasisProjection b s) := by
  exact ⟨(Submodule.span ℂ (b '' (s : Set ι))).starProjection_isIdempotent,
    (Submodule.span ℂ (b '' (s : Set ι))).starProjection_isSymmetric.adjoint_eq⟩

/-- The finite cutoff has rank at most the number of selected basis vectors. -/
theorem rank_paperBasisProjection_le {ι : Type*}
    (b : HilbertBasis ι ℂ F) (s : Finset ι) :
    (paperBasisProjection b s).rank ≤ (s.card : Cardinal) := by
  calc
    (paperBasisProjection b s).rank
        ≤ Module.rank ℂ (Submodule.span ℂ (b '' (s : Set ι))) := by
          exact LinearMap.rank_le_of_range_le
            (Submodule.starProjection_range _).le
    _ ≤ (s.card : Cardinal) := by
          simpa using Submodule.rank_span_le_card (R := ℂ)
            (s.image b)

/-- The cutoff operator is the finite column expansion. -/
theorem comp_paperBasisProjection_apply {ι : Type*}
    (b : HilbertBasis ι ℂ F) (s : Finset ι)
    (A : F →L[ℂ] E) (x : F) :
    (A ∘L paperBasisProjection b s) x =
      ∑ i ∈ s, ⟪b i, x⟫_ℂ • A (b i) := by
  rw [ContinuousLinearMap.comp_apply]
  have hproj : paperBasisProjection b s x =
      ∑ i ∈ s, ⟪b i, x⟫_ℂ • b i := by
    exact Submodule.starProjection_eq_sum_orthonormal
      b.orthonormal (s := s) x
  rw [hproj, map_sum]
  simp only [map_smul]

/-- Finite-cutoff Frobenius identity in approximation-number form. -/
theorem paperHilbertSchmidtEnergy_comp_paperBasisProjection
    {ι : Type*} (b : HilbertBasis ι ℂ F) (s : Finset ι)
    (A : F →L[ℂ] E) :
    paperHilbertSchmidtEnergy (A ∘L paperBasisProjection b s) =
      ∑ i ∈ s, ENNReal.ofReal (‖A (b i)‖ ^ 2) := by
  let U : EuclideanSpace ℂ s →ₗᵢ[ℂ] F :=
    LinearIsometry.ofOrthonormal
      (fun i : s => b i.1) (b.orthonormal.comp_subtype s)
  let T : EuclideanSpace ℂ s →L[ℂ] E := A ∘L U.toContinuousLinearMap
  have hsame : SameApproximationSingularSequence
      (A ∘L paperBasisProjection b s) T := by
    intro n
    apply le_antisymm
    · exact approximationSingularValue_comp_isometry_le n A
        U.toContinuousLinearMap
    · have hrange : Set.range U =
          Submodule.span ℂ (b '' (s : Set ι)) := by
        exact LinearIsometry.range_ofOrthonormal_eq_span _ _
      exact approximationSingularValue_le_of_isometricRangeRestriction
        n A U hrange
  rw [hsame.paperHilbertSchmidtEnergy_eq]
  have hTrank : T.rank ≤ (s.card : Cardinal) := by
    calc T.rank ≤ Module.rank ℂ (EuclideanSpace ℂ s) :=
      LinearMap.rank_le_domain T.toLinearMap
    _ = (s.card : Cardinal) := by simp
  rw [paperHilbertSchmidtEnergy_eq_sum_range_of_rank_le hTrank]
  have hfinite : ∀ n < s.card,
      approximationSingularValue n T = T.toLinearMap.singularValues n := by
    intro n hn
    exact approximationSingularValue_eq_singularValues T.toLinearMap n
  rw [Finset.sum_congr rfl fun n hn => congrArg ENNReal.ofReal
    (congrArg (· ^ 2) (hfinite n (Finset.mem_range.mp hn)))]
  rw [← Fin.sum_univ_eq_sum_range]
  have hsq := ForMathlib.sum_sq_singularValues T.toLinearMap rfl
    (EuclideanSpace.basisFun s ℂ)
  rw [hsq]
  apply Finset.sum_congr rfl
  intro i hi
  simp [T, U, ENNReal.ofReal_pow, LinearIsometry.ofOrthonormal_apply]

/-- Finite basis projections converge strongly to the identity. -/
theorem paperBasisProjection_stronglyTendsto {ι : Type*}
    (b : HilbertBasis ι ℂ F) :
    StronglyTendsto (fun s : Finset ι => paperBasisProjection b s)
      atTop (ContinuousLinearMap.id ℂ F) := by
  intro x
  have hsum := b.hasSum_repr x
  have hpartial : Tendsto
      (fun s : Finset ι => ∑ i ∈ s, ⟪b i, x⟫_ℂ • b i)
      atTop (𝓝 x) := hsum.tendsto_sum_nat
  simpa [paperBasisProjection,
    Submodule.starProjection_eq_sum_orthonormal b.orthonormal] using hpartial

/-- Approximation singular values of finite basis cutoffs converge pointwise. -/
theorem approximationSingularValue_cutoff_tendsto {ι : Type*}
    (b : HilbertBasis ι ℂ F) (A : F →L[ℂ] E) (n : ℕ) :
    Tendsto
      (fun s : Finset ι => approximationSingularValue n
        (A ∘L paperBasisProjection b s))
      atTop (𝓝 (approximationSingularValue n A)) := by
  exact approximationSingularValue_comp_strongProjection_tendsto_complex
    (fun s => paperBasisProjection_isOrthogonalProjection b s)
    (paperBasisProjection_stronglyTendsto b) n A

/-- The approximation-number energy is the supremum of finite-basis cutoff
energies. -/
theorem paperHilbertSchmidtEnergy_eq_iSup_cutoff {ι : Type*}
    (b : HilbertBasis ι ℂ F) (A : F →L[ℂ] E) :
    paperHilbertSchmidtEnergy A =
      ⨆ s : Finset ι,
        paperHilbertSchmidtEnergy (A ∘L paperBasisProjection b s) := by
  apply le_antisymm
  · unfold paperHilbertSchmidtEnergy
    rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro t
    obtain ⟨s, hs⟩ : ∃ s : Finset ι,
        ∀ n ∈ t, ENNReal.ofReal ((approximationSingularValue n A) ^ 2) ≤
          paperHilbertSchmidtEnergy (A ∘L paperBasisProjection b s) := by
      classical
      choose s hs using fun n : ℕ =>
        (approximationSingularValue_cutoff_tendsto b A n).eventually
          (eventually_ge_atTop
            (approximationSingularValue n A - (1 : ℝ) / (t.card + 1)))
      exact ⟨t.biUnion s, fun n hn => by
        exact le_trans (ENNReal.ofReal_mono (pow_le_pow_left₀
          (approximationSingularValue_nonneg n A) (hs n) 2))
          (ENNReal.le_tsum n)⟩
    calc
      ∑ n ∈ t, ENNReal.ofReal ((approximationSingularValue n A) ^ 2)
          ≤ ∑ n ∈ t,
              paperHilbertSchmidtEnergy
                (A ∘L paperBasisProjection b s) :=
            Finset.sum_le_sum fun n hn => hs n hn
      _ ≤ paperHilbertSchmidtEnergy
            (A ∘L paperBasisProjection b s) := by
          simpa using ENNReal.sum_const_le_self
      _ ≤ ⨆ s : Finset ι,
            paperHilbertSchmidtEnergy
              (A ∘L paperBasisProjection b s) := le_iSup _ s
  · apply iSup_le
    intro s
    unfold paperHilbertSchmidtEnergy
    apply ENNReal.tsum_le_tsum
    intro n
    exact ENNReal.ofReal_mono (pow_le_pow_left₀
      (approximationSingularValue_nonneg n _)
      (approximationSingularValue_comp_le n A
        (paperBasisProjection b s)) 2)

/-- A nonnegative series is the supremum of its finite partial subsums. -/
theorem paperHilbertSchmidtBasisEnergy_eq_iSup_finset {ι : Type*}
    (b : HilbertBasis ι ℂ F) (A : F →L[ℂ] E) :
    paperHilbertSchmidtBasisEnergy b A =
      ⨆ s : Finset ι, ∑ i ∈ s, ENNReal.ofReal (‖A (b i)‖ ^ 2) := by
  unfold paperHilbertSchmidtBasisEnergy
  rw [ENNReal.tsum_eq_iSup_sum]
  congr 1
  funext s
  apply Finset.sum_congr rfl
  intro i hi
  simp [ENNReal.coe_pow, ENNReal.ofReal_pow]

/-- The approximation-number and basis definitions of rectangular
Hilbert--Schmidt energy agree exactly. -/
theorem paperHilbertSchmidtEnergy_eq_basisEnergy {ι : Type*}
    (b : HilbertBasis ι ℂ F) (A : F →L[ℂ] E) :
    paperHilbertSchmidtEnergy A = paperHilbertSchmidtBasisEnergy b A := by
  rw [paperHilbertSchmidtEnergy_eq_iSup_cutoff b A,
    paperHilbertSchmidtBasisEnergy_eq_iSup_finset b A]
  congr 1
  funext s
  exact paperHilbertSchmidtEnergy_comp_paperBasisProjection b s A

/-- Paper square membership is equivalent to square-summable columns in any
Hilbert basis. -/
theorem isPaperHilbertSchmidt_iff_summable_basis {ι : Type*}
    (b : HilbertBasis ι ℂ F) (A : F →L[ℂ] E) :
    IsPaperHilbertSchmidt A ↔ Summable (fun i => ‖A (b i)‖ ^ 2) := by
  unfold IsPaperHilbertSchmidt
  rw [paperHilbertSchmidtEnergy_eq_basisEnergy b A,
    ← ENNReal.tsum_coe_ne_top_iff_summable]
  simp only [paperHilbertSchmidtBasisEnergy, ENNReal.coe_pow,
    coe_nnnorm]

/-- The paper square norm is the ordinary basis Hilbert--Schmidt norm. -/
theorem paperHilbertSchmidtNorm_eq_sqrt_tsum_basis {ι : Type*}
    (b : HilbertBasis ι ℂ F) (A : F →L[ℂ] E)
    (hA : IsPaperHilbertSchmidt A) :
    paperHilbertSchmidtNorm A = Real.sqrt (∑' i, ‖A (b i)‖ ^ 2) := by
  rw [paperHilbertSchmidtNorm, paperHilbertSchmidtEnergy_eq_basisEnergy b A]
  have hsummable := (isPaperHilbertSchmidt_iff_summable_basis b A).1 hA
  rw [ENNReal.toReal_tsum]
  simp [paperHilbertSchmidtBasisEnergy, hsummable,
    ENNReal.toReal_ofReal (sq_nonneg _)]

/-- Finite paper square energy is equivalent to representation by a unique
Hilbert tensor. -/
theorem isPaperHilbertSchmidt_iff_existsUnique_tensor
    (A : F →L[ℂ] E) :
    IsPaperHilbertSchmidt A ↔
      ∃! z : Spectra.HilbertSchmidtTensor.Space E F,
        Spectra.HilbertSchmidtTensor.toOperator z = A := by
  let b := stdHilbertBasis F
  rw [isPaperHilbertSchmidt_iff_summable_basis b A]
  exact (Spectra.HilbertSchmidtTensor.
    existsUnique_tensor_iff_summable_columns b A).symm

/-- The canonical tensor representing a paper Hilbert--Schmidt operator. -/
noncomputable def paperHilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : IsPaperHilbertSchmidt A) :
    Spectra.HilbertSchmidtTensor.Space E F :=
  Classical.choose ((isPaperHilbertSchmidt_iff_existsUnique_tensor A).1 hA)

@[simp]
theorem toOperator_paperHilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : IsPaperHilbertSchmidt A) :
    Spectra.HilbertSchmidtTensor.toOperator
      (paperHilbertSchmidtTensor A hA) = A :=
  (Classical.choose_spec
    ((isPaperHilbertSchmidt_iff_existsUnique_tensor A).1 hA)).1

/-- The tensor norm is exactly the paper square norm. -/
theorem norm_paperHilbertSchmidtTensor (A : F →L[ℂ] E)
    (hA : IsPaperHilbertSchmidt A) :
    ‖paperHilbertSchmidtTensor A hA‖ = paperHilbertSchmidtNorm A := by
  let b := stdHilbertBasis F
  have hsq := Spectra.HilbertSchmidtTensor.norm_sq_eq_tsum_column_norm_sq
    b (paperHilbertSchmidtTensor A hA)
  rw [toOperator_paperHilbertSchmidtTensor] at hsq
  have hnorm := paperHilbertSchmidtNorm_eq_sqrt_tsum_basis b A hA
  rw [hnorm]
  nlinarith [norm_nonneg (paperHilbertSchmidtTensor A hA),
    Real.sqrt_nonneg (∑' i, ‖A (b i)‖ ^ 2)]

/-- Every Hilbert tensor represents a paper Hilbert--Schmidt operator. -/
theorem isPaperHilbertSchmidt_toOperator
    (z : Spectra.HilbertSchmidtTensor.Space E F) :
    IsPaperHilbertSchmidt (Spectra.HilbertSchmidtTensor.toOperator z) := by
  rw [isPaperHilbertSchmidt_iff_existsUnique_tensor]
  refine ⟨z, rfl, ?_⟩
  intro w hw
  exact Spectra.HilbertSchmidtTensor.toOperator_injective hw

/-- The paper square norm of the represented operator is exactly the Hilbert
tensor norm. -/
theorem paperHilbertSchmidtNorm_toOperator
    (z : Spectra.HilbertSchmidtTensor.Space E F) :
    paperHilbertSchmidtNorm (Spectra.HilbertSchmidtTensor.toOperator z) = ‖z‖ := by
  let hZ := isPaperHilbertSchmidt_toOperator z
  have hcanon := norm_paperHilbertSchmidtTensor
    (Spectra.HilbertSchmidtTensor.toOperator z) hZ
  have heq : paperHilbertSchmidtTensor
      (Spectra.HilbertSchmidtTensor.toOperator z) hZ = z := by
    apply Spectra.HilbertSchmidtTensor.toOperator_injective
    rw [toOperator_paperHilbertSchmidtTensor]
  rw [heq] at hcanon
  exact hcanon.symm

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
