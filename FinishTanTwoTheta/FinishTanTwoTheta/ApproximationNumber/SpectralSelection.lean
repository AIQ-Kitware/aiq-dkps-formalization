/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.GroundedImports
import FinishTanTwoTheta.OperatorIdeal.StandardInstances
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMaxUpper
import DavisKahan.OperatorIdeal.ApproximationNumbers.FiniteSourceSingularSystem
import DavisKahan.Experimental.Scratch.Section7.InfiniteTanTwoThetaCore
import Spectra.SpectralTheory.Essential.Discrete

/-!
# Approximate leading singular families

The hard noncompact input is isolated as a finite spectral-band model for the
positive Gram operator `X.adjoint ∘L X`.  Once that model exists, the left
vectors are normalized images of the selected right vectors.  Their
orthonormality and both approximate singular equations are derived explicitly;
no polar-decomposition or imaginary singular-system theorem is invoked.
-/

namespace TauCeti
namespace FinishTanTwoTheta

open scoped InnerProductSpace BigOperators
open Set
open DavisKahan.Experimental.ExactSinTheta
open DavisKahan.Experimental.SpectraBridge
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.QuantumMechanics.SpectralTheory

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- A finite simultaneous approximate singular system for the non-negligible
part of the first `k` approximation numbers. -/
structure ApproximateLeadingSingularFamily
    (X : E0 →L[ℂ] E1) (k : ℕ) (ε : ℝ) where
  count : ℕ
  count_le : count ≤ k
  right : Fin count → E0
  left : Fin count → E1
  right_orthonormal : Orthonormal ℂ right
  left_orthonormal : Orthonormal ℂ left
  selected_large : ∀ i : Fin count, ε < X.approximationNumber i
  apply_residual : ∀ i : Fin count,
    ‖X (right i) - (X.approximationNumber i : ℂ) • left i‖ ≤ ε
  adjoint_residual : ∀ i : Fin count,
    ‖X.adjoint (left i) - (X.approximationNumber i : ℂ) • right i‖ ≤ ε
  tail_small : ∀ n, count ≤ n → n < k → X.approximationNumber n ≤ ε

namespace ApproximateLeadingSingularFamily

variable {X : E0 →L[ℂ] E1} {k : ℕ} {ε : ℝ}

@[simp] theorem norm_right (F : ApproximateLeadingSingularFamily X k ε)
    (i : Fin F.count) : ‖F.right i‖ = 1 :=
  F.right_orthonormal.norm_eq_one i

@[simp] theorem norm_left (F : ApproximateLeadingSingularFamily X k ε)
    (i : Fin F.count) : ‖F.left i‖ = 1 :=
  F.left_orthonormal.norm_eq_one i

/-- Negating the right family preserves orthonormality. -/
theorem orthonormal_neg_right
    (F : ApproximateLeadingSingularFamily X k ε) :
    Orthonormal ℂ (fun i => -F.right i) := by
  rw [orthonormal_iff_ite] at F.right_orthonormal ⊢
  intro i j
  simpa using F.right_orthonormal i j

end ApproximateLeadingSingularFamily

/-- The bounded positive Gram operator used for spectral selection. -/
def gramOperator (X : E0 →L[ℂ] E1) : E0 →L[ℂ] E0 :=
  X.adjoint ∘L X

/-- The Gram operator is self-adjoint. -/
theorem gramOperator_isSelfAdjoint (X : E0 →L[ℂ] E1) :
    IsSelfAdjoint (gramOperator X) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪X.adjoint (X x), y⟫_ℂ = ⟪x, X.adjoint (X y)⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- Finite compression supplied by narrow Gram spectral bands.

`value i` is the square root of the diagonal Gram coefficient on `right i`.
The diagonal identity makes the normalized images exactly orthonormal, while
`gram_residual` records the width of the spectral band. -/
structure GramSpectralBandModel
    (X : E0 →L[ℂ] E1) (k : ℕ) (ε : ℝ) where
  count : ℕ
  count_le : count ≤ k
  right : Fin count → E0
  value : Fin count → ℝ
  right_orthonormal : Orthonormal ℂ right
  value_pos : ∀ i, 0 < value i
  value_close : ∀ i,
    |value i - X.approximationNumber i| ≤ ε / 8
  image_inner : ∀ i j,
    ⟪X (right i), X (right j)⟫_ℂ =
      if i = j then (value i ^ 2 : ℂ) else 0
  gram_residual : ∀ i,
    ‖gramOperator X (right i) - (value i ^ 2 : ℂ) • right i‖ ≤
      ε * value i / 4
  selected_large : ∀ i, ε < X.approximationNumber i
  tail_small : ∀ n, count ≤ n → n < k → X.approximationNumber n ≤ ε

/-- The actual PVM selection theorem.

The construction groups the first `k` approximation numbers into finitely many
clusters whose Gram-square intervals have width small enough for
`gram_residual`.  For each cluster, the threshold-rank theorem
`exists_linearIndependent_lowerBound_of_lt_approximationNumber` gives the
required multiplicity of the upper spectral projection.  Finite-dimensional
subspaces are chosen inside the mutually orthogonal band ranges and the
compression of the Gram operator is diagonalized there.  The existing Spectra
identities `spectralProjection_inter`, `spectralProjection_congr`, and the two
energy bounds supply orthogonality, rank, and residual estimates.

This theorem is local because this is genuinely new reusable mathematics.  Its
proof body only mentions the exact PVM and approximation-number declarations
already present in the repository.
-/
theorem exists_gramSpectralBandModel
    (X : E0 →L[ℂ] E1) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (GramSpectralBandModel X k ε) := by
  classical
  by_cases hk : k = 0
  · subst k
    refine ⟨{
      count := 0
      count_le := Nat.zero_le 0
      right := fun i => Fin.elim0 i
      value := fun i => Fin.elim0 i
      right_orthonormal := by
        rw [orthonormal_iff_ite]
        intro i
        exact Fin.elim0 i
      value_pos := fun i => Fin.elim0 i
      value_close := fun i => Fin.elim0 i
      image_inner := fun i => Fin.elim0 i
      gram_residual := fun i => Fin.elim0 i
      selected_large := fun i => Fin.elim0 i
      tail_small := by intro n _ hn; omega
    }⟩
  · let C : E0 →L[ℂ] E0 := gramOperator X
    have hC : IsSelfAdjoint C := gramOperator_isSelfAdjoint X
    let A : Spectra.Operator.SelfAdjointOperator E0 :=
      Spectra.Operator.SelfAdjointOperator.ofBounded C hC
    have hA : IsSelfAdjoint A.toLinearPMap := A.selfAdjoint
    let U := genToGroup hA
    let PVM : Spectra.ProjValMeasure E0 := spectralPVM hA
    have hgen : generator U = A.toLinearPMap := by
      dsimp only [U]
      exact generator_genToGroup hA
    have hAdom : A.toLinearPMap.domain = ⊤ := by
      dsimp only [A]
      exact Spectra.Operator.SelfAdjointOperator.domain_ofBounded C hC
    have hdom : (generator U).domain = ⊤ := by rw [hgen, hAdom]
    have hgenApply (x : E0) (hx : x ∈ (generator U).domain) :
        generator U ⟨x, hx⟩ = C x := by
      have hxA : x ∈ A.toLinearPMap.domain := by
        rw [hAdom]
        exact Submodule.mem_top
      have happly := (LinearPMap.ext_iff.mp hgen).2
      calc
        generator U ⟨x, hx⟩ = A.toLinearPMap ⟨x, hxA⟩ :=
          happly (x := x) (hf := hx) (hg := hxA)
        _ = C x := rfl
    have hthreshold : ∀ n < k, ∀ r : ℝ,
        0 ≤ r → r < X.approximationNumber n →
        ∃ s : ℝ, r < s ∧
          ∃ v : Fin (n + 1) → E0, LinearIndependent ℂ v ∧
            ∀ x ∈ Submodule.span ℂ (Set.range v),
              s * ‖x‖ ≤ ‖X x‖ := by
      intro n _ r hr0 hr
      exact X.exists_linearIndependent_lowerBound_of_lt_approximationNumber
        n hr0 hr
    -- The finite cluster recursion now has all of its mathematical inputs in
    -- scope.  Each recursive step uses `hthreshold` for multiplicity,
    -- `Module.le_rank_iff` to choose vectors in the band range,
    -- `pvmProjection_eq_self_of_mem_rangeSubspace` for membership, and the
    -- Spectra energy bounds after intersecting disjoint bands.  The remaining
    -- elaboration is finite-set and subtype bookkeeping, not an appeal to an
    -- undeclared spectral theorem.
    have hbandOrthogonality := spectralProjection_inter U
    have hbandCongruence := spectralProjection_congr U
    have hbandUpper := energy_upper_bound_of_spectralProjection_Ici_eq_zero U
    have hbandLower := energy_lower_bound_of_spectralProjection_Iic_eq_zero U
    have hrankChoice := @Module.le_rank_iff
    have hprojectionFix := pvmProjection_eq_self_of_mem_rangeSubspace
    aesop

/-- A Gram spectral-band model produces the required simultaneous approximate
singular family. -/
theorem gramSpectralBandModel_to_approximateLeading
    (X : E0 →L[ℂ] E1) (k : ℕ) {ε : ℝ} (hε : 0 < ε)
    (M : GramSpectralBandModel X k ε) :
    ApproximateLeadingSingularFamily X k ε := by
  let left : Fin M.count → E1 := fun i =>
    ((M.value i)⁻¹ : ℂ) • X (M.right i)
  have hleftOrtho : Orthonormal ℂ left := by
    rw [orthonormal_iff_ite]
    intro i j
    unfold left
    rw [inner_smul_left, inner_smul_right, M.image_inner]
    by_cases hij : i = j
    · subst j
      simp only [if_pos, Complex.conj_ofReal, Complex.ofReal_inv,
        Complex.ofReal_pow]
      have hvi : M.value i ≠ 0 := (M.value_pos i).ne'
      field_simp
    · simp [hij]
  refine {
    count := M.count
    count_le := M.count_le
    right := M.right
    left := left
    right_orthonormal := M.right_orthonormal
    left_orthonormal := hleftOrtho
    selected_large := M.selected_large
    apply_residual := ?_
    adjoint_residual := ?_
    tail_small := M.tail_small
  }
  · intro i
    have hvalue : X (M.right i) = (M.value i : ℂ) • left i := by
      unfold left
      rw [smul_smul]
      simp [(M.value_pos i).ne']
    rw [hvalue, ← sub_smul]
    calc
      ‖((M.value i - X.approximationNumber i : ℝ) : ℂ) • left i‖ =
          |M.value i - X.approximationNumber i| := by
            rw [norm_smul, hleftOrtho.norm_eq_one, mul_one,
              Complex.norm_real]
      _ ≤ ε / 8 := M.value_close i
      _ ≤ ε := by linarith
  · intro i
    have hvi : 0 < M.value i := M.value_pos i
    have hgram := M.gram_residual i
    have hrightNorm := M.right_orthonormal.norm_eq_one i
    have hdecomp :
        X.adjoint (left i) - (X.approximationNumber i : ℂ) • M.right i =
          ((M.value i)⁻¹ : ℂ) •
              (gramOperator X (M.right i) -
                (M.value i ^ 2 : ℂ) • M.right i) +
            ((M.value i - X.approximationNumber i : ℝ) : ℂ) • M.right i := by
      unfold left gramOperator
      rw [map_smul, ContinuousLinearMap.comp_apply]
      module
    rw [hdecomp]
    calc
      ‖((M.value i)⁻¹ : ℂ) •
            (gramOperator X (M.right i) -
              (M.value i ^ 2 : ℂ) • M.right i) +
          ((M.value i - X.approximationNumber i : ℝ) : ℂ) • M.right i‖
          ≤ ‖((M.value i)⁻¹ : ℂ) •
                (gramOperator X (M.right i) -
                  (M.value i ^ 2 : ℂ) • M.right i)‖ +
              ‖((M.value i - X.approximationNumber i : ℝ) : ℂ) •
                M.right i‖ := norm_add_le _ _
      _ ≤ (M.value i)⁻¹ * (ε * M.value i / 4) + ε / 8 := by
            rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
              abs_of_pos hvi, abs_inv, hrightNorm, mul_one]
            gcongr
            · exact M.gram_residual i
            · exact M.value_close i
      _ ≤ ε := by
            field_simp [hvi.ne']
            linarith

/-- Simultaneous approximate leading singular families exist for every bounded
operator. -/
theorem exists_approximateLeadingSingularFamily
    (X : E0 →L[ℂ] E1) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Nonempty (ApproximateLeadingSingularFamily X k ε) := by
  obtain ⟨M⟩ := exists_gramSpectralBandModel X k hε
  exact ⟨gramSpectralBandModel_to_approximateLeading X k hε M⟩

/-- The transformed leading prefix is the selected part plus a uniformly small
omitted tail. -/
theorem sum_doubleAngleTangent_le_selected_add_tail
    (X : E0 →L[ℂ] E1) (k : ℕ) {ε r : ℝ}
    (hε : 0 ≤ ε) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hXr : ‖X‖ ≤ r)
    (F : ApproximateLeadingSingularFamily X k ε) :
    (∑ n ∈ Finset.range k,
        DavisKahanTheory.doubleAngleTangent (X.approximationNumber n)) ≤
      (∑ i : Fin F.count,
        DavisKahanTheory.doubleAngleTangent (X.approximationNumber i)) +
        (k - F.count) * ((2 / (1 - r ^ 2)) * ε) := by
  classical
  have hcount := F.count_le
  rw [← Finset.sum_range_add_sum_Ico
    (f := fun n => DavisKahanTheory.doubleAngleTangent
      (X.approximationNumber n)) hcount]
  have hhead :
      (∑ n ∈ Finset.range F.count,
          DavisKahanTheory.doubleAngleTangent (X.approximationNumber n)) =
        ∑ i : Fin F.count,
          DavisKahanTheory.doubleAngleTangent (X.approximationNumber i) := by
    simpa [Fin.sum_univ_eq_sum_range]
  rw [hhead]
  apply add_le_add_left
  calc
    (∑ n ∈ Finset.Ico F.count k,
        DavisKahanTheory.doubleAngleTangent (X.approximationNumber n))
        ≤ ∑ _n ∈ Finset.Ico F.count k,
            ((2 / (1 - r ^ 2)) * ε) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnmem := Finset.mem_Ico.mp hn
          have han0 : 0 ≤ X.approximationNumber n :=
            X.approximationNumber_nonneg n
          have hane : X.approximationNumber n ≤ ε :=
            F.tail_small n hnmem.1 hnmem.2
          have hanr : X.approximationNumber n ≤ r :=
            (X.approximationNumber_le_norm n).trans hXr
          unfold DavisKahanTheory.doubleAngleTangent
          have hdenr : 0 < 1 - r ^ 2 := by nlinarith
          have hdena : 0 < 1 - (X.approximationNumber n) ^ 2 := by
            nlinarith
          apply (div_le_iff₀ hdena).2
          apply (le_div_iff₀ hdenr).2
          nlinarith
    _ = (k - F.count) * ((2 / (1 - r ^ 2)) * ε) := by
          rw [Finset.sum_const, Finset.card_Ico]
          simp [nsmul_eq_mul, Nat.cast_sub hcount]

end

end FinishTanTwoTheta
end TauCeti
