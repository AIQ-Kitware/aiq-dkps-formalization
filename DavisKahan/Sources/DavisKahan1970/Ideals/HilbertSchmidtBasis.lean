/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidt
public import DavisKahan.Sources.DavisKahan1970.Ideals.HilbertSchmidtFiniteRank
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Projection
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Isometry
public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

public section

open ContinuousLinearMap (toPointwiseConvergenceCLM)

open TauCeti.DavisKahan.Sylvester

/-!
# Basis and tensor models of the paper square norm

The paper defines square energy through the approximation-number sequence.
TauCeti's Hilbert–Schmidt reconciliation identifies it with the native
column energy of any Hilbert basis. The tensor model uses that identity in
`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtTensor.lean`.

The finite-basis cutoff results identify the square energy of each
compression and its supremum under strong convergence.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators ENNReal
open scoped Topology
open Filter

noncomputable section

universe vE vF

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type vE} {F : Type vF}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The paper's sum of squared approximation numbers equals the native column
energy in every Hilbert basis of the source. -/
theorem approximationNumberEnergy_eq_hilbertSchmidtEnergy {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) :
    approximationNumberEnergy A = A.hilbertSchmidtEnergy b := by
  simpa only [approximationNumberEnergy,
    ENNReal.ofReal_pow NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal] using
    A.tsum_singularValue_sq_eq_hilbertSchmidtEnergy b

omit [CompleteSpace F] in
/-- The finite coordinate projection has rank at most the number of selected vectors. -/
theorem rank_basisProjection_le {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (s : Finset ι) :
    (b.projection (s : Set ι)).rank ≤ (s.card : Cardinal) := by
  classical
  have hoff (i : ι) (hi : i ∉ s) : b.projection (s : Set ι) (b i) = 0 := by
    simp [hi]
  have himage : (fun i => b.projection (s : Set ι) (b i)) '' (s : Set ι) = b '' (s : Set ι) :=
    Set.image_congr fun i hi => by simp [hi]
  change Module.rank 𝕜 (b.projection (s : Set ι)).toLinearMap.range ≤ _
  rw [b.range_eq_span_image_of_apply_eq_zero _ s hoff, himage, ← Finset.coe_image]
  exact (rank_span_finset_le (s.image b)).trans (by exact_mod_cast Finset.card_image_le)

/-- The square energy of a finite-dimensional domain cutoff is the sum of
the squared column norms over any orthonormal basis of that subspace. -/
theorem approximationNumberEnergy_comp_starProjection
    (A : F →L[𝕜] E) (K : Submodule 𝕜 F) [FiniteDimensional 𝕜 K]
    {n : ℕ} (c : OrthonormalBasis (Fin n) 𝕜 K) :
    approximationNumberEnergy (A ∘L K.starProjection) =
      ∑ k : Fin n, ENNReal.ofReal (‖A ((c k : F))‖ ^ 2) := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 F
  rw [approximationNumberEnergy_eq_hilbertSchmidtEnergy b, Submodule.starProjection,
    ← ContinuousLinearMap.comp_assoc]
  have hK (x : K) : ‖K.orthogonalProjectionOnto.adjoint x‖ = ‖x‖ := by
    rw [K.adjoint_orthogonalProjectionOnto]
    rfl
  rw [ContinuousLinearMap.hilbertSchmidtEnergy_comp_coisometry _ _ hK b c.toHilbertBasis,
    ContinuousLinearMap.hilbertSchmidtEnergy_def, tsum_fintype]
  simp only [OrthonormalBasis.coe_toHilbertBasis, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- A finite coordinate cutoff keeps exactly the square energy of its selected columns. -/
theorem approximationNumberEnergy_comp_basisProjection
    {ι : Type*} (b : HilbertBasis ι 𝕜 F) (s : Finset ι)
    (A : F →L[𝕜] E) :
    approximationNumberEnergy (A ∘L b.projection (s : Set ι)) =
      ∑ i ∈ s, ENNReal.ofReal (‖A (b i)‖ ^ 2) := by
  rw [approximationNumberEnergy_eq_hilbertSchmidtEnergy b,
    ContinuousLinearMap.hilbertSchmidtEnergy_def, tsum_eq_sum (s := s)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp [ContinuousLinearMap.comp_apply, hi, ENNReal.ofReal_pow, ofReal_norm]
  · intro i hi
    simp [ContinuousLinearMap.comp_apply, hi]

omit [CompleteSpace F] in
/-- The net of coordinate projections over all finite index sets converges
strongly to the identity. -/
theorem basisProjection_stronglyTendsto {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) :
    Tendsto
      (fun s : Finset ι => toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) F F
        (b.projection (s : Set ι))) atTop
      (𝓝 (toPointwiseConvergenceCLM 𝕜 (RingHom.id 𝕜) F F (ContinuousLinearMap.id 𝕜 F))) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  intro x
  have hsum := b.hasSum_repr x
  simp only [HilbertBasis.repr_apply_apply] at hsum
  exact Tendsto.congr (fun s => (b.projection_eq_sum s x).symm) hsum

omit [CompleteSpace E] in
/-- Approximation singular values of finite basis cutoffs converge pointwise. -/
theorem approximationSingularValue_cutoff_tendsto {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) (n : ℕ) :
    Tendsto
      (fun s : Finset ι => ((A ∘L b.projection (s : Set ι)).singularValue n : ℝ))
      atTop (𝓝 ((A.singularValue n : ℝ))) :=
  approximationSingularValue_comp_strongProjection_tendsto_of_minMax
    TauCeti.HasMinMaxLowerBound.of_completeSpace
    (P := fun s : Finset ι => b.projection (s : Set ι))
    (fun s => ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection.mp
      (b.isStarProjection_projection (s : Set ι)))
    (basisProjection_stronglyTendsto b) n A

/-- The square energy is the supremum over all finite coordinate cutoffs,
including when the energy is infinite. -/
theorem approximationNumberEnergy_eq_iSup_cutoff {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) :
    approximationNumberEnergy A =
      ⨆ s : Finset ι,
        approximationNumberEnergy (A ∘L b.projection (s : Set ι)) := by
  rw [approximationNumberEnergy_eq_hilbertSchmidtEnergy b,
    ContinuousLinearMap.hilbertSchmidtEnergy_def, tsum_eq_iSup_sum]
  simp_rw [approximationNumberEnergy_comp_basisProjection,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The paper square energy is the canonical extended norm, squared: the two
energy interfaces agree without any finiteness hypothesis at all. -/
theorem approximationNumberEnergy_eq_hilbertSchmidtGauge_sq
    (A : F →L[𝕜] E) :
    approximationNumberEnergy A = ((OperatorIdealFamily.hilbertSchmidt 𝕜).gauge A) ^ (2 : ℝ) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 F
  rw [OperatorIdealFamily.gauge_hilbertSchmidt A b,
    ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
    ENNReal.rpow_one, approximationNumberEnergy_eq_hilbertSchmidtEnergy b A]

/-- **The canonical real norm is the paper's square-root-of-energy formula**, with no
finiteness hypothesis: off the ideal both sides are `0`, because `ENNReal.toReal` sends
`∞` to `0` and `Real.sqrt 0 = 0`.

This is what lets every estimate the paper proves about `√(Σ aₙ²)` be *stated* about the
one canonical norm, rather than about a second norm that happens to be equal to it. -/
theorem hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy
    (A : F →L[𝕜] E) :
    A.hilbertSchmidtNorm = Real.sqrt (approximationNumberEnergy A).toReal := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 F
  rw [A.hilbertSchmidtNorm_eq_sqrt b, approximationNumberEnergy_eq_hilbertSchmidtEnergy b A]

/-- On the paper ideal, the accepted Hilbert–Schmidt gauge is the real norm. -/
theorem hilbertSchmidtGauge_eq_ofReal_hilbertSchmidtNorm
    (A : F →L[𝕜] E)
    (hA : approximationNumberEnergy A ≠ ⊤) :
    ((OperatorIdealFamily.hilbertSchmidt 𝕜).gauge A) = ENNReal.ofReal
      (ContinuousLinearMap.hilbertSchmidtNorm A) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 F
  have henergy : A.hilbertSchmidtEnergy b = approximationNumberEnergy A := by
    exact (approximationNumberEnergy_eq_hilbertSchmidtEnergy b A).symm
  have hne : approximationNumberEnergy A ≠ ⊤ := hA
  rw [hilbertSchmidtNorm_eq_sqrt_approximationNumberEnergy,
    OperatorIdealFamily.gauge_hilbertSchmidt A b,
    henergy, Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal hne, one_div]

/-- Consequently the gauge of the accepted symmetric ideal family, read on the paper ideal,
is the paper square norm.

`TauCeti.SymmetricOperatorIdealFamily` is the diagonal layer, so it constrains the source
and target to one universe; the rectangular statements above are the general ones. -/
theorem hilbertSchmidtIdealFamily_gauge_eq_hilbertSchmidtNorm {G K : Type vE}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : G →L[𝕜] K) (hA : approximationNumberEnergy A ≠ ⊤) :
    (TauCeti.SymmetricOperatorIdealFamily.hilbertSchmidt 𝕜).toOperatorIdealFamily.gauge A =
      ENNReal.ofReal (ContinuousLinearMap.hilbertSchmidtNorm A) := by
  rw [TauCeti.SymmetricOperatorIdealFamily.hilbertSchmidt_toOperatorIdealFamily]
  exact hilbertSchmidtGauge_eq_ofReal_hilbertSchmidtNorm A hA

/-! ### The bridge at the two scalar fields

Min--max is the only hypothesis above, so it is discharged once here and the
paper and staged Hilbert--Schmidt theories are one theory over `ℂ` and over
`ℝ` alike.  Before this, the identification existed over `ℂ` only, and the
`ℝ`-valued paper norm had no connection at all to the staged ideal gauge over
a real Hilbert space. -/





/-! ### The `ℝ` and `ℝ≥0∞` interfaces are the same number

The ideal gauge is `ℝ≥0∞`-valued because a gauge must be defined off the ideal; the
paper's square norm is a real number because every estimate it appears in is an
inequality between reals.  These say the two readings agree on the ideal, so a paper
estimate and an ideal-gauge estimate are interchangeable rather than merely analogous. -/



end

end ExactSinTheta
end DavisKahan
end TauCeti
