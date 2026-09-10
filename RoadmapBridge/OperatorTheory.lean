/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Rank
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional
import ForTauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge
import ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.RealLowerBound
import ForTauCeti.Analysis.InnerProductSpace.OneParameterUnitaryGroup.SemigroupBridge
import ForTauCeti.Analysis.Matrix.SpectralProjection
import ForTauCeti.Analysis.Matrix.EntrywiseEigenvalue

/-! # Operator-theory signature regressions

These examples exercise the revised roadmap's assumptions, not name matching.
The rank characterization needs no inner product; truncation needs no monotonicity;
rectangular families retain independent universes; point gaps supply invariance;
and real-shift resolvents provide membership and the inverse-norm estimate together.
The matrix examples include a threshold equal to an eigenvalue and do not exclude
zero-dimensional spaces. Compilation, not the presence of these examples, is the test.
-/

namespace RoadmapBridge.OperatorTheory

open TauCeti
open scoped BigOperators ENNReal InnerProductSpace Matrix

universe u v w

section Rank

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n = 0 ↔ T.rank ≤ (n : Cardinal) :=
  T.approximationNumber_eq_zero_iff_rank_le n

end Rank

section Gauges

example (Phi : SymmetricGauge) (a : ℕ → NNReal) :
    Phi.extend (fun n => (a n : ENNReal)) =
      ⨆ N : ℕ, (Phi (SymmetricGauge.truncate a N) : ENNReal) :=
  Phi.extend_eq_iSup_truncate a

example (Phi : SymmetricGauge) {a b : ℕ → ENNReal} (ha : Antitone a)
    (h : ∀ k, ∑ n ∈ Finset.range k, a n ≤ ∑ n ∈ Finset.range k, b n) :
    Phi.extend a ≤ Phi.extend b :=
  Phi.extend_le_extend_of_forall_sum_le ha h

variable {𝕜 : Type u} [RCLike 𝕜]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

noncomputable example (Phi : SymmetricGauge) : OperatorIdealFamily.{u, v, w} 𝕜 :=
  symmetricGaugeFamily 𝕜 Phi

example (Phi : SymmetricGauge) (T : E →L[𝕜] F) :
    (symmetricGaugeFamily.{u, w, v} 𝕜 Phi).gauge T.adjoint =
      (symmetricGaugeFamily.{u, v, w} 𝕜 Phi).gauge T :=
  gauge_adjoint_symmetricGaugeFamily Phi T

example (Phi : SymmetricGauge) : IsKyFanDominant (symmetricGaugeFamily.{u, v, w} 𝕜 Phi) :=
  inferInstance

example (p : ℝ) (hp : 1 ≤ p) : (schattenFamily.{u, v, w} 𝕜 p hp).IsComplete :=
  isComplete_schattenFamily hp

example : schattenFamilyInf.{u, v, w} 𝕜 = operatorNormIdealFamily.{u, v, w} 𝕜 :=
  schattenFamilyInf_eq_operatorNormIdealFamily 𝕜

example [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (T : E →L[𝕜] F) (n : ℕ) :
    T.singularValues n = 0 ↔ T.rank ≤ (n : Cardinal) :=
  T.singularValues_eq_zero_iff_rank_le n

end Gauges

section PointGaps

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

example {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} {δ : ℝ}
    (hgap : PointInternalGap A U δ) : IsInvariant A U := hgap.1

example {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} {δ c : ℝ} (hgap : PointInternalGap A U δ)
    (hspec : PointSpectrumIn A U (Set.Iic c)) :
    ∀ x ∈ U, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
  upperFormBound_of_pointSpectrumIn hA hgap.1 hspec

example {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} {δ c : ℝ} (hgap : PointInternalGap A U δ)
    (hspec : PointSpectrumIn A U (Set.Ici c)) :
    ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜 :=
  lowerFormBound_of_pointSpectrumIn hA hgap.1 hspec

end PointGaps

section Resolvents

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

example {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) {z c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : A.domain,
      c * ‖(x : E)‖ ≤ ‖A x - (z : 𝕜) • (x : E)‖) :
    (z : 𝕜) ∈ TauCeti.LinearPMap.resolventSet A ∧
      ‖TauCeti.LinearPMap.resolvent A (z : 𝕜)‖ ≤ c⁻¹ :=
  TauCeti.LinearPMap.mem_resolventSet_and_norm_le_of_lower_bound hA hc hbound

end Resolvents

section Groups

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

example (U : OneParameterUnitaryGroup H) (t : NNReal) : ‖U.toSemigroup t‖ ≤ 1 :=
  U.norm_toSemigroup_le t

end Groups

section Matrices

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

example {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (c : ℝ) (i : Fin n)
    (hi : hA.eigenvalues i = c) :
    (TauCeti.Matrix.spectralProjectionIci c A hA) *ᵥ
        (fun j => (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) j i) =
      (fun j => (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) j i) :=
  TauCeti.Matrix.spectralProjectionIci_mulVec_of_eigenvalue_eq c hA i hi

example (c : ℝ) :
    Measurable fun A : {A : Matrix (Fin n) (Fin n) 𝕜 // A.IsHermitian} =>
      TauCeti.Matrix.spectralProjectionIci c A.1 A.2 :=
  TauCeti.Matrix.measurable_spectralProjectionIci c

example {A B : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {e : ℝ} (he : ∀ i j, ‖B i j - A i j‖ ≤ e)
    (k : Fin (Fintype.card (Fin n))) :
    |hB.eigenvalues₀ k - hA.eigenvalues₀ k| ≤ (n : ℝ) * e :=
  TauCeti.Matrix.abs_eigenvalues₀_sub_le_of_entry_le hA hB he k

end Matrices

end RoadmapBridge.OperatorTheory
