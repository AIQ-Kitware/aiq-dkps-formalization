/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import DavisKahan.Sources.DavisKahan1970.SineTheta.AngleIdentity
import DavisKahan.Sources.DavisKahan1970.SineTheta.FullAngleReal
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport
import DavisKahan.Geometry.Angle.OperatorAngleGeneric
import DavisKahan.SpectralTheory.OperatorAngle
import DavisKahan.SpectralTheory.Complexification.Subspace

/-!
# Presentation bridges for the full Davis--Kahan operator angle

Davis--Kahan define the ambient angle by the literal block diagonal operator

`Theta = diag (Theta_0, Theta_1)`.

The proof API often replaces its largest angle by
`maximalAngle U V = arcsin (projectionGap U V)`.  This file proves that
replacement rather than treating it as notation: the operator norm of the
literal source block angle is exactly `maximalAngle`.  Thus Section 8 can state
its quarter-angle conditions directly on the source `Theta`, while retaining
`maximalAngle` as the convenient proof representative.

The same calculation also identifies the norm of the modern intrinsic ambient
`Angle.angleOperator` with the literal source block angle.  The two operators
live on different coordinate Hilbert spaces, so literal equality is not the
well-typed correspondence; equality of their exact maximal-angle norm is the
coordinate-independent statement consumed by Section 8.
-/

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open TauCeti.DavisKahanExt

noncomputable section

universe v

private theorem norm_cfc_arcsin_of_nonneg
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : G →L[ℂ] G) (hA : 0 ≤ A) :
    ‖cfc Real.arcsin A‖ = Real.arcsin ‖A‖ := by
  rcases subsingleton_or_nontrivial G with hG | hG
  · letI := hG
    have hAzero : A = 0 := Subsingleton.elim _ _
    have hcfcZero : cfc Real.arcsin A = 0 := Subsingleton.elim _ _
    rw [hcfcZero, norm_zero, hAzero, norm_zero, Real.arcsin_zero]
  · letI := hG
    apply le_antisymm
    · refine norm_cfc_le (Real.arcsin_nonneg.mpr (norm_nonneg A)) ?_
      intro t ht
      have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg hA ht
      have hnormC : ‖((t : ℂ))‖ ≤ ‖A‖ * ‖(1 : G →L[ℂ] G)‖ :=
        spectrum.norm_le_norm_mul_of_mem ht
      have hnorm : |t| ≤ ‖A‖ * ‖(1 : G →L[ℂ] G)‖ := by
        simpa using hnormC
      have habs : |t| ≤ ‖A‖ := by
        calc
          |t| ≤ ‖A‖ * ‖(1 : G →L[ℂ] G)‖ := hnorm
          _ ≤ ‖A‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg A)
          _ = ‖A‖ := mul_one _
      have htle : t ≤ ‖A‖ := (le_abs_self t).trans habs
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.arcsin_nonneg.mpr ht0)]
      exact Real.arcsin_le_arcsin htle
    · have hmem : (‖A‖ : ℝ) ∈ spectrum ℝ A :=
        CStarAlgebra.norm_mem_spectrum_of_nonneg (a := A) hA
      have hlow := norm_apply_le_norm_cfc Real.arcsin A hmem
      have hnonneg : 0 ≤ Real.arcsin ‖A‖ :=
        Real.arcsin_nonneg.mpr (norm_nonneg A)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hlow

private theorem spectrum_subset_Iic_iff_norm_le_of_nonneg
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : G →L[ℂ] G) (hA : 0 ≤ A) {c : ℝ} (hc : 0 ≤ c) :
    spectrum ℝ A ⊆ Set.Iic c ↔ ‖A‖ ≤ c := by
  constructor
  · intro hspec
    rcases subsingleton_or_nontrivial G with hG | hG
    · letI := hG
      have hAzero : A = 0 := Subsingleton.elim _ _
      simpa [hAzero] using hc
    · letI := hG
      exact hspec (CStarAlgebra.norm_mem_spectrum_of_nonneg (a := A) hA)
  · intro hnorm t ht
    have hnormC : ‖((t : ℂ))‖ ≤ ‖A‖ * ‖(1 : G →L[ℂ] G)‖ :=
      spectrum.norm_le_norm_mul_of_mem ht
    have habs0 : |t| ≤ ‖A‖ * ‖(1 : G →L[ℂ] G)‖ := by
      simpa using hnormC
    have habs : |t| ≤ ‖A‖ := by
      calc
        |t| ≤ ‖A‖ * ‖(1 : G →L[ℂ] G)‖ := habs0
        _ ≤ ‖A‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg A)
        _ = ‖A‖ := mul_one _
    exact (le_abs_self t).trans (habs.trans hnorm)

private theorem spectrum_subset_Iio_iff_norm_lt_of_nonneg
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : G →L[ℂ] G) (hA : 0 ≤ A) {c : ℝ} (hc : 0 < c) :
    spectrum ℝ A ⊆ Set.Iio c ↔ ‖A‖ < c := by
  constructor
  · intro hspec
    rcases subsingleton_or_nontrivial G with hG | hG
    · letI := hG
      have hAzero : A = 0 := Subsingleton.elim _ _
      simpa [hAzero] using hc
    · letI := hG
      exact hspec (CStarAlgebra.norm_mem_spectrum_of_nonneg (a := A) hA)
  · intro hnorm t ht
    have hnormC : ‖((t : ℂ))‖ ≤ ‖A‖ * ‖(1 : G →L[ℂ] G)‖ :=
      spectrum.norm_le_norm_mul_of_mem ht
    have habs0 : |t| ≤ ‖A‖ * ‖(1 : G →L[ℂ] G)‖ := by
      simpa using hnormC
    have habs : |t| ≤ ‖A‖ := by
      calc
        |t| ≤ ‖A‖ * ‖(1 : G →L[ℂ] G)‖ := habs0
        _ ≤ ‖A‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg A)
        _ = ‖A‖ := mul_one _
    exact (le_abs_self t).trans_lt (habs.trans_lt hnorm)

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Local C-star algebra instance for the source coordinate subspaces.  The
functional-calculus search does not always discover this submodule-shaped
instance automatically. -/
noncomputable local instance instCStarAlgebraSubspaceCoordinateFullAnglePresentation
    {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] :
    CStarAlgebra (↥U →L[ℂ] ↥U) :=
  inferInstance

private theorem subtype_comp_adjoint_subtype
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] :
    W.subtypeL ∘L W.subtypeL.adjoint = W.starProjection := by
  rw [Submodule.adjoint_subtypeL]
  rfl

/-- The source sine block has operator norm equal to the directed projection gap. -/
theorem norm_sineBlockC_eq_directedProjectionGap
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sineBlockC U V‖ = U.directedProjectionGap V := by
  have hseq := sameApproximationSingularValues_ambientSubspaceBlock
    U Vᗮ (sineBlockC U V)
  have h0 := hseq 0
  rw [ContinuousLinearMap.approximationNumber_index_zero,
    ContinuousLinearMap.approximationNumber_index_zero] at h0
  have hamb :
      Vᗮ.subtypeL ∘L sineBlockC U V ∘L U.subtypeL.adjoint =
        Vᗮ.starProjection ∘L U.starProjection := by
    rw [sineBlockC]
    have hV :
        Vᗮ.subtypeL ∘L Vᗮ.subtypeL.adjoint = Vᗮ.starProjection :=
      subtype_comp_adjoint_subtype Vᗮ
    have hU :
        U.subtypeL ∘L U.subtypeL.adjoint = U.starProjection :=
      subtype_comp_adjoint_subtype U
    calc
      (Vᗮ.subtypeL ∘L Vᗮ.subtypeL.adjoint ∘L U.subtypeL) ∘L
          U.subtypeL.adjoint =
          (Vᗮ.subtypeL ∘L Vᗮ.subtypeL.adjoint) ∘L
            (U.subtypeL ∘L U.subtypeL.adjoint) := by
        ext x
        rfl
      _ = Vᗮ.starProjection ∘L U.starProjection := by rw [hV, hU]
  rw [hamb] at h0
  simpa [Submodule.directedProjectionGap] using h0.symm

/-- The source positive sine modulus has the same norm as the directed gap. -/
theorem norm_sineBlockModulusC_eq_directedProjectionGap
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sineBlockModulusC U V‖ = U.directedProjectionGap V := by
  rw [sineBlockModulusC, ContinuousLinearMap.norm_modulus,
    norm_sineBlockC_eq_directedProjectionGap]

/-- The norm of the source cosine-defined directed angle is the arcsine of the
corresponding directed projection gap. -/
theorem norm_directedAngleBlockC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖directedAngleBlockC U V‖ = Real.arcsin (U.directedProjectionGap V) := by
  rw [← sineDefinedDirectedAngleC_eq_directedAngleBlockC U V,
    sineDefinedDirectedAngleC,
    norm_cfc_arcsin_of_nonneg (sineBlockModulusC U V)
      (ContinuousLinearMap.modulus_nonneg _),
    norm_sineBlockModulusC_eq_directedProjectionGap]

/-- Orthogonal complementation swaps the orientation of the directed gap. -/
theorem directedProjectionGap_orthogonal
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Uᗮ.directedProjectionGap Vᗮ = V.directedProjectionGap U := by
  rw [Submodule.directedProjectionGap, Submodule.directedProjectionGap]
  have hdouble : Vᗮᗮ.starProjection = V.starProjection := by
    calc
      Vᗮᗮ.starProjection = (1 : E →L[ℂ] E) - Vᗮ.starProjection :=
        Submodule.starProjection_orthogonal' Vᗮ
      _ = (1 : E →L[ℂ] E) - ((1 : E →L[ℂ] E) - V.starProjection) := by
        rw [Submodule.starProjection_orthogonal' V]
      _ = V.starProjection := by module
  rw [hdouble]
  let T : E →L[ℂ] E := V.starProjection ∘L Uᗮ.starProjection
  have hadj : T.adjoint = Uᗮ.starProjection ∘L V.starProjection := by
    rw [show T = V.starProjection ∘L Uᗮ.starProjection from rfl,
      ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection V).adjoint_eq,
      (isSelfAdjoint_starProjection Uᗮ).adjoint_eq]
  have h := ContinuousLinearMap.approximationNumber_adjoint T 0
  rw [ContinuousLinearMap.approximationNumber_index_zero,
    ContinuousLinearMap.approximationNumber_index_zero, hadj] at h
  exact h.symm

/-- The source cosine-defined directed angle is a positive operator. -/
theorem directedAngleBlockC_nonneg
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ directedAngleBlockC U V := by
  rw [← sineDefinedDirectedAngleC_eq_directedAngleBlockC U V,
    sineDefinedDirectedAngleC]
  apply cfc_nonneg
  intro t ht
  exact Real.arcsin_nonneg.mpr
    (spectrum_nonneg_of_nonneg (ContinuousLinearMap.modulus_nonneg _) ht)

/-- The literal source full angle `Theta = diag(Theta_0,Theta_1)` is positive. -/
theorem fullAngleBlockC_nonneg
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ fullAngleBlockC U V := by
  rw [fullAngleBlockC, ContinuousLinearMap.nonneg_iff_isPositive]
  exact continuousOrthogonalBlockSum_isPositive
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (directedAngleBlockC_nonneg U V))
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (directedAngleBlockC_nonneg Uᗮ Vᗮ))

/-- Closed source-angle comparison `Theta ≤ c`, represented directly as the
real spectrum of the literal positive operator `Theta` lying in `(-∞, c]`.
For a self-adjoint operator this is exactly the spectral-order meaning of the
paper's operator inequality. -/
noncomputable def sourceFullAngleLeC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (c : ℝ) : Prop :=
  spectrum ℝ (fullAngleBlockC U V) ⊆ Set.Iic c

/-- Strict source-angle comparison `Theta < c`, stated directly as every
spectral angle of the literal source operator lying below `c`. -/
noncomputable def sourceFullAngleLtC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (c : ℝ) : Prop :=
  spectrum ℝ (fullAngleBlockC U V) ⊆ Set.Iio c

/-- The direct closed source-angle condition is equivalent to the norm bound
used by the proof API. -/
theorem sourceFullAngleLeC_iff_norm_le
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c : ℝ} (hc : 0 ≤ c) :
    sourceFullAngleLeC U V c ↔ ‖fullAngleBlockC U V‖ ≤ c := by
  exact spectrum_subset_Iic_iff_norm_le_of_nonneg
    (fullAngleBlockC U V) (fullAngleBlockC_nonneg U V) hc

/-- The direct strict source-angle condition is equivalent to the strict norm
bound used by the proof API. -/
theorem sourceFullAngleLtC_iff_norm_lt
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c : ℝ} (hc : 0 < c) :
    sourceFullAngleLtC U V c ↔ ‖fullAngleBlockC U V‖ < c := by
  exact spectrum_subset_Iio_iff_norm_lt_of_nonneg
    (fullAngleBlockC U V) (fullAngleBlockC_nonneg U V) hc

/-- **The operator norm of the literal source full angle is the maximal angle.**

This is the exact bridge used by the Section 8 presentation layer. -/
theorem norm_fullAngleBlockC_eq_maximalAngle
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖fullAngleBlockC U V‖ = maximalAngle U V := by
  rw [fullAngleBlockC, norm_continuousOrthogonalBlockSum,
    norm_directedAngleBlockC U V,
    norm_directedAngleBlockC Uᗮ Vᗮ,
    directedProjectionGap_orthogonal U V,
    maximalAngle,
    Submodule.projectionGap_eq_max_directedProjectionGap]
  rcases le_total (U.directedProjectionGap V) (V.directedProjectionGap U) with h | h
  · rw [max_eq_right h, max_eq_right (Real.arcsin_le_arcsin h)]
  · rw [max_eq_left h, max_eq_left (Real.arcsin_le_arcsin h)]

/-- Direct closed source-angle comparison, transported to the scalar proof API. -/
theorem sourceFullAngleLeC_iff_maximalAngle_le
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c : ℝ} (hc : 0 ≤ c) :
    sourceFullAngleLeC U V c ↔ maximalAngle U V ≤ c := by
  rw [sourceFullAngleLeC_iff_norm_le U V hc, norm_fullAngleBlockC_eq_maximalAngle]

/-- Direct strict source-angle comparison, transported to the scalar proof API. -/
theorem sourceFullAngleLtC_iff_maximalAngle_lt
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c : ℝ} (hc : 0 < c) :
    sourceFullAngleLtC U V c ↔ maximalAngle U V < c := by
  rw [sourceFullAngleLtC_iff_norm_lt U V hc, norm_fullAngleBlockC_eq_maximalAngle]

/-- The modern intrinsic ambient angle and the literal source block angle have
exactly the same maximal angle.  They live on different coordinate spaces, so
norm equality is the well-typed coordinate-independent bridge needed by the
Section 8 inequalities. -/
theorem norm_fullAngleBlockC_eq_angleOperator
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖fullAngleBlockC U V‖ = ‖Angle.angleOperator U V‖ := by
  rw [norm_fullAngleBlockC_eq_maximalAngle, maximalAngle, Angle.angleOperator,
    norm_cfc_arcsin_of_nonneg (Angle.sinAngleOperator U V)
      (Angle.sinAngleOperator_nonneg U V),
    Angle.norm_sinAngleOperator]


/-- The modern intrinsic ambient angle is positive.  This local presentation
lemma records the order fact needed to compare it directly with the source
block angle. -/
theorem intrinsicAngleOperator_nonnegC
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ Angle.angleOperator U V := by
  rw [Angle.angleOperator]
  apply cfc_nonneg
  intro t ht
  exact Real.arcsin_nonneg.mpr
    (spectrum_nonneg_of_nonneg (Angle.sinAngleOperator_nonneg U V) ht)

/-- **The literal Davis--Kahan full angle and the intrinsic ambient angle have
the same closed upper-angle comparisons.**

The operators live on different coordinate Hilbert spaces, so raw equality is
ill-typed.  This theorem is the direct, proved replacement for silently
identifying them in statements such as `Theta ≤ c`. -/
theorem sourceFullAngleLeC_iff_intrinsicAngle_spectrum_le
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c : ℝ} (hc : 0 ≤ c) :
    sourceFullAngleLeC U V c ↔
      spectrum ℝ (Angle.angleOperator U V) ⊆ Set.Iic c := by
  rw [sourceFullAngleLeC_iff_norm_le U V hc,
    spectrum_subset_Iic_iff_norm_le_of_nonneg
      (Angle.angleOperator U V) (intrinsicAngleOperator_nonnegC U V) hc,
    norm_fullAngleBlockC_eq_angleOperator]

/-- **The literal source full angle and the intrinsic ambient angle have the
same strict upper-angle comparisons.** -/
theorem sourceFullAngleLtC_iff_intrinsicAngle_spectrum_lt
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c : ℝ} (hc : 0 < c) :
    sourceFullAngleLtC U V c ↔
      spectrum ℝ (Angle.angleOperator U V) ⊆ Set.Iio c := by
  rw [sourceFullAngleLtC_iff_norm_lt U V hc,
    spectrum_subset_Iio_iff_norm_lt_of_nonneg
      (Angle.angleOperator U V) (intrinsicAngleOperator_nonnegC U V) hc,
    norm_fullAngleBlockC_eq_angleOperator]

section Real

variable {F : Type v}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Real source full angle: its norm is exactly the scalar maximal angle. -/
theorem norm_sourceFullAngleR_eq_maximalAngle
    (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖sourceFullAngleR U V‖ = maximalAngle U V := by
  rw [sourceFullAngleR,
    norm_fullAngleBlockC_eq_maximalAngle,
    maximalAngle, maximalAngle,
    projectionGap_complexifySubmodule]

/-- Closed spectral-order comparison on the literal real source full angle.
The real source angle is defined by canonical complexification, so reuse the
complex source predicate on exactly those complexified subspaces.  This avoids
introducing a second, definitionally equal real-algebra instance for the same
complexified block space. -/
noncomputable def sourceFullAngleLeR
    (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (c : ℝ) : Prop :=
  sourceFullAngleLeC (complexifySubmodule U) (complexifySubmodule V) c

/-- Strict spectral comparison on the literal real source full angle. -/
noncomputable def sourceFullAngleLtR
    (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (c : ℝ) : Prop :=
  sourceFullAngleLtC (complexifySubmodule U) (complexifySubmodule V) c

/-- The direct real closed source-angle condition is exactly the scalar
`maximalAngle` bound used by the proof API. -/
theorem sourceFullAngleLeR_iff_maximalAngle_le
    (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c : ℝ} (hc : 0 ≤ c) :
    sourceFullAngleLeR U V c ↔ maximalAngle U V ≤ c := by
  rw [sourceFullAngleLeR,
    sourceFullAngleLeC_iff_maximalAngle_le (complexifySubmodule U)
      (complexifySubmodule V) hc]
  simp only [maximalAngle, projectionGap_complexifySubmodule]

/-- The direct real strict source-angle condition is exactly the scalar
`maximalAngle` bound used by the proof API. -/
theorem sourceFullAngleLtR_iff_maximalAngle_lt
    (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {c : ℝ} (hc : 0 < c) :
    sourceFullAngleLtR U V c ↔ maximalAngle U V < c := by
  rw [sourceFullAngleLtR,
    sourceFullAngleLtC_iff_maximalAngle_lt (complexifySubmodule U)
      (complexifySubmodule V) hc]
  simp only [maximalAngle, projectionGap_complexifySubmodule]

end Real

end

end ExactSinTheta
end DavisKahan
end TauCeti
