/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import DavisKahan.Sylvester.PairwiseSpectrumGap
public import DavisKahan.Sylvester.ClosedSylvesterEquation
public import DavisKahan.SpectralTheory.PartialMap.RealSpectrum
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Rosenblum

/-!
# Homogeneous Sylvester uniqueness at arbitrary spectral separation

A domain-aware closed Sylvester equation says exactly that its solution
intertwines the two operators, and Rosenblum's theorem then forces a bounded
intertwiner of disjoint spectra to vanish.  Unlike the older uniqueness lemma,
no interval/exterior or ordered half-line geometry is required.

The domain-aware equation uses Tau Ceti's `LinearPMap.SylvesterEquation`.
The zero-defect equivalence gives `LinearPMap.Intertwines`, and
`LinearPMap.Intertwines.eq_zero_of_disjoint_spectrum` gives uniqueness.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A bounded homogeneous Sylvester solution for raw self-adjoint partial maps
vanishes whenever their spectra are disjoint. -/
theorem Sylvester_homogeneous_eq_zero_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E}
    (hdisj : Disjoint
      (_root_.LinearPMap.spectrum A)
      (_root_.LinearPMap.spectrum B))
    (hEq : _root_.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  have hIntertwines := _root_.LinearPMap.sylvesterEquation_zero_iff_intertwines.mp hEq
  exact hIntertwines.eq_zero_of_disjoint_spectrum hB hA hdisj.symm

/-- Positive pairwise spectral distance gives homogeneous uniqueness for raw
self-adjoint partial maps. -/
theorem Sylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : LinearPMap.PairwiseSpectrumGap A B δ)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  exact Sylvester_homogeneous_eq_zero_of_disjoint_spectrum
    hA hB (hgap.disjoint hδ) hEq

/-- **Sylvester--Rosenblum uniqueness for raw self-adjoint partial maps.**  Two bounded
solutions of the same Sylvester equation coincide as soon as the two spectra are
*disjoint*; no quantitative gap is needed.

The gap version below is this statement composed with
`PairwiseSpectrumGap.disjoint`, so a positive separation buys nothing here — it is
needed only where a *bound* on the solution is wanted. -/
theorem Sylvester_solution_unique_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E}
    (hdisj : Disjoint
      (_root_.LinearPMap.spectrum A)
      (_root_.LinearPMap.spectrum B))
    (hX : _root_.LinearPMap.SylvesterEquation A B X C)
    (hY : _root_.LinearPMap.SylvesterEquation A B Y C) :
    X = Y :=
  hX.eq_of_disjoint_spectrum hY hA hB hdisj

/-- Two bounded raw partial-map Sylvester solutions coincide under positive
pairwise spectral separation.  A corollary of
`Sylvester_solution_unique_of_disjoint_spectrum`, which is the sharp form. -/
theorem Sylvester_solution_unique_of_pairwiseSpectrumGap
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : LinearPMap.PairwiseSpectrumGap A B δ)
    (hX : _root_.LinearPMap.SylvesterEquation A B X C)
    (hY : _root_.LinearPMap.SylvesterEquation A B Y C) :
    X = Y :=
  Sylvester_solution_unique_of_disjoint_spectrum hA hB (hgap.disjoint hδ) hX hY

/-- A bounded homogeneous closed Sylvester solution vanishes whenever the two
self-adjoint spectra are disjoint. -/
theorem closedSylvester_homogeneous_eq_zero_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E}
    (hdisj : Disjoint
      (_root_.LinearPMap.spectrum A)
      (_root_.LinearPMap.spectrum B))
    (hEq : _root_.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  exact Sylvester_homogeneous_eq_zero_of_disjoint_spectrum
    hA hB hdisj hEq

/-- Positive pairwise spectral distance implies homogeneous uniqueness. -/
theorem closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X 0) :
    X = 0 := by
  exact Sylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
    hA hB hδ hgap hEq

/-- **Sylvester--Rosenblum uniqueness for closed operators.**  Two bounded solutions of the
same closed Sylvester equation coincide as soon as the two spectra are *disjoint*. -/
theorem closedSylvester_solution_unique_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E}
    (hdisj : Disjoint
      (_root_.LinearPMap.spectrum A)
      (_root_.LinearPMap.spectrum B))
    (hX : _root_.LinearPMap.SylvesterEquation A B X C)
    (hY : _root_.LinearPMap.SylvesterEquation A B Y C) :
    X = Y :=
  Sylvester_solution_unique_of_disjoint_spectrum hA hB hdisj hX hY

/-- Two bounded solutions of the same closed Sylvester equation coincide under
positive pairwise spectral separation.  A corollary of
`closedSylvester_solution_unique_of_disjoint_spectrum`, which is the sharp form. -/
theorem closedSylvester_solution_unique_of_pairwiseSpectrumGap
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hX : _root_.LinearPMap.SylvesterEquation A B X C)
    (hY : _root_.LinearPMap.SylvesterEquation A B Y C) :
    X = Y :=
  closedSylvester_solution_unique_of_disjoint_spectrum hA hB (hgap.disjoint hδ) hX hY

end

end Sylvester
end DavisKahan
end TauCeti
