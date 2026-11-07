/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8, GPT 5.6 High
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.QuadraticForm.Spectrum
public import TauCeti.Analysis.InnerProductSpace.Projection.SinTheta
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
public import ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Spectral order and quadratic forms over `RCLike`

For bounded self-adjoint operators on Hilbert spaces over an arbitrary `RCLike` field,
actual spectral inclusions imply upper and lower quadratic-form bounds.  The real continuous
functional calculus is supplied by scalar transport, so the same spectral-order API serves
real, complex, and abstract `RCLike` scalars.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original modules: the former real and complex spectral-order bridges, now unified after the
  real continuous functional calculus became available over arbitrary `RCLike` scalars.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Original authors / copyright: Jon Crall, Claude Opus 4.8, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/

public section

namespace TauCeti
namespace SpectralOrder
open TauCeti
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

/-- Spectral upper bound, packaged as a global upper form bound. -/
theorem upperFormBoundOn_top_of_spectrum_subset_Iic
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Iic c) :
    T.UpperFormBoundOn ⊤ c := by
  apply (_root_.ContinuousLinearMap.upperFormBoundOn_iff T ⊤ c).2
  intro x _
  exact ContinuousLinearMap.re_inner_le_of_spectrum_subset_Iic T hT hσ x

/-- Spectral lower bound, packaged as a global lower form bound. -/
theorem lowerFormBoundOn_top_of_spectrum_subset_Ici
    (T : H →L[𝕜] H) (hT : IsSelfAdjoint T) {c : ℝ}
    (hσ : spectrum ℝ T ⊆ Set.Ici c) :
    T.LowerFormBoundOn ⊤ c := by
  apply (_root_.ContinuousLinearMap.lowerFormBoundOn_iff T ⊤ c).2
  intro x _
  exact ContinuousLinearMap.le_re_inner_of_spectrum_subset_Ici T hT hσ x

/-- The sharp projector bound from spectra of the actual restrictions, uniformly over `RCLike`. -/
theorem opNorm_starProjection_sub_le_of_restriction_spectra
    {A B : H →L[𝕜] H} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U W : Submodule 𝕜 H} [U.HasOrthogonalProjection]
    [W.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A) (hW : Submodule.IsReducing W B)
    {c g : ℝ} (hg : 0 < g)
    (hUhi : spectrum ℝ (A.restrict hU.mem_invtSubmodule) ⊆ Set.Ici (c + g))
    (hUlo : spectrum ℝ (A.restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      hU.orthogonal_mem_invtSubmodule)) ⊆ Set.Iic c)
    (hWhi : spectrum ℝ (B.restrict hW.mem_invtSubmodule) ⊆ Set.Ici (c + g))
    (hWlo : spectrum ℝ (B.restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      hW.orthogonal_mem_invtSubmodule)) ⊆ Set.Iic c) :
    ‖(U.starProjection - W.starProjection : H →L[𝕜] H)‖ ≤ ‖B - A‖ / g := by
  rw [← Submodule.projectionGap_def U W]
  apply Submodule.projectionGap_le_norm_sub_div (c := c) (c' := c)
    U W hA hB hU.mem_invtSubmodule hW.mem_invtSubmodule hg
  · exact (ContinuousLinearMap.lowerFormBoundOn_iff A U (c + g)).mp
      (ContinuousLinearMap.lowerFormBoundOn_of_restriction_spectrum_subset_Ici
        hA hU.mem_invtSubmodule hUhi)
  · exact (ContinuousLinearMap.upperFormBoundOn_iff B Wᗮ c).mp
      (ContinuousLinearMap.upperFormBoundOn_of_restriction_spectrum_subset_Iic hB
        hW.orthogonal_mem_invtSubmodule hWlo)
  · exact (ContinuousLinearMap.lowerFormBoundOn_iff B W (c + g)).mp
      (ContinuousLinearMap.lowerFormBoundOn_of_restriction_spectrum_subset_Ici
        hB hW.mem_invtSubmodule hWhi)
  · exact (ContinuousLinearMap.upperFormBoundOn_iff A Uᗮ c).mp
      (ContinuousLinearMap.upperFormBoundOn_of_restriction_spectrum_subset_Iic hA
        hU.orthogonal_mem_invtSubmodule hUlo)


end SpectralOrder
end TauCeti
