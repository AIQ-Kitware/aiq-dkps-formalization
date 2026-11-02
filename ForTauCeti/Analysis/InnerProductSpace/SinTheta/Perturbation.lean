/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
public import ForTauCeti.Analysis.InnerProductSpace.Residual.Ritz
public import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Interval
public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralDistance
public import ForTauCeti.Analysis.InnerProductSpace.Residual.AngleEmbedding
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
public import ForTauCeti.Analysis.InnerProductSpace.SinTheta.UnitarilyInvariant
public import ForTauCeti.Analysis.InnerProductSpace.SinTheta.OperatorNorm
public import TauCeti.Analysis.InnerProductSpace.Projection.SinTheta
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Gap
public import ForTauCeti.Analysis.InnerProductSpace.SinTheta.DirectedBounds

/-!
# The complete finite-dimensional `sin Θ` theorem family

Literature map:

* `prose/core-arguments/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Section 7, "The sin Theta theorem".
* Davis--Kahan (1970), Section 2 (`sin Θ`) and Section 6 (proof and symmetric
  extension).
* `prose/core-arguments/Yu-Wang-Samworth-2014-core-arguments.tex`,
  Sections "The symmetric-matrix variant" and "Lower bound on the residual".

The residual theorem is the numerical analyst's form.  The perturbation
version is the operator theorist's form.  Both are stated for every relevant
unitarily invariant norm, followed by the interval, spectral-projector, and
concrete-norm corollaries expected from the final API.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/SinTheta/Perturbation.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

## The split

This file held all four sections in 1110 lines, over Tau Ceti's stated 1000-line
limit for a new file (`ForTauCeti/README.md` §4) — the last module in the library
over it. It is divided at its own `## Perturbation form` boundary:

* the residual, directed and two-sided projector-difference bounds are now in
  `ForTauCeti.Analysis.InnerProductSpace.SinTheta.DirectedBounds`, which this
  module imports;
* this file keeps the **perturbation form** — the transport lemmas for the
  canonical isometric inclusion of a subspace, and the theorems built on them:
  `sinTheta_perturbation_le`,
  `sinTheta_perturbation_le_of_orderedGap`,
  `opNorm_sinThetaMap_le_of_intervalGap`,
  `frobenius_sinTheta_residual_le_of_spectralDistance`,
  `frobenius_sinTheta_le`, `kyFan_sinTheta_le` and
  `sinTheta_perturbation_le_of_spectralDistance`.

The seam is that transport: nothing in `DirectedBounds` mentions a domain
isometry, and the perturbation theorems kept here use that transport.
At the time of the split, statements, signatures, proofs and declaration
names were unchanged. The import
`ForTauCeti.Analysis.InnerProductSpace.SinTheta.Perturbation` continued to
provide the development. Later upstream consumption is recorded below.

## October 31 accepted-upstream consumption

The original `sinAngleOperator_perturbation_le` was the finite-dimensional
symmetric, two-orientation, constant-one Davis--Kahan bound. TauCeti #19817
adapted it into the canonical `UnitarilyInvariantSeminorm` API, including the
projector-difference and symmetric sine-angle formulations. Its local proof,
private cross-block/adjoint helpers, and Ky Fan block-assembly lemmas have been
removed. `DavisKahan.Sources.DavisKahan1970.PartIII` uses the accepted
`mul_map_sinAngleOperator_le_map_sub` theorem directly through its source-specific alias.
The one-sided, ordered-gap, spectral-distance, and Frobenius results in this
module are separate results and remain maintained. The pre-consumption source
and detailed declaration mapping are recorded in the upstream contribution
census and extraction manifest.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-! ## Perturbation form -/

/-- The adjoint of the canonical isometric inclusion of a subspace is its
orthogonal projection onto that subspace.  This is the finite-dimensional
bridge used by `domainIsometryTransport` in the perturbation wrappers below. -/
private theorem adjoint_subtype_eq_orthogonalProjectionOnto
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    LinearMap.adjoint U.subtypeₗᵢ.toLinearMap =
      U.orthogonalProjectionOnto.toLinearMap := by
  rw [eq_comm]
  apply (LinearMap.eq_adjoint_iff
    U.orthogonalProjectionOnto.toLinearMap U.subtype).2
  intro x y
  -- states the inner-product goal against the projection's defining property.
  change ⟪U.starProjection x, (y : E)⟫_𝕜 = ⟪x, (y : E)⟫_𝕜
  rw [U.inner_starProjection_left_eq_right,
    U.starProjection_eq_self_iff.mpr y.2]

/-- Transporting the rectangular sine embedding on `U` back to the ambient
square space gives the one-sided sine cross projection `P_{Vᗮ} P_U`. -/
@[simp]
private theorem domainTransport_sinThetaEmbedding_apply
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    (N.domainIsometryTransport U.subtypeₗᵢ)
        (sinThetaEmbedding V U.subtypeₗᵢ) = N ((U.sinThetaMap V).toLinearMap) := by
  -- states the goal with the local definitions unfolded, in the exact shape the
  -- following rewrite needs. `simp only` on those definitions normalises further
  -- and the rewrite then has nothing to match -- tried, and it fails here.
  change N ((sinThetaEmbedding V U.subtypeₗᵢ) ∘ₗ
      LinearMap.adjoint U.subtypeₗᵢ.toLinearMap) = N ((U.sinThetaMap V).toLinearMap)
  rw [adjoint_subtype_eq_orthogonalProjectionOnto]
  congr 1
  rw [Submodule.sinThetaMap_def]
  ext x
  rfl

/-- The transported residual of the reducing inclusion is bounded by the
ambient perturbation norm. -/
private theorem domainTransport_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U) :
    (N.domainIsometryTransport U.subtypeₗᵢ)
        (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) := by
  have hres : residual B U.subtypeₗᵢ (A.restrict hU) =
      (B - A) ∘ₗ U.subtype := by
    ext x
    -- states the goal with the local definitions unfolded, in the exact shape the
    -- following rewrite needs. `simp only` on those definitions normalises further
    -- and the rewrite then has nothing to match -- tried, and it fails here.
    change B (x : E) - A (x : E) = (B - A) (x : E)
    rfl
  -- states the goal with the local definitions unfolded, in the exact shape the
  -- following rewrite needs. `simp only` on those definitions normalises further
  -- and the rewrite then has nothing to match -- tried, and it fails here.
  change N ((residual B U.subtypeₗᵢ (A.restrict hU)) ∘ₗ
      LinearMap.adjoint U.subtypeₗᵢ.toLinearMap) ≤ N (B - A)
  rw [hres, adjoint_subtype_eq_orthogonalProjectionOnto]
  have hcomp : ((B - A) ∘ₗ U.subtype) ∘ₗ
      U.orthogonalProjectionOnto.toLinearMap =
      (B - A) ∘ₗ projection U := by
    ext x
    rfl
  rw [hcomp]
  calc
    N ((B - A) ∘ₗ projection U) ≤ N (B - A) * 1 := by
      simpa only [mul_comm] using
        N.map_comp_le_right (B - A) (projection U) (c := 1)
          (fun x => by
            change ‖U.starProjection x‖ ≤ 1 * ‖x‖
            simpa only [one_mul] using U.norm_starProjection_apply_le x)
    _ = N (B - A) := mul_one _


/-- **Davis--Kahan `sin Θ`, perturbation form, every square UI norm.**
-/
theorem sinTheta_perturbation_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : PointIntervalExteriorGap A U B Vᗮ a b δ) :
    δ * N ((U.sinThetaMap V).toLinearMap) ≤ N (B - A) := by
  let NU : UnitarilyInvariantSeminorm 𝕜 U E :=
    N.domainIsometryTransport U.subtypeₗᵢ
  have hM : (A.restrict hU).IsSymmetric := hA.restrict_invariant hU
  have hMspec : Module.End.PointSpectrumIn (A.restrict hU) ⊤ (Set.Icc a b) :=
    (pointSpectrumIn_restrict_iff A hU (Set.Icc a b)).2 hgap.1
  have hres :
      δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) ≤
        NU (residual B U.subtypeₗᵢ (A.restrict hU)) :=
    sinTheta_residual_le (A := B) (U := V) (M := A.restrict hU)
      NU hB hV U.subtypeₗᵢ hM hδ hMspec hgap.2
  have hsin :
      NU (sinThetaEmbedding V U.subtypeₗᵢ) = N ((U.sinThetaMap V).toLinearMap) :=
    domainTransport_sinThetaEmbedding_apply N U V
  have hresBound :
      NU (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) :=
    domainTransport_residual_le (B := B) N hU
  calc
    δ * N ((U.sinThetaMap V).toLinearMap) =
        δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) := by rw [hsin]
    _ ≤ NU (residual B U.subtypeₗᵢ (A.restrict hU)) := hres
    _ ≤ N (B - A) := hresBound

/-- Ordered half-line perturbation form.
-/
theorem sinTheta_perturbation_le_of_orderedGap
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N ((U.sinThetaMap V).toLinearMap) ≤ N (B - A) := by
  let NU : UnitarilyInvariantSeminorm 𝕜 U E :=
    N.domainIsometryTransport U.subtypeₗᵢ
  have hM : (A.restrict hU).IsSymmetric := hA.restrict_invariant hU
  have hgap' : OrderedGap (A.restrict hU) ⊤ B Vᗮ δ := by
    intro lam μ hlam hμ
    apply hgap lam μ
    · rw [← restrictedPointSpectrum_restrict A hU]
      exact hlam
    · exact hμ
  have hres :
      δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) ≤
        NU (residual B U.subtypeₗᵢ (A.restrict hU)) :=
    sinTheta_residual_le_of_orderedGap
      (A := B) (U := V) (M := A.restrict hU) NU hB hV
      U.subtypeₗᵢ hM hδ hgap'
  have hsin :
      NU (sinThetaEmbedding V U.subtypeₗᵢ) = N ((U.sinThetaMap V).toLinearMap) :=
    domainTransport_sinThetaEmbedding_apply N U V
  have hresBound :
      NU (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) :=
    domainTransport_residual_le (B := B) N hU
  calc
    δ * N ((U.sinThetaMap V).toLinearMap) =
        δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) := by rw [hsin]
    _ ≤ NU (residual B U.subtypeₗᵢ (A.restrict hU)) := hres
    _ ≤ N (B - A) := hresBound

/-- **Sharp one-sided interval/exterior `sin Θ` bound in operator norm.**

The analytic estimate is delegated to the polar-absorption Sylvester theorem.
Finite dimensionality enters only through restriction of the two diagonal
blocks and the finite spectral bridge used by that theorem. -/
theorem opNorm_sinThetaMap_le_of_intervalGap
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : PointIntervalExteriorGap A U B Vᗮ a b δ) :
    δ * ‖(U.sinThetaMap V)‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  have hnative : (U.sinThetaMap V).toLinearMap.toContinuousLinearMap =
      U.sinThetaMap V := by
    ext x
    rfl
  simpa only [UnitarilyInvariantSeminorm.opNorm_apply, hnative] using
    sinTheta_perturbation_le (UnitarilyInvariantSeminorm.opNorm 𝕜 E E)
      hA hB hU hV hδ hgap

/-- General disjoint-spectrum residual form for the Frobenius norm, with
the sharp constant one.  Unlike a general symmetric gauge, the square norm
can be estimated entrywise in eigenbases of the two compressed operators. -/
theorem frobenius_sinTheta_residual_le_of_spectralDistance
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : IsInvariant A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PointSpectraSeparated M ⊤ A Uᗮ δ) :
    δ * UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := F) (F := E)
        (sinThetaEmbedding U X) ≤
      UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := F) (F := E)
        (residual A X M) := by
  have hUperp : IsInvariant A Uᗮ := isInvariant_orthogonal_of_isSymmetric hA hU
  let AU : Uᗮ →ₗ[𝕜] Uᗮ := A.restrict hUperp
  let Y : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ X.toLinearMap
  let C : F →ₗ[𝕜] Uᗮ :=
    Uᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ residual A X M
  have hAU : AU.IsSymmetric := hA.restrict_invariant hUperp
  have hgap' : PointSpectraSeparated AU ⊤ M ⊤ δ := by
    intro lam mu hlam hmu
    have hlam' : lam ∈ Module.End.restrictedPointSpectrum A Uᗮ := by
      rw [← restrictedPointSpectrum_restrict A hUperp]
      exact hlam
    have hsep := hgap mu lam hmu hlam'
    simpa [abs_sub_comm] using hsep
  have hEq : AU ∘ₗ Y - Y ∘ₗ M = C :=
    sylvester_projectedResidual_eq hA hU hUperp X M
  have hSylv := frobenius_sylvester_le_of_pointSpectraSeparated
    hAU hM hδ hgap' hEq
  have hY : UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := F) (F := Uᗮ) Y =
      UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := F) (F := E)
        (sinThetaEmbedding U X) := by
    rw [← UnitarilyInvariantSeminorm.frobenius_subtype_comp Uᗮ Y]
    congr 1
  have hC : UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := F) (F := Uᗮ) C ≤
      UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := F) (F := E)
        (residual A X M) := by
    have hCembed : Uᗮ.subtypeₗᵢ.toLinearMap ∘ₗ C =
        complementaryProjection U ∘ₗ residual A X M := by
      ext x
      simp [C, complementaryProjection, projection, LinearMap.comp_apply]
    rw [← UnitarilyInvariantSeminorm.frobenius_subtype_comp Uᗮ C, hCembed]
    have hproj := (UnitarilyInvariantSeminorm.frobenius
      (𝕜 := 𝕜) (E := F) (F := E)).map_starProjection_comp_le Uᗮ
        (residual A X M).toContinuousLinearMap
    simpa [complementaryProjection, projection] using hproj
  rw [hY] at hSylv
  exact hSylv.trans hC

/-- Frobenius form.
-/
theorem frobenius_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : PointIntervalExteriorGap A U B Vᗮ a b δ) :
    δ * UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E)
        (U.sinThetaMap V).toLinearMap ≤
      UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A) := by
  exact sinTheta_perturbation_le (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E))
    hA hB hU hV hδ hgap

/-- Ky Fan form, simultaneously controlling every singular-value prefix.
-/
theorem kyFan_sinTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : PointIntervalExteriorGap A U B Vᗮ a b δ) (k : ℕ) :
    δ * ((U.sinThetaMap V).toLinearMap).kyFanSum k ≤ (B - A).kyFanSum k := by
  let NK : UnitarilyInvariantSeminorm 𝕜 E E :=
    (UnitarilyInvariantSeminorm.kyFan
      (𝕜 := 𝕜) (E := E) (F := E) k)
  have h := sinTheta_perturbation_le NK hA hB hU hV hδ hgap
  simpa only [NK, UnitarilyInvariantSeminorm.kyFan_apply] using h

/-- General two-sided spectral separation with the `π/2` constant.  The
ambient transport proof is complete; the only open analytic input is the Ky Fan
separated reciprocal-multiplier theorem in `Sylvester.lean`.
-/
theorem sinTheta_perturbation_le_of_spectralDistance
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PointSpectraSeparated A U B Vᗮ δ) :
    δ * N ((U.sinThetaMap V).toLinearMap) ≤ (Real.pi / 2) * N (B - A) := by
  let NU : UnitarilyInvariantSeminorm 𝕜 U E :=
    N.domainIsometryTransport U.subtypeₗᵢ
  have hM : (A.restrict hU).IsSymmetric := hA.restrict_invariant hU
  have hgap' : PointSpectraSeparated (A.restrict hU) ⊤ B Vᗮ δ := by
    intro lam μ hlam hμ
    apply hgap lam μ
    · rw [← restrictedPointSpectrum_restrict A hU]
      exact hlam
    · exact hμ
  have hres :
      δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) ≤
        (Real.pi / 2) * NU (residual B U.subtypeₗᵢ (A.restrict hU)) :=
    sinTheta_residual_le_of_spectralDistance
      (A := B) (U := V) (M := A.restrict hU) NU hB hV
      U.subtypeₗᵢ hM hδ hgap'
  have hsin :
      NU (sinThetaEmbedding V U.subtypeₗᵢ) = N ((U.sinThetaMap V).toLinearMap) :=
    domainTransport_sinThetaEmbedding_apply N U V
  have hresBound :
      NU (residual B U.subtypeₗᵢ (A.restrict hU)) ≤ N (B - A) :=
    domainTransport_residual_le (B := B) N hU
  calc
    δ * N ((U.sinThetaMap V).toLinearMap) =
        δ * NU (sinThetaEmbedding V U.subtypeₗᵢ) := by rw [hsin]
    _ ≤ (Real.pi / 2) *
        NU (residual B U.subtypeₗᵢ (A.restrict hU)) := hres
    _ ≤ (Real.pi / 2) * N (B - A) :=
      mul_le_mul_of_nonneg_left hresBound (by positivity)

end TauCeti
