/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.SpectralProjection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Resolvents, Riesz projections, and spectral continuation

Literature writeup: local TeX, Sections 6, 11, and 20.  This module records the
analytic bridge from Banach-algebra resolvents to projection-valued spectral
subspaces and continuation under perturbation.
-/


/-! ## Construction plan

* Replace the total `resolventOperator` interface by mathlib's actual
  Banach-algebra resolvent, or by a bundled inverse parameterized by a proof of
  resolvent-set membership.  Prove inverse uniqueness once and use it in both
  resolvent identities.
* Package `ContourSeparatesSpectrum` with piecewise smoothness, closedness,
  resolvent membership along the path, and the winding-number conditions for
  selected and complementary spectral components.
* Define `rieszProjection` as the Bochner integral of the resolvent with the
  `1/(2*pi*i)` factor.  Prove idempotence by the first resolvent identity and
  Fubini, then prove agreement with the self-adjoint spectral projection by
  functional calculus.
-/


/-! ## Weak-agent execution plan: proof-carrying resolvents and Riesz projections

Refactor the total `resolventOperator` before proving identities.  The elegant
interface is either

`resolventOperator A z (hz : InResolventSet A z)`

or a bundled subtype containing an inverse and its two inverse laws.  If the
public total definition must remain temporarily, define it with an `if hz`
branch and prove an `_eq_of_mem` theorem; every analytic result must rewrite
through that theorem first.

Prove inverse uniqueness once.  Then both resolvent identities are ring
algebra with named inverse equations; use `ContinuousLinearMap.ext` and
`noncomm_ring` only after compositions are reassociated.

Do not define `ContourSeparatesSpectrum` as an opaque proposition.  Replace or
supplement it with a structure containing:

* a piecewise `C1` or rectifiable closed path;
* a proof every contour point is in the resolvent set;
* a uniform resolvent bound;
* winding number one on the selected spectrum and zero on the complement.

Define `rieszProjection` with the repository/mathlib contour-integral API and
include the normalization factor in the definition.  Prove continuity of the
integrand before forming the integral.  Establish agreement with the Borel
spectral projection by functional-calculus extensionality on the spectrum;
then obtain idempotence and self-adjointness from that equality rather than by
a first, difficult double-integral proof.

For continuation, first prove the local estimate from the second resolvent
identity, then pass it through the contour integral.  Keep the finite
continuation theorem separate: it may use a fixed finite contour and needs no
general PVM construction.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Resolvent-set predicate. -/
def InResolventSet (A : E →L[𝕜] E) (z : 𝕜) : Prop :=
  ∃ R : E →L[𝕜] E,
    R ∘L (A - z • ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 E ∧
    (A - z • ContinuousLinearMap.id 𝕜 E) ∘L R = ContinuousLinearMap.id 𝕜 E

/-- Resolvent operator `(A - zI)⁻¹`, defined on the resolvent set and extended
by zero elsewhere.  Analytic statements must access it only through
`resolventOperator_inverse` and its multiplicative corollaries. -/
noncomputable def resolventOperator (A : E →L[𝕜] E) (z : 𝕜) : E →L[𝕜] E :=
  haveI := Classical.propDecidable (InResolventSet A z)
  if h : InResolventSet A z then h.choose else 0

omit [CompleteSpace E] in
/-- On the resolvent set, `resolventOperator` is a two-sided inverse of
`A - zI`. -/
theorem resolventOperator_inverse (A : E →L[𝕜] E) {z : 𝕜}
    (hz : InResolventSet A z) :
    resolventOperator A z ∘L (A - z • ContinuousLinearMap.id 𝕜 E) =
        ContinuousLinearMap.id 𝕜 E ∧
      (A - z • ContinuousLinearMap.id 𝕜 E) ∘L resolventOperator A z =
        ContinuousLinearMap.id 𝕜 E := by
  simp only [resolventOperator]
  rw [dif_pos hz]
  exact hz.choose_spec

omit [CompleteSpace E] in
/-- Ring-language left-inverse law for the resolvent. -/
theorem resolventOperator_mul_cancel (A : E →L[𝕜] E) {z : 𝕜}
    (hz : InResolventSet A z) :
    resolventOperator A z * (A - z • 1) = 1 := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
  exact (resolventOperator_inverse A hz).1

omit [CompleteSpace E] in
/-- Ring-language right-inverse law for the resolvent. -/
theorem mul_resolventOperator_cancel (A : E →L[𝕜] E) {z : 𝕜}
    (hz : InResolventSet A z) :
    (A - z • 1) * resolventOperator A z = 1 := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
  exact (resolventOperator_inverse A hz).2

omit [CompleteSpace E] in
/-- First resolvent identity.

Lean proof route for a weaker agent:

1. Obtain the two inverse identities for `A-zI` and `A-wI` from `hz,hw`.
2. Expand `Rz-Rw = Rz((A-wI)-(A-zI))Rw`.
3. Simplify the middle difference to `(z-w)I` and reassociate compositions.


Ext-agent signature audit (GPT 5.6 High): The sign is correct for the convention
`(A-zI)⁻¹`. Ensure `resolventOperator` is chosen from `InResolventSet` and prove inverse
uniqueness once.

Preferred dependency route: Use Banach-algebra inverse uniqueness and Bochner contour
integration; keep contour regularity and winding-number obligations inside
`ContourSeparatesSpectrum`.
-/
theorem resolvent_identity
    (A : E →L[𝕜] E) {z w : 𝕜}
    (hz : InResolventSet A z) (hw : InResolventSet A w) :
    resolventOperator A z - resolventOperator A w =
      (z - w) • (resolventOperator A z ∘L resolventOperator A w) := by
  have h1 := resolventOperator_mul_cancel A hz
  have h2 := mul_resolventOperator_cancel A hw
  have hdiff : (A - w • (1 : E →L[𝕜] E)) - (A - z • (1 : E →L[𝕜] E)) =
      (z - w) • (1 : E →L[𝕜] E) := by
    rw [sub_smul]; abel
  have key : resolventOperator A z - resolventOperator A w =
      (z - w) • (resolventOperator A z * resolventOperator A w) := by
    calc resolventOperator A z - resolventOperator A w
        = resolventOperator A z * ((A - w • 1) * resolventOperator A w) -
            resolventOperator A z * (A - z • 1) * resolventOperator A w := by
          rw [h2, mul_one, h1, one_mul]
      _ = resolventOperator A z * ((A - w • 1) - (A - z • 1)) *
            resolventOperator A w := by
          noncomm_ring
      _ = resolventOperator A z * ((z - w) • (1 : E →L[𝕜] E)) *
            resolventOperator A w := by
          rw [hdiff]
      _ = (z - w) • (resolventOperator A z * resolventOperator A w) := by
          rw [mul_smul_comm, mul_one, smul_mul_assoc]
  simpa only [ContinuousLinearMap.mul_def] using key

omit [CompleteSpace E] in
/-- Second resolvent identity.

Lean proof route for a weaker agent:

1. Use the algebraic inverse-difference formula `Y⁻¹-X⁻¹=Y⁻¹(X-Y)X⁻¹`.
2. Instantiate `X=A-zI` and `Y=B-zI` with the inverses supplied by `hA,hB`.
3. Simplify the scalar identity terms and reassociate compositions.


Ext-agent signature audit (GPT 5.6 High): The order and sign are correct: `R_B-R_A =
R_B(A-B)R_A` for the chosen resolvent convention.

Preferred dependency route: Use Banach-algebra inverse uniqueness and Bochner contour
integration; keep contour regularity and winding-number obligations inside
`ContourSeparatesSpectrum`.
-/
theorem resolvent_perturbation_identity
    (A B : E →L[𝕜] E) {z : 𝕜}
    (hA : InResolventSet A z) (hB : InResolventSet B z) :
    resolventOperator B z - resolventOperator A z =
      resolventOperator B z ∘L (A - B) ∘L resolventOperator A z := by
  have h1 := resolventOperator_mul_cancel B hB
  have h2 := mul_resolventOperator_cancel A hA
  have hdiff : (A - z • (1 : E →L[𝕜] E)) - (B - z • (1 : E →L[𝕜] E)) =
      A - B := by
    abel
  have key : resolventOperator B z - resolventOperator A z =
      resolventOperator B z * (A - B) * resolventOperator A z := by
    calc resolventOperator B z - resolventOperator A z
        = resolventOperator B z * ((A - z • 1) * resolventOperator A z) -
            resolventOperator B z * (B - z • 1) * resolventOperator A z := by
          rw [h2, mul_one, h1, one_mul]
      _ = resolventOperator B z * ((A - z • 1) - (B - z • 1)) *
            resolventOperator A z := by
          noncomm_ring
      _ = resolventOperator B z * (A - B) * resolventOperator A z := by
          rw [hdiff]
  simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    using key


omit [CompleteSpace E] in
/-- Quantitative form of the second resolvent identity.  This is the local
operator estimate needed before passing to a contour integral. -/
theorem norm_resolventOperator_sub_le
    (A B : E →L[𝕜] E) {z : 𝕜}
    (hA : InResolventSet A z) (hB : InResolventSet B z) :
    ‖resolventOperator B z - resolventOperator A z‖ ≤
      ‖resolventOperator B z‖ * ‖A - B‖ * ‖resolventOperator A z‖ := by
  rw [resolvent_perturbation_identity A B hA hB]
  calc
    ‖resolventOperator B z ∘L (A - B) ∘L resolventOperator A z‖ ≤
        ‖resolventOperator B z‖ * ‖(A - B) ∘L resolventOperator A z‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖resolventOperator B z‖ *
        (‖A - B‖ * ‖resolventOperator A z‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg (resolventOperator B z))
    _ = ‖resolventOperator B z‖ * ‖A - B‖ *
        ‖resolventOperator A z‖ := (mul_assoc _ _ _).symm

omit [CompleteSpace E] in
/-- Uniform-bound corollary of `norm_resolventOperator_sub_le`. -/
theorem norm_resolventOperator_sub_le_of_bounds
    (A B : E →L[𝕜] E) {z : 𝕜} {M : ℝ}
    (hA : InResolventSet A z) (hB : InResolventSet B z)
    (hRA : ‖resolventOperator A z‖ ≤ M)
    (hRB : ‖resolventOperator B z‖ ≤ M) :
    ‖resolventOperator B z - resolventOperator A z‖ ≤
      M * ‖A - B‖ * M := by
  calc
    ‖resolventOperator B z - resolventOperator A z‖ ≤
        ‖resolventOperator B z‖ * ‖A - B‖ *
          ‖resolventOperator A z‖ :=
      norm_resolventOperator_sub_le A B hA hB
    _ ≤ M * ‖A - B‖ * ‖resolventOperator A z‖ := by
      gcongr
    _ ≤ M * ‖A - B‖ * M := by
      have hM : 0 ≤ M := (norm_nonneg (resolventOperator B z)).trans hRB
      exact mul_le_mul_of_nonneg_left hRA
        (mul_nonneg hM (norm_nonneg (A - B)))


/-! ## Spectral-parameter continuity -/

omit [CompleteSpace E] in
/-- Quantitative first-resolvent estimate.  For one fixed operator, the
resolvent is locally Lipschitz in the spectral parameter, with constant given
by the product of the two endpoint resolvent norms. -/
theorem norm_resolventOperator_sub_spectral_le
    (A : E →L[𝕜] E) {z w : 𝕜}
    (hz : InResolventSet A z) (hw : InResolventSet A w) :
    ‖resolventOperator A z - resolventOperator A w‖ ≤
      ‖z - w‖ * ‖resolventOperator A z‖ * ‖resolventOperator A w‖ := by
  rw [resolvent_identity A hz hw, norm_smul]
  have hcomp :
      ‖resolventOperator A z ∘SL resolventOperator A w‖ ≤
        ‖resolventOperator A z‖ * ‖resolventOperator A w‖ :=
    ContinuousLinearMap.opNorm_comp_le (𝕜 := 𝕜)
      (resolventOperator A z) (resolventOperator A w)
  have hmul := mul_le_mul_of_nonneg_left hcomp (norm_nonneg (z - w))
  exact hmul.trans_eq (mul_assoc _ _ _).symm

omit [CompleteSpace E] in
/-- Uniform-bound specialization of the spectral-parameter resolvent
estimate. -/
theorem norm_resolventOperator_sub_spectral_le_of_bounds
    (A : E →L[𝕜] E) {z w : 𝕜} {M : ℝ}
    (hz : InResolventSet A z) (hw : InResolventSet A w)
    (hRz : ‖resolventOperator A z‖ ≤ M)
    (hRw : ‖resolventOperator A w‖ ≤ M) :
    ‖resolventOperator A z - resolventOperator A w‖ ≤
      M ^ 2 * ‖z - w‖ := by
  have hM : 0 ≤ M := (norm_nonneg (resolventOperator A z)).trans hRz
  calc
    ‖resolventOperator A z - resolventOperator A w‖ ≤
        ‖z - w‖ * ‖resolventOperator A z‖ *
          ‖resolventOperator A w‖ :=
      norm_resolventOperator_sub_spectral_le A hz hw
    _ ≤ ‖z - w‖ * M * M := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hRz (norm_nonneg (z - w)))
        hRw (norm_nonneg (resolventOperator A w))
        (mul_nonneg (norm_nonneg (z - w)) hM)
    _ = M ^ 2 * ‖z - w‖ := by ring

omit [CompleteSpace E] in
/-- A uniform resolvent bound on a set upgrades the total resolvent map to a
Lipschitz map on that set. -/
theorem lipschitzOnWith_resolventOperator_of_uniform_bound
    (A : E →L[𝕜] E) (S : Set 𝕜) (M : ℝ)
    (hmem : ∀ z ∈ S, InResolventSet A z)
    (hbound : ∀ z ∈ S, ‖resolventOperator A z‖ ≤ M) :
    LipschitzOnWith (Real.toNNReal (M ^ 2)) (resolventOperator A) S := by
  refine LipschitzOnWith.of_dist_le' ?_
  intro z hz w hw
  simpa only [dist_eq_norm] using
    norm_resolventOperator_sub_spectral_le_of_bounds A
      (hmem z hz) (hmem w hw) (hbound z hz) (hbound w hw)

omit [CompleteSpace E] in
/-- Continuity on a uniformly resolvent-bounded parameter set. -/
theorem continuousOn_resolventOperator_of_uniform_bound
    (A : E →L[𝕜] E) (S : Set 𝕜) (M : ℝ)
    (hmem : ∀ z ∈ S, InResolventSet A z)
    (hbound : ∀ z ∈ S, ‖resolventOperator A z‖ ≤ M) :
    ContinuousOn (resolventOperator A) S :=
  (lipschitzOnWith_resolventOperator_of_uniform_bound
    A S M hmem hbound).continuousOn


/-! ## Complex self-adjoint resolvent bounds -/

section ComplexResolventDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- For a complex self-adjoint operator, positive distance from the real
spectrum gives both resolvent-set membership and the sharp inverse-distance
operator-norm bound.

The proof constructs the inverse through the complex continuous functional
calculus using the symbol `w ↦ (w - z)⁻¹`.  Self-adjointness restricts the
complex spectrum to the embedded real spectrum, so the supplied distance
hypothesis controls the symbol on the whole spectrum. -/
theorem complex_inResolventSet_and_norm_resolvent_le_inv_distance
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (z : ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ lam ∈ realSpectrum A, delta ≤ ‖z - (lam : ℂ)‖) :
    InResolventSet A z ∧ ‖resolventOperator A z‖ ≤ delta⁻¹ := by
  let f : ℂ → ℂ := fun w => w - z
  let g : ℂ → ℂ := fun w => (w - z)⁻¹
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hnormal : IsStarNormal A := hAsa.isStarNormal
  have hne : ∀ w ∈ spectrum ℂ A, f w ≠ 0 := by
    intro w hw hzero
    obtain ⟨lam, hlam, rfl⟩ :=
      hAsa.spectrumRestricts.algebraMap_image.symm ▸ hw
    have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
      rw [← hAsa.spectrumRestricts.algebraMap_image]
      exact ⟨lam, hlam, rfl⟩
    have hdist := hsep lam (by exact hlamC)
    have heq : (lam : ℂ) = z :=
      sub_eq_zero.mp (by simpa [f] using hzero)
    rw [← heq, sub_self, norm_zero] at hdist
    linarith
  have hfcont : ContinuousOn f (spectrum ℂ A) :=
    (continuous_id.sub continuous_const).continuousOn
  have hgcont : ContinuousOn g (spectrum ℂ A) := hfcont.inv₀ hne
  let R : H →L[ℂ] H := cfc g A
  have hshift : cfc f A = A - z • (1 : H →L[ℂ] H) := by
    rw [show f = fun w : ℂ => w - z from rfl,
      cfc_sub (fun w : ℂ => w) (fun _ : ℂ => z) A,
      cfc_id' (R := ℂ) (a := A), cfc_const z A,
      Algebra.algebraMap_eq_smul_one]
  have hleft : R * (A - z • (1 : H →L[ℂ] H)) = 1 := by
    have hmul : cfc g A * cfc f A = cfc (fun w => g w * f w) A :=
      (cfc_mul g f A hgcont hfcont).symm
    rw [← hshift]
    change cfc g A * cfc f A = 1
    rw [hmul,
      cfc_congr (g := fun _ : ℂ => (1 : ℂ))
        (fun w hw => by simpa [f, g] using inv_mul_cancel₀ (hne w hw)),
      cfc_const_one ℂ A]
  have hright : (A - z • (1 : H →L[ℂ] H)) * R = 1 := by
    have hmul : cfc f A * cfc g A = cfc (fun w => f w * g w) A :=
      (cfc_mul f g A hfcont hgcont).symm
    rw [← hshift]
    change cfc f A * cfc g A = 1
    rw [hmul,
      cfc_congr (g := fun _ : ℂ => (1 : ℂ))
        (fun w hw => by simpa [f, g] using mul_inv_cancel₀ (hne w hw)),
      cfc_const_one ℂ A]
  have hz : InResolventSet A z := by
    refine ⟨R, ?_, ?_⟩
    · simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
        using hleft
    · simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
        using hright
  have hresolvent : resolventOperator A z = R := by
    have hchosen := resolventOperator_mul_cancel A hz
    calc
      resolventOperator A z = resolventOperator A z * 1 := (mul_one _).symm
      _ = resolventOperator A z *
          ((A - z • (1 : H →L[ℂ] H)) * R) := by rw [hright]
      _ = (resolventOperator A z *
          (A - z • (1 : H →L[ℂ] H))) * R := by rw [mul_assoc]
      _ = R := by rw [hchosen, one_mul]
  have hRnorm : ‖R‖ ≤ delta⁻¹ := by
    change ‖cfc g A‖ ≤ delta⁻¹
    refine norm_cfc_le (inv_nonneg.mpr hdelta.le) ?_
    intro w hw
    obtain ⟨lam, hlam, rfl⟩ :=
      hAsa.spectrumRestricts.algebraMap_image.symm ▸ hw
    have hlamC : (lam : ℂ) ∈ spectrum ℂ A := by
      rw [← hAsa.spectrumRestricts.algebraMap_image]
      exact ⟨lam, hlam, rfl⟩
    have hdist : delta ≤ ‖z - algebraMap ℝ ℂ lam‖ := by
      convert hsep lam (by exact hlamC) using 1 <;> simp
    have hdist' : delta ≤ ‖algebraMap ℝ ℂ lam - z‖ := by
      simpa only [norm_sub_rev] using hdist
    change ‖(algebraMap ℝ ℂ lam - z)⁻¹‖ ≤ delta⁻¹
    rw [norm_inv]
    exact inv_anti₀ hdelta hdist'
  exact ⟨hz, hresolvent.symm ▸ hRnorm⟩

/-- Resolvent-set membership from a positive complex spectral-distance bound. -/
theorem complex_inResolventSet_of_distance
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (z : ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ lam ∈ realSpectrum A, delta ≤ ‖z - (lam : ℂ)‖) :
    InResolventSet A z :=
  (complex_inResolventSet_and_norm_resolvent_le_inv_distance
    A hA z delta hdelta hsep).1

/-- Sharp resolvent norm bound for a complex self-adjoint operator. -/
theorem complex_norm_resolvent_le_inv_distance
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (z : ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ lam ∈ realSpectrum A, delta ≤ ‖z - (lam : ℂ)‖) :
    ‖resolventOperator A z‖ ≤ delta⁻¹ :=
  (complex_inResolventSet_and_norm_resolvent_le_inv_distance
    A hA z delta hdelta hsep).2

/-- On any set of complex spectral parameters with one common positive
distance from the real spectrum of a complex self-adjoint operator, the
resolvent is Lipschitz with the sharp distance-squared constant. -/
theorem complex_lipschitzOnWith_resolventOperator_of_distance
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (S : Set ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ z ∈ S, ∀ lam ∈ realSpectrum A,
      delta ≤ ‖z - (lam : ℂ)‖) :
    LipschitzOnWith (Real.toNNReal (delta⁻¹ ^ 2))
      (resolventOperator A) S := by
  apply lipschitzOnWith_resolventOperator_of_uniform_bound A S delta⁻¹
  · intro z hz
    exact complex_inResolventSet_of_distance A hA z delta hdelta
      (hsep z hz)
  · intro z hz
    exact complex_norm_resolvent_le_inv_distance A hA z delta hdelta
      (hsep z hz)

/-- Continuity of the complex self-adjoint resolvent on a uniformly separated
spectral-parameter set.  This is the continuity input for a Riesz contour
integrand. -/
theorem complex_continuousOn_resolventOperator_of_distance
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (S : Set ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ z ∈ S, ∀ lam ∈ realSpectrum A,
      delta ≤ ‖z - (lam : ℂ)‖) :
    ContinuousOn (resolventOperator A) S :=
  (complex_lipschitzOnWith_resolventOperator_of_distance
    A hA S delta hdelta hsep).continuousOn


end ComplexResolventDistance

/-
The self-adjoint resolvent-norm bound, the contour-separation predicate, the
Riesz projection, and its identification with the spectral projection used to
live here.  They were written against a `Contour.integral` / `Contour.IsClosed`
/ `Contour.Rectifiable` / `Contour.index` API that exists nowhere in this
repository, in Mathlib, or in vendored Spectra, so the whole tail never
compiled and kept every downstream module dark.

The circle-only replacement is
`DavisKahan.Experimental.Frontier.RieszCircle`, which builds the Riesz
projection from Mathlib's `circleIntegral` and identifies it with the existing
`boundedSelfAdjointSpectralProjection`.  The single consumer of the removed
tail, `SinTheta/Continuation.lean`, is rewired onto that surface.
-/

end DavisKahanExt
end ForMathlib
