/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.FiniteDimensional.DoubleAngle.SinTheta
import DavisKahan.Experimental.FiniteDimensional.Core.AngleOperators
import DavisKahan.FiniteDimensional.Core.OperatorBlocks
import DavisKahan.FiniteDimensional.DoubleAngle.TanTheta

/-!
# Proposed finite-dimensional `tan (2 Θ)` extensions

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 10--11.
* Davis--Kahan (1970), Section 2 (`tan 2Θ`), Section 7 (proof), and
  Theorem 8.1 (selection of the correct perturbed spectral subspace and
  spectral repulsion).
* `ForMathlib/prose/Davis-1963-core-arguments.tex`, Section
  "The sharp two-subspace estimate" for the one-vector ancestor.

The proof-complete classical finite Part III theorem is
`ForMathlib.tan_two_theta_norm_sub_le`, re-exported canonically by
`DavisKahanTheory.PartIII`.  It is the sharp operator-norm theorem and includes
the strict quarter-turn conclusion.  This module records proposed residual,
canonical-angle-operator, spectral-selection, and every-UI-norm
strengthenings; those declarations are extensions rather than missing pieces
of the source-checked Part III headline.
-/


/-! ## Weak-agent execution plan: Riccati identity and branch selection

### A. Raw `tan 2Θ` estimate

Prove the residual theorem before the perturbation theorem.  In the splitting
`U ⊕ Uᗮ`, write the reducing equation for the represented subspace and extract
the two block equations.  Eliminate the diagonal terms to obtain the Riccati
or double-angle Sylvester identity.  Package that identity as a named lemma
whose left side is exactly the operator used by `tanTwoThetaEmbedding`; this
prevents repeated block algebra in every norm specialization.

Quarter-turn avoidance should be proved from injectivity of the denominator
operator, not assumed through a total inverse.  Use `InternalGap A U δ` to
show a vector in the denominator kernel would solve a homogeneous separated
Sylvester equation, hence vanish.  Only then rewrite the totalized
`tanTwoThetaEmbedding` to its proof-carrying branch and apply the ordered
rectangular UI estimate.  The perturbation form follows by parameterizing `V`
with an isometry and rewriting its residual as `(B-A) ∘ X`.

### B. Finite continuation for the canonical branch

Do not begin with the experimental infinite-dimensional Riesz integral.  The
finite theorem can use the existing eigenbasis-defined `spectralProjection`.
Introduce the path

`Apath t := A + ((t : ℝ) : 𝕜) • H`, for `t ∈ Set.Icc 0 1`.

Prove these helpers in order:

1. `isSymmetric_Apath`.
2. A uniform exclusion of the cut interval `(a,b)` from the spectrum of
   `Apath t`; the off-diagonal hypothesis is used here through the squared
   block equation or spectral-repulsion estimate.
3. Local constancy of the number of eigenvalues below `a`.  Use continuity of
   ordered eigenvalues in finite dimensions, or prove local norm continuity of
   the finite spectral projector from a fixed contour once the resolvent
   helper exists.
4. Norm continuity of
   `P t := spectralProjection (Apath t) (Set.Iic a)` on each neighborhood with
   the same selected eigenvalue indices.
5. Openness and closedness of `{t | ‖P t - projection U‖ < 1}` in `[0,1]`.
   It contains zero; connectedness of the interval gives the endpoint.
6. Convert `‖P 1 - projection U‖ < 1` to `IsAcute` using the projection-gap
   characterization already present in the supported core.

Once `isAcute_canonical_tanTwoTheta` is proved, derive
`tanTwoTheta_spectralSubspace_le` by the raw perturbation theorem.  For
`existsUnique_reducingSubspace_preserving_gap`, existence is the same spectral
subspace; uniqueness should follow from the spectral inclusion and the finite
spectral decomposition, not from a second continuation argument.

### C. Repulsion

Treat `spectral_repulsion_compression` as a separate min--max root.  Build the
isometry from `Uᗮ` to the graph `Vᗮ`, compute the compressed quadratic form,
and prove a pointwise Rayleigh inequality.  Then use the ordered-eigenvalue
min--max theorem.  The eigenvalue and UI-norm statements must be corollaries;
do not repeat graph computations in them.

### D. Avoid circular dependencies

The continuation theorem may use the already proved raw `tan 2Θ` estimate only
if that estimate does not itself assume canonical acuteness.  Keep the raw
quarter-turn theorem and the canonical acute-branch theorem in this order.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- **Davis--Kahan `tan 2Θ`, residual form, every UI norm.**

Here `X` spans a reducing subspace of the perturbed operator `B`, while the
perturbation `B-A` is fully off diagonal relative to the unperturbed splitting
`U ⊕ Uᗮ`.  The theorem itself excludes quarter-turn angles; acuteness is not a
hypothesis for the raw double-angle theorem.

Lean proof route for a weaker agent:

1. Use `hoff` and the reducing decompositions of `A` and `B` to derive the finite Riccati equation for the angular operator from `U` to `V`.
2. Prove the cosine-difference denominator is nonzero from `InternalGap A U δ`; this yields `AvoidsQuarterTurn U V` and legitimizes `tanTwoAngleOperator`.
3. Apply the ordered Sylvester/Ky Fan estimate to the Riccati identity and use finite Fan dominance to obtain the arbitrary UI-norm inequality.
-/
theorem tanTwoTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurnEmbedding U X ∧
      δ * N (tanTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
  classical
  let C₂ := cosTwoThetaSourceOperator U X
  let S₂ := sinTwoThetaEmbedding U X
  let R := residual A X M
  have hriccati :
      doubleAngleSylvesterOperator A U S₂ =
        doubleAngleResidual U X R :=
    doubleAngleRiccatiIdentity hA hB hM hU hBX hoff
  have hker : LinearMap.ker C₂ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x hx
    have hhom := doubleAngleHomogeneousEquation_of_cosTwo_apply_eq_zero
      hriccati hx
    exact internalGap_homogeneous_doubleAngle_injective hA hU hδ hgap hhom
  have havoid : AvoidsQuarterTurnEmbedding U X :=
    avoidsQuarterTurnEmbedding_iff_cosTwo_injective.mpr
      (LinearMap.ker_eq_bot.mp hker)
  have htan : tanTwoThetaEmbedding U X =
      S₂ ∘ₗ inverseOnRange C₂ (LinearMap.ker_eq_bot.mp hker) := by
    simpa [C₂, S₂] using
      tanTwoThetaEmbedding_eq_inverseOnRange U X
        (LinearMap.ker_eq_bot.mp hker)
  have hsolve := internalGap_doubleAngleTangent_uiNorm_le
    N hA hU hδ hgap hriccati hker
  have hres : N (doubleAngleResidual U X R) ≤ 2 * N R :=
    doubleAngleResidual_uiNorm_le N U X R
  refine ⟨havoid, ?_⟩
  simpa [htan, R] using (hsolve.trans hres)

/-- **Davis--Kahan `tan 2Θ`, perturbation form, every UI norm.**

For an arbitrary reducing subspace `V`, angles may lie on either side of
`π/4`.  The theorem proves that no angle equals `π/4` and bounds the norm of
`tan (2Θ)`; the later spectral-selection theorem chooses the acute branch.

Lean proof route for a weaker agent:

1. Use `hoff` and the reducing decompositions of `A` and `B` to derive the finite Riccati equation for the angular operator from `U` to `V`.
2. Prove the cosine-difference denominator is nonzero from `InternalGap A U δ`; this yields `AvoidsQuarterTurn U V` and legitimizes `tanTwoAngleOperator`.
3. Apply the ordered Sylvester/Ky Fan estimate to the Riccati identity and use finite Fan dominance to obtain the arbitrary UI-norm inequality.
-/
theorem tanTwoTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurn U V ∧
      δ * N (tanTwoAngleOperator U V) ≤ 2 * N (B - A) := by
  classical
  let X := V.orthonormalBasis.isometryEquiv.rangeIsometry
  let M := compression B V
  have hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M :=
    reduces_compression_intertwines hB hV
  have hM : M.IsSymmetric := compression_isSymmetric hB
  have hraw := tanTwoTheta_residual_le
    (N.rectangularRestriction X) hA hB hU X hM hBX hoff hδ hgap
  have hR : residual A X M = (B - A) ∘ₗ X.toLinearMap := by
    ext x
    simp [residual, hBX, LinearMap.comp_apply]
  have hN : (N.rectangularRestriction X) ((B - A) ∘ₗ X.toLinearMap) ≤ N (B - A) :=
    N.comp_isometry_le _ X
  refine ⟨?_, ?_⟩
  · simpa [X, AvoidsQuarterTurnEmbedding, approximateSubspace_rangeIsometry] using hraw.1
  · have hident := tanTwoThetaEmbedding_identifies_angleOperator U V X
    rw [hident, hR] at hraw
    exact hraw.2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN zero_le_two)
      (le_of_lt hδ))

/-- The off-diagonal hypotheses and the canonical same-cut spectral choice
imply the acute-angle condition.  This is the branch selection in
Davis--Kahan Theorem 8.1.

Lean proof route for a weaker agent:

1. Consider the path `A_t := A + t • H` and the spectral projection below the fixed cut `a`.
2. Use off-diagonal gap preservation and continuity of the finite Riesz/spectral projection to keep this branch in the acute component starting at `U`.
3. At `t=1`, identify the continued range with `spectralSubspace (A+H) (Set.Iic a)` and rewrite the acute projection condition as `IsAcute`.
-/
theorem isAcute_canonical_tanTwoTheta
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    IsAcute U (spectralSubspace (A + H) (Set.Iic a)) := by
  classical
  let Apath : ℝ → E →ₗ[𝕜] E := fun t => A + (t : 𝕜) • H
  let P : ℝ → E →ₗ[𝕜] E := fun t =>
    projection (spectralSubspace (Apath t) (Set.Iic a))
  have hsymm : ∀ t, (Apath t).IsSymmetric := fun t =>
    hA.add (hH.smul_ofReal t)
  have hgap : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      spectrum 𝕜 (Apath t) ∩ ((Set.Ioo a b : Set ℝ) : Set 𝕜) = ∅ := by
    intro t ht
    exact offDiagonal_gap_repulsion_along_segment hA hH hU hoff hab hUa hUb ht
  have hcont : ContinuousOn P (Set.Icc (0 : ℝ) 1) :=
    spectralProjection_continuousOn_fixedGap hsymm hgap
  have hP0 : P 0 = projection U := by
    simp [P, Apath, spectralSubspace_eq_of_spectrum_split hA hU hUa hUb]
  let G := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ ‖P t - projection U‖ < 1}
  have hGopen : IsOpenIn G (Set.Icc (0 : ℝ) 1) := by
    exact relativeOpen_norm_lt_one hcont
  have hGclosed : IsClosedIn G (Set.Icc (0 : ℝ) 1) := by
    intro t ht htn
    have hquarter := avoidsQuarterTurn_along_segment hA hH hU hoff hab hUa hUb ht
    exact projectionGap_component_closed hquarter htn
  have h0 : (0 : ℝ) ∈ G := by simp [G, hP0]
  have hG : G = Set.Icc (0 : ℝ) 1 :=
    connected_Icc.clopen_eq_univ hGopen hGclosed h0
  have h1 : ‖P 1 - projection U‖ < 1 := by
    have : (1 : ℝ) ∈ G := by rw [hG]; simp
    exact this.2
  simpa [P, Apath, IsAcute, subspaceGap, norm_sub_rev] using h1

/-- Canonical spectral-subspace `tan 2Θ` theorem, with the acute conclusion
built in and the same spectral cut used for `A` and `A+H`.

Lean proof route for a weaker agent:

1. Consider the path `A_t := A + t • H` and the spectral projection below the fixed cut `a`.
2. Use off-diagonal gap preservation and continuity of the finite Riesz/spectral projection to keep this branch in the acute component starting at `U`.
3. At `t=1`, identify the continued range with `spectralSubspace (A+H) (Set.Iic a)` and rewrite the acute projection condition as `IsAcute`.
-/
theorem tanTwoTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    let V := spectralSubspace (A + H) (Set.Iic a)
    IsAcute U V ∧
      (b - a) * N (tanTwoAngleOperator U V) ≤ 2 * N H := by
  intro V
  have hB : (A + H).IsSymmetric := hA.add hH
  have hδ : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hgap : InternalGap A U (b - a) := by
    intro lam mu hlam hmu
    have h1 : lam ≤ a := hUa hlam
    have h2 : b ≤ mu := hUb hmu
    calc b - a ≤ mu - lam := by linarith
      _ ≤ |mu - lam| := le_abs_self _
      _ = |lam - mu| := abs_sub_comm mu lam
  have hoff' : IsOffDiagonal U (A + H - A) := by
    rwa [add_sub_cancel_left]
  have h := tanTwoTheta_perturbation_le N hA hB hU
    (reduces_spectralSubspace (A + H) (Set.Iic a)) hoff' hδ hgap
  rw [add_sub_cancel_left] at h
  exact ⟨isAcute_canonical_tanTwoTheta hA hH hU hoff hab hUa hUb, h.2⟩

/-! ## Davis--Kahan Theorem 8.1: spectral selection and repulsion -/

/-- Existence and uniqueness of the reducing projector on the correct side of
an off-diagonal gap.

Lean proof route for a weaker agent:

1. Consider the path `A_t := A + t • H` and the spectral projection below the fixed cut `a`.
2. Use off-diagonal gap preservation and continuity of the finite Riesz/spectral projection to keep this branch in the acute component starting at `U`.
3. At `t=1`, identify the continued range with `spectralSubspace (A+H) (Set.Iic a)` and rewrite the acute projection condition as `IsAcute`.
-/
theorem existsUnique_reducingSubspace_preserving_gap
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    ∃! V : Submodule 𝕜 E,
      Reduces (A + H) V ∧
      SpectrumIn (A + H) V (Set.Iic a) ∧
      SpectrumIn (A + H) Vᗮ (Set.Ici b) ∧
      IsAcute U V := by
  classical
  let V := spectralSubspace (A + H) (Set.Iic a)
  have hrep := offDiagonal_spectral_repulsion hA hH hU hoff hab hUa hUb
  have hred : Reduces (A + H) V := reduces_spectralSubspace (hA.add hH) _
  have hlow : SpectrumIn (A + H) V (Set.Iic a) :=
    spectralSubspace_spectrumIn (hA.add hH) _
  have hupp : SpectrumIn (A + H) Vᗮ (Set.Ici b) := hrep.upper
  have hacute := isAcute_canonical_tanTwoTheta hA hH hU hoff hab hUa hUb
  refine ⟨V, ⟨hred, hlow, hupp, hacute⟩, ?_⟩
  intro W hW
  have hWspec : W = spectralSubspace (A + H) (Set.Iic a) :=
    reducingSubspace_eq_spectralSubspace_of_split
      (hA.add hH) hW.1 hW.2.1 hW.2.2.1 hab
  simpa [V] using hWspec

/-- Theorem 8.1(i): compression comparison through the cosine block.

Lean proof route for a weaker agent:

1. Use `horder` to orient `U` as the lower spectral block and `Uᗮ` as the upper block.
2. Write `Vᗮ` as the graph of the adjoint angular operator over `Uᗮ`; use `hoff` to compute the compression of `A+H` to that graph.
3. Compare the graph compression with the compression of `A` on `Uᗮ` by a positive congruence, then apply the finite min--max principle to obtain the spectral inclusion.

Signature audit: `horder` now identifies `U` as the lower block and fixes the direction of the
repulsion inequality.
-/
theorem spectral_repulsion_compression
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (horder : OrderedGap A U A Uᗮ δ) :
    SpectrumIn (A + H) Vᗮ
      {lam | ∃ μ ∈ restrictedSpectrum A Uᗮ, μ ≤ lam} := by
  classical
  let X := angularOperator U V hacute
  let C := positiveCosineEquiv U V hacute
  have hgraph : Vᗮ = graphSubspace Uᗮ (-LinearMap.adjoint X) :=
    orthogonal_graph_angularOperator U V hacute
  have hriccati := offDiagonal_Riccati_equation hA hH hU hV hoff hacute
  have hcompression :
      compression (A + H) Vᗮ =
        C.symm.toLinearMap ∘ₗ
          (compression A Uᗮ + positiveGraphCorrection A H U X) ∘ₗ
        C.toLinearMap :=
    graph_compression_formula hA hH hU hoff hriccati
  have hcorr : (positiveGraphCorrection A H U X).IsPositive :=
    graphCorrection_positive_of_orderedGap horder hriccati
  rw [hgraph, hcompression]
  exact spectrum_congruence_add_positive_above hA.compression hcorr

/-- Theorem 8.1(ii): ordered eigenvalues move away from the gap.

Signature audit: The inherited ordered-gap premise fixes the eigenvalue comparison direction.
-/
theorem spectral_repulsion_eigenvalues
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (horder : OrderedGap A U A Uᗮ δ) :
    ∀ lam ∈ restrictedSpectrum (A + H) Vᗮ,
      ∃ μ ∈ restrictedSpectrum A Uᗮ, μ ≤ lam := by
  exact spectral_repulsion_compression hA hH hU hV hoff hacute hδ horder

/-- Theorem 8.1(iii): symmetric-gauge/UI-norm spectral repulsion.

Lean proof route for a weaker agent:

1. Express both compressed operators in eigenbases ordered compatibly with the lower/upper block orientation from `horder`.
2. Use `spectral_repulsion_eigenvalues` to obtain coordinatewise domination of the shifted nonnegative eigenvalues; prove the required singular-value prefix inequalities.
3. Apply finite Fan dominance to `N`, then rewrite the cosine compression and projection compositions into the displayed operators.

Signature audit: The ordered-gap premise fixes the block orientation; the proof must identify
the exact compressed operators before applying Fan dominance.
-/
theorem spectral_repulsion_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (horder : OrderedGap A U A Uᗮ δ)
    {c : ℝ} :
    N (projection Vᗮ ∘ₗ ((A + H) - (c : 𝕜) • LinearMap.id) ∘ₗ projection Vᗮ) ≥
      N (cosThetaMap Uᗮ Vᗮ ∘ₗ
        (projection Uᗮ ∘ₗ (A - (c : 𝕜) • LinearMap.id) ∘ₗ projection Uᗮ)) := by
  classical
  have heig := spectral_repulsion_eigenvalues hA hH hU hV hoff hacute hδ horder
  have hprefix : ∀ k,
      kyFanSingularValueSum 𝕜
        (cosThetaMap Uᗮ Vᗮ ∘ₗ
          (projection Uᗮ ∘ₗ (A - (c : 𝕜) • LinearMap.id) ∘ₗ projection Uᗮ)) k ≤
      kyFanSingularValueSum 𝕜
        (projection Vᗮ ∘ₗ ((A + H) - (c : 𝕜) • LinearMap.id) ∘ₗ projection Vᗮ) k := by
    intro k
    exact minmax_cosine_compression_kyFan_dominance hA hH hU hV hacute heig k c
  exact N.le_of_kyFan_singular_dominance hprefix

/-- Largest-angle consequence: the selected subspaces differ by less than
`π/4`.

Lean proof route for a weaker agent:

1. Consider the path `A_t := A + t • H` and the spectral projection below the fixed cut `a`.
2. Use off-diagonal gap preservation and continuity of the finite Riesz/spectral projection to keep this branch in the acute component starting at `U`.
3. At `t=1`, identify the continued range with `spectralSubspace (A+H) (Set.Iic a)` and rewrite the acute projection condition as `IsAcute`.
-/
theorem largestPrincipalAngle_lt_pi_div_four
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    principalAngles U (spectralSubspace (A + H) (Set.Iic a)) 0 <
      Real.pi / 4 := by
  classical
  let V := spectralSubspace (A + H) (Set.Iic a)
  have hacute := isAcute_canonical_tanTwoTheta hA hH hU hoff hab hUa hUb
  have hδ : 0 < b - a := sub_pos.mpr hab
  have hgap : InternalGap A U (b - a) :=
    internalGap_of_spectrumIn_interval_sides hA hU hUa hUb hab
  have hV : Reduces (A + H) V := reduces_spectralSubspace (hA.add hH) _
  have havoid := (tanTwoTheta_perturbation_le
    (UnitarilyInvariantNorm.opNorm 𝕜 E) hA (hA.add hH) hU hV
    (by simpa using hoff) hδ hgap).1
  have hconnected := principalAngles_continuous_along_offDiagonal_path
    hA hH hU hoff hab hUa hUb
  exact acute_avoidsQuarterTurn_continuation_selects_lower_branch
    hacute havoid hconnected

/-- Operator-norm endpoint already represented by `TanTwoTheta.lean`.
-/
theorem opNorm_tanTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurn U V ∧
      δ * ‖(tanTwoAngleOperator U V).toContinuousLinearMap‖ ≤
        2 * ‖(B - A).toContinuousLinearMap‖ := by
  exact tanTwoTheta_perturbation_le (UnitarilyInvariantNorm.opNorm 𝕜 E)
    hA hB hU hV hoff hδ hgap

/-- Frobenius endpoint.
-/
theorem frobenius_tanTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurn U V ∧
      δ * UnitarilyInvariantNorm.frobenius 𝕜 E (tanTwoAngleOperator U V) ≤
        2 * UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  exact tanTwoTheta_perturbation_le (UnitarilyInvariantNorm.frobenius 𝕜 E)
    hA hB hU hV hoff hδ hgap

/-- Ky Fan endpoint.
-/
theorem kyFan_tanTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ)
    (k : ℕ) :
    AvoidsQuarterTurn U V ∧
      δ * kyFanSum k (tanTwoAngleOperator U V) ≤ 2 * kyFanSum k (B - A) := by
  let NK : UnitarilyInvariantNorm 𝕜 E :=
    (RectangularUnitarilyInvariantNorm.kyFan
      (𝕜 := 𝕜) (E := E) (F := E) k).toSquare
  have h := tanTwoTheta_perturbation_le NK hA hB hU hV hoff hδ hgap
  refine ⟨h.1, ?_⟩
  simpa [NK, RectangularUnitarilyInvariantNorm.toSquare,
    RectangularUnitarilyInvariantNorm.kyFan_apply,
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum,
    kyFanSum_eq_sum_fin] using h.2

end DavisKahanTheory
end ForMathlib
