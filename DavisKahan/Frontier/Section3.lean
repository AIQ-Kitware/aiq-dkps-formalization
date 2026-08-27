/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Geometry.Halmos.TwoProjections
import DavisKahan.Geometry.Halmos.FixedCosineSubspace
import DavisKahan.Geometry.Polar.DirectRotationBlocks
-- supplies the Proposition 3.4 block estimates promoted out of this file: diagonal-block
-- self-adjointness, the `√2/2` norm bound, the half-angle inequality, and the
-- reflection/projection algebra the source statements below consume.
-- supplies the fixed-cosine eigenspace of Proposition 3.5, promoted out of this file
-- along with the `halmosCosineSq` block-application lemmas it needs.  The `BlockCalculus`
-- section below is unrelated and stayed here.  This import is still load-bearing because
-- `inner_starProjection_self_eq` is used by Proposition 3.4 below.
import DavisKahan.Geometry.Halmos.GenericRotationPredicates
import DavisKahan.Geometry.Halmos.UnitaryEquivalence
import DavisKahan.SpectralTheory.SpectralRestriction
-- supplies `compressOperator`
import DavisKahan.SpectralTheory.CircleRieszProjection
import DavisKahan.Sylvester.Spectrum
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import DavisKahan.Geometry.Polar.DirectRotation
-- supplies `spectraReflectionProduct` and `IsUniformlyAcute.symm`
import DavisKahan.Geometry.Polar.DirectRotationSquare
-- supplies `reflectedSubspace` and its projection/conjugation calculus used by
-- Proposition 3.4.  This module imports only `SinTheta`/`SpectralTheory`
-- material and never touches `Frontier`, so the dependency is acyclic.
import DavisKahan.Geometry.Polar.PrincipalSquareRoot
-- supplies Proposition 3.3 -- the principal-unitary-square-root characterisation of a direct
-- rotation -- together with the `U`-block calculus it shares with Proposition 3.1, all
-- promoted out of this file.  This import is load-bearing: `sq_eq_spectraReflectionProduct`,
-- `star_blocks_eq` and `proposition3_3_principalSquareRoot_converse` are used by
-- Propositions 3.1 and 3.4 below.  That module imports only `Geometry` material and never
-- touches `Frontier`, so the dependency is acyclic.
import DavisKahan.InfiniteDimensional.DoubleAngle
-- supplies the completed nonacute construction and acute characterizations used
-- to ground the Proposition 3.2 and Corollary 3.2 source statements below.  The
-- construction depends on the polar and acute machinery under `MathAhead`, which
-- itself never imports this module, so the dependency is acyclic.
import DavisKahan.Geometry.Polar.Section3Nonacute
-- supplies the forward direction of the operator-level Halmos classification
-- (`sameHalmosInvariant_of_pairEquiv`).  That module never imports `Frontier`,
-- so the dependency is acyclic.
import DavisKahan.Geometry.Halmos.Classification
import DavisKahan.Geometry.Halmos.GenericReconstruction
import ForTauCeti.Analysis.InnerProductSpace.CompactApproximationEigenvalues
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.PrescribedSequence
import DavisKahan.Geometry.Halmos.CompactClassification
import ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus
-- supplies the continuous functional calculus over `ℝ` for bounded self-adjoint
-- operators on a real Hilbert space, in unrestricted dimension.  It is what
-- discharges the functional-calculus hypotheses of the Halmos spine at
-- `𝕜 = ℝ`, and so what makes the real-scalar section at the end of this file
-- inhabited rather than vacuous.
import ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
-- supplies `TauCeti.IsAcute` together with
-- `TauCeti.isAcute_iff_inf_orthogonal_eq_bot`, the literal restatement of the
-- paper's Definition 3.2 as the vanishing of the two crossed intersections.
-- Proposition 3.2's nonuniqueness sentence is stated against that definition.
import DavisKahan.Geometry.Halmos.AngleSequenceRealization
-- supplies the diagonal angle datum of a prescribed decreasing sequence, which
-- is what Corollary 3.1's realization sentence asks for.  That module imports
-- only `Geometry/Halmos/Realization` and `ForTauCeti`, so it is acyclic.
import DavisKahan.Geometry.Halmos.Realization
-- supplies the realization half of Theorem 3.1: the explicit direct-rotation
-- construction attaining a prescribed admissible angle datum.  That module
-- imports only `Geometry/Halmos/TwoProjections` and Mathlib, so the dependency
-- is acyclic.

/-!
# Section 3 frontier: separation and classification of two subspaces

These declarations state the remaining source results and the reusable
classification bridges beneath them.  The first completion target is the
constructive nonacute direct-rotation criterion.  The spectral-multiplicity
formulation is separated from the operator-level Halmos classification so the
latter can be completed without inventing direct-integral infrastructure.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Frontier
namespace Section3

open TauCeti.DavisKahanExt (reflectedSubspace starProjection_reflectedSubspace)
open TauCeti.DavisKahan

universe u v

section OneSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- Davis--Kahan 1970, Proposition 3.1: in the acute case the direct rotation
is the unique unitary intertwiner whose diagonal `U`-compressions are positive.

The predicate `IsPaperDirectRotation` records the diagonal compressions only
through their numerical range (`0 ≤ re ⟪x, (P T P) x⟫`), which is strictly
weaker than operator positivity and does not pin the phase on the common part:
on `U = V` every scalar `exp (I * θ)` with `|θ| < π / 2` satisfies all five
fields yet differs from the identity direct rotation.  Uniqueness therefore
needs the diagonal compressions to be self-adjoint (equivalently genuinely
positive operators, which the canonical direct rotation satisfies because its
diagonal blocks are the positive Halmos cosine).  These two self-adjointness
hypotheses are the minimal strengthening; with them the operator squares to the
reflection product and the square-root branch is fixed by accretivity. -/
theorem proposition3_1_positivity_characterization
    (hacute : IsUniformlyAcute U V) (T : H →L[ℂ] H)
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * projection U = projection V * T)
    (hsource_sa : IsSelfAdjoint (projection U * T * projection U))
    (hcomplement_sa :
      IsSelfAdjoint (complementaryProjection U * T * complementaryProjection U)) :
    IsPaperDirectRotation U V T ↔
      T = spectraDirectRotation U V hacute := by
  constructor
  · intro hT
    have hsq : T * T = spectraReflectionProduct U V :=
      sq_eq_spectraReflectionProduct U V T hunitary hintertwines hsource_sa
        hcomplement_sa hT.crossed_blocks
    -- Accretivity fixes the square-root branch.
    have hre : ∀ x, 0 ≤ Complex.re ⟪T x, x⟫_ℂ := by
      intro x
      have h := TauCeti.DavisKahan.re_inner_paperDirectRotation_nonneg U V T hT x
      rwa [← inner_re_symm (𝕜 := ℂ) (T x) x, RCLike.re_eq_complex_re] at h
    exact spectraDirectRotation_unique_of_sq U V hacute T hunitary hsq hre
  · rintro rfl
    exact TauCeti.DavisKahan.spectraDirectRotation_isPaperDirectRotation U V hacute

omit [CompleteSpace H] [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection] in
/-- The paper's crossed intersections are exactly the Halmos source and target
defect spaces. -/
theorem crossed_intersections_are_halmos_defects :
    halmosSourceDefect U V = U ⊓ Vᗮ ∧
      halmosTargetDefect U V = Uᗮ ⊓ V :=
  ⟨rfl, rfl⟩

/-- Davis--Kahan 1970, Proposition 3.4 in source form: the square of the direct
rotation is the direct rotation between the reflected source and target
subspaces.  The natural reflected pair is `Uref = U`, `Vref = reflectedSubspace
V U`, for which `spectraDirectRotation U V hacute` squared is the ordered
reflection product `R_V R_U = spectraReflectionProduct U V` (see
`spectraDirectRotation_sq`).  Because `reflectionOperator (reflectedSubspace V U)
= R_V R_U R_V`, the reflection product of the reflected pair is `(R_V R_U) ^ 2`,
so `R_V R_U` is a unitary square root of it; the accretive branch is the direct
rotation between the reflected subspaces.

Two hypothesis corrections are recorded here relative to the originally printed
statement.  First, the half-angle threshold is on the cosine *square*,
`re ⟪halmosCosineSq x, x⟫ ≥ ‖x‖ ^ 2 / 2` (cosine `≥ 1 / √2`, double angle
`≤ π / 2`); it is *not* the pointwise bound `re ⟪|S| x, x⟫ ≥ ‖x‖ ^ 2 / 2`, which
is strictly weaker since `|S| ≤ 1`.  The algebra `2 S = 1 + R_V R_U` together
with the normality identity `Re S = S⋆ S = |S| ^ 2 = halmosCosineSq` shows this
cosine-square bound is exactly accretivity of `R_V R_U`
(`re_inner_reflectionProduct_nonneg`), which is the branch condition needed to
identify the square root with the direct rotation.

Second, acuteness of the reflected pair `IsUniformlyAcute U (reflectedSubspace V U)` is
carried as an *independent* hypothesis.  It is genuinely not derivable from the
cosine-square bound and is not implied by it: a boundary cosine square of `1/2`
makes the double angle exactly `π / 2`, so the reflected pair has gap `1` and is
not acute, while the cosine-square bound still holds nonstrictly.  Conversely
acuteness of the reflected pair alone does not force accretivity of `R_V R_U`:
a pair carrying a single principal angle in `(π/4, π/2)` has an acute reflected
pair (double angle folded below `π/2`) yet a reflection product with strictly
negative numerical real part on the corresponding vectors, so the conclusion
fails without the cosine-square bound.  Both conditions are therefore necessary;
a single uniform spectral-gap field on `R_V R_U` would subsume them, but the
present two-hypothesis form is the faithful minimal correction. -/
theorem proposition3_4_square_is_reflected_directRotation
    (hacute : IsUniformlyAcute U V)
    (hacuteReflected : IsUniformlyAcute U (reflectedSubspace V U))
    (hhalf : ∀ x : H,
      0 ≤ RCLike.re
        ⟪x, halmosCosineSq U V x⟫_ℂ - ‖x‖ ^ 2 / 2) :
    -- the reflected pair is existentially quantified, so its orthogonal
    -- projections cannot be found by instance search; they are bound here and
    -- reinstated with `haveI` inside the body
    ∃ (Uref Vref : Submodule ℂ H) (iU : Uref.HasOrthogonalProjection)
        (iV : Vref.HasOrthogonalProjection),
      haveI : Uref.HasOrthogonalProjection := iU
      haveI : Vref.HasOrthogonalProjection := iV
      ∃ hacuteRef : IsUniformlyAcute Uref Vref,
        spectraDirectRotation U V hacute *
            spectraDirectRotation U V hacute =
          spectraDirectRotation Uref Vref hacuteRef := by
  refine ⟨U, reflectedSubspace V U, inferInstance, inferInstance, hacuteReflected, ?_⟩
  have hWsq : spectraDirectRotation U V hacute * spectraDirectRotation U V hacute
      = spectraReflectionProduct U V := spectraDirectRotation_sq U V hacute
  rw [hWsq]
  have hGunit : spectraReflectionProduct U V ∈ unitary (H →L[ℂ] H) :=
    spectraReflectionProduct_mem_unitary U V
  have hGsq : spectraReflectionProduct U V * spectraReflectionProduct U V
      = spectraReflectionProduct U (reflectedSubspace V U) := by
    show spectraReflectionProduct U V * spectraReflectionProduct U V
      = reflectionOperator (reflectedSubspace V U) * reflectionOperator U
    rw [reflectionOperator_reflectedSubspace U V]
    show (reflectionOperator V * reflectionOperator U)
        * (reflectionOperator V * reflectionOperator U)
      = reflectionOperator V * reflectionOperator U * reflectionOperator V
        * reflectionOperator U
    noncomm_ring
  have hGre : ∀ x, 0 ≤ Complex.re ⟪spectraReflectionProduct U V x, x⟫_ℂ :=
    re_inner_reflectionProduct_nonneg U V hhalf
  exact spectraDirectRotation_unique_of_sq U (reflectedSubspace V U) hacuteReflected
    (spectraReflectionProduct U V) hGunit hGsq hGre

/-- Davis--Kahan 1970, Corollary 3.2, quarter-turn half: interchanging the subspaces
reverses the canonical quarter-turn. -/
theorem corollary3_2_reversal_source_form
    (hacute : IsUniformlyAcute U V) :
    spectraDirectRotation V U
        (_root_.TauCeti.DavisKahan.IsUniformlyAcute.symm hacute) =
      star (spectraDirectRotation U V hacute) :=
  TauCeti.DavisKahan.corollary3_2_reversal_completed U V hacute

/-- Davis--Kahan 1970, Corollary 3.2, angle half: interchanging the subspaces leaves the
angle operator unchanged.  The two projections enter the angle operator only through
their difference, and the absolute value is insensitive to its sign. -/
theorem corollary3_2_sinAngleOperator_symm :
    DavisKahanExt.sinAngleOperator V U = DavisKahanExt.sinAngleOperator U V := by
  rw [DavisKahanExt.sinAngleOperator, DavisKahanExt.sinAngleOperator,
    ← DavisKahanExt.operatorAbsoluteValue_neg]
  congr 1
  abel

/-- **Davis--Kahan 1970, Corollary 3.2**, both halves in one statement: swapping the pair
leaves the angle operator unchanged and reverses the quarter-turn. -/
theorem corollary3_2_reversal
    (hacute : IsUniformlyAcute U V) :
    DavisKahanExt.sinAngleOperator V U = DavisKahanExt.sinAngleOperator U V ∧
      spectraDirectRotation V U
          (_root_.TauCeti.DavisKahan.IsUniformlyAcute.symm hacute) =
        star (spectraDirectRotation U V hacute) :=
  ⟨corollary3_2_sinAngleOperator_symm U V, corollary3_2_reversal_source_form U V hacute⟩

/-! ### Proposition 3.4 at the printed scope

`proposition3_4_square_is_reflected_directRotation` above is true and axiom-clean, but it is
not the printed statement: it exhibits *an* unnamed acute pair, from a whole-space form bound,
under an extra acuteness hypothesis.  The printed statement names the pair `(Q₋ℋ, Qℋ)`, its
hypothesis is `C₀² ≥ ½` on `Pℋ` alone, and it assumes nothing about the reflected pair.

The three declarations that close those gaps are source-facing and live in
`DavisKahan/Sources/DavisKahan1970/Section3Proposition34.lean`, together with the printed
sentence `proposition3_4_source`.  The block estimates they run on were promoted to
`DavisKahan/Geometry/Polar/DirectRotationBlocks.lean`.
-/

end OneSpace

/-! ## Proposition 3.2, the nonacute existence criterion

Stated over an arbitrary `RCLike` field.  Nothing in the nonacute construction
is complex-specific: the crossed-defect quarter turn is built out of the polar
factor of `Q P + Qᗮ Pᗮ`, and the only field-dependent ingredient is the
continuous functional calculus that the modulus runs on, carried here as a
hypothesis exactly as `ForTauCeti`'s modulus API carries it.  Typeclass
inference discharges it at `𝕜 = ℂ` and, through
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`, at
`𝕜 = ℝ`.

These statements used to live in `section OneSpace` above, over `ℂ`.  They were
moved rather than duplicated: `section OneSpace` also carries Propositions 3.3
and 3.5, whose square-root branch selection is genuinely complex
(`spectrum ℂ T` and `ComplexOrder`), so the two groups cannot share one variable
block. -/

section NonacuteExistence

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]
variable [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)]
  [ContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

/-- Davis--Kahan 1970, Proposition 3.2: a nonacute direct rotation exists
exactly when the crossed defect spaces have equal Hilbert dimension, expressed
constructively by a linear isometric equivalence. -/
theorem proposition3_2_exists_iff_crossedDefectsEquivalent :
    (∃ T : H →L[𝕜] H, IsPaperDirectRotation U V T) ↔
      CrossedDefectsEquivalent U V :=
  TauCeti.DavisKahan.proposition3_2_completed U V

/-- Explicit parameterization of the freedom in Proposition 3.2.  Distinct
unitaries between the crossed defect spaces must produce distinct direct
rotations. -/
theorem proposition3_2_parameterized_nonuniqueness
    (hdefect : CrossedDefectsEquivalent U V) :
    ∃ build :
        (halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) →
          (H →L[𝕜] H),
      (∀ J, IsPaperDirectRotation U V (build J)) ∧
      Function.Injective build :=
  TauCeti.DavisKahan.proposition3_2_parameterization_completed U V hdefect

omit [CompleteSpace H] [Algebra ℝ (H →L[𝕜] H)] [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- **In the nonacute case the crossed defect spaces are nonzero.**

The paper's Definition 3.2 declares the pair acute exactly when both crossed
intersections `U ⊓ Vᗮ` and `Uᗮ ⊓ V` vanish, so failing to be acute makes at
least one of them nonzero; the isometry supplied by (3.5) then transports that
to the source defect. -/
theorem halmosSourceDefect_ne_bot_of_not_isAcute
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    halmosSourceDefect U V ≠ ⊥ := by
  obtain ⟨J⟩ := hdefect
  intro hbot
  refine hnonacute (TauCeti.isAcute_iff_inf_orthogonal_eq_bot.mpr ⟨hbot, ?_⟩)
  refine (Submodule.eq_bot_iff _).mpr fun y hy => ?_
  have hzero : ((J.symm ⟨y, hy⟩ : halmosSourceDefect U V) : H) = 0 :=
    (Submodule.eq_bot_iff _).mp hbot _ (J.symm ⟨y, hy⟩).2
  have hsymm : (J.symm ⟨y, hy⟩ : halmosSourceDefect U V) = 0 := Subtype.ext hzero
  have htarget : (⟨y, hy⟩ : halmosTargetDefect U V) = 0 := by
    have h := congrArg J hsymm
    rwa [J.apply_symm_apply, map_zero] at h
  exact congrArg Subtype.val htarget

/-- **Davis--Kahan 1970, Proposition 3.2, second printed sentence: "It is not
unique."**

In the nonacute case a direct rotation, once it exists, is never unique.  The
witnesses are produced by feeding an isometry `J` of the crossed defect spaces
and its negation `-J` through the injective parameterization
`proposition3_2_parameterized_nonuniqueness`.  Over a field of characteristic
zero `J ≠ -J` requires a nonzero defect space, and that is supplied by the
nonacute hypothesis rather than assumed separately: the paper's acute case is
precisely the vanishing of both crossed intersections.

This is the paper's own reason for the nonuniqueness -- "This extension is not
unique (even if `dim Null(C₀) = 1`), and the nonuniqueness will survive" -- with
the arbitrary unitary extension replaced by the single sign change, which is
enough to refute uniqueness. -/
theorem proposition3_2_not_unique
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    ∃ T₁ T₂ : H →L[𝕜] H,
      IsPaperDirectRotation U V T₁ ∧ IsPaperDirectRotation U V T₂ ∧ T₁ ≠ T₂ := by
  obtain ⟨build, hbuild, hinj⟩ :=
    proposition3_2_parameterized_nonuniqueness U V hdefect
  obtain ⟨J⟩ := hdefect
  obtain ⟨x, hxmem, hxne⟩ :=
    Submodule.ne_bot_iff _ |>.mp
      (halmosSourceDefect_ne_bot_of_not_isAcute U V ⟨J⟩ hnonacute)
  refine ⟨build J, build (J.trans (LinearIsometryEquiv.neg 𝕜)), hbuild _, hbuild _, ?_⟩
  intro hEq
  have hJJ : J = J.trans (LinearIsometryEquiv.neg 𝕜) := hinj hEq
  have hval : J ⟨x, hxmem⟩ = -J ⟨x, hxmem⟩ :=
    congrArg (fun e : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V =>
      e ⟨x, hxmem⟩) hJJ
  have hsrc : (⟨x, hxmem⟩ : halmosSourceDefect U V) = -⟨x, hxmem⟩ := by
    refine J.injective ?_
    rw [map_neg]
    exact hval
  have htwo : (2 : 𝕜) • (⟨x, hxmem⟩ : halmosSourceDefect U V) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hsrc
  rcases smul_eq_zero.mp htwo with h2 | hx0
  · exact absurd h2 two_ne_zero
  · exact hxne (congrArg Subtype.val hx0)

/-- **Proposition 3.2's nonuniqueness in literal `∃!` form.** -/
theorem proposition3_2_not_existsUnique
    (hdefect : CrossedDefectsEquivalent U V) (hnonacute : ¬ TauCeti.IsAcute U V) :
    ¬ ∃! T : H →L[𝕜] H, IsPaperDirectRotation U V T := by
  rintro ⟨T, _, huniq⟩
  obtain ⟨T₁, T₂, h₁, h₂, hne⟩ := proposition3_2_not_unique U V hdefect hnonacute
  exact hne ((huniq T₁ h₁).trans (huniq T₂ h₂).symm)
end NonacuteExistence

/-! ## Theorem 3.1, the operator-level classification

Stated over an arbitrary `RCLike` field.  Nothing in the Halmos spine is
complex-specific; the only field-dependent ingredient is the continuous
functional calculus used by the polar decomposition of the cross block, and it
is carried as a hypothesis exactly as `ForTauCeti`'s modulus API carries it. -/

section OperatorClassification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- Equality of the four elementary Halmos summands, expressed without a
finite-rank substitute. -/
structure SameHalmosTrivialDimensions : Prop where
  common : Nonempty
    (halmosCommonPart U₁ V₁ ≃ₗᵢ[𝕜] halmosCommonPart U₂ V₂)
  sourceDefect : Nonempty
    (halmosSourceDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosSourceDefect U₂ V₂)
  targetDefect : Nonempty
    (halmosTargetDefect U₁ V₁ ≃ₗᵢ[𝕜] halmosTargetDefect U₂ V₂)
  exterior : Nonempty
    (halmosExteriorPart U₁ V₁ ≃ₗᵢ[𝕜] halmosExteriorPart U₂ V₂)

/-- The modern operator-level complete invariant: trivial dimensions plus the
unitary-equivalence class of the angle operator `cos²Θ`.

**The angle operator is read on the `U`-side, as the compression of `P_V` to
`U ⊓ generic`** — the `genericCosineBlock` of `Geometry/Halmos/GenericPosition`.
That is the operator whose spectral multiplicity function Davis and Kahan's
Theorem 3.1 uses.

This field used to record `genericHalmosCosineSq`, the compression of the
symmetrized `P_U P_V P_U + P_Uᗮ P_Vᗮ P_Uᗮ`.  On the generic part that operator is
the cosine block on the `U`-half and `1 - D` on the `Uᗮ`-half, i.e. `A ⊕ A`
(`coe_genericHalmosCosineSq_of_mem_left` proves the `M` half).  Recovering `A`
from `A ⊕ A` up to unitary equivalence is multiplicity-halving — Hahn--Hellinger,
which Mathlib does not have — whereas the pair `(U, V)` is determined by `A`
alone by elementary means.  The symmetrized reading was a repository choice that
doubled the multiplicity and put multiplicity theory on the critical path for no
mathematical reason.  Changed 2026-08-04, which is what closes
`twoProjection_operator_classification`. -/
structure SameHalmosOperatorInvariant : Prop where
  trivial : SameHalmosTrivialDimensions U₁ V₁ U₂ V₂
  generic : BoundedOperatorsUnitaryEquivalent
    (genericCosineBlock U₁ V₁)
    (genericCosineBlock U₂ V₂)

/-- Forward direction of the operator-level Halmos classification: a unitary
equivalence of the ordered pairs induces the complete operator invariant.  The
restriction of the equivalence to each elementary Halmos summand is a linear
isometric equivalence, and on the generic remainder it intertwines the
cosine-square operator.  Proved axiom-clean in
`sameHalmosInvariant_of_pairEquiv`. -/
theorem sameHalmosOperatorInvariant_of_pairEquiv
    (h : PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂) :
    SameHalmosOperatorInvariant U₁ V₁ U₂ V₂ := by
  obtain ⟨hc, hs, ht, he, _⟩ :=
    sameHalmosInvariant_of_pairEquiv U₁ V₁ U₂ V₂ h
  exact ⟨⟨hc, hs, ht, he⟩,
    exists_cosineBlockEquiv_of_pairEquiv U₁ V₁ U₂ V₂ h⟩

/-! ### Corollary 3.1 with the printed compactness hypothesis

Davis and Kahan assume `P tilde(Q) P = P (I - Q) P` compact -- the *defect*
(sine-square) block -- not `P Q P`.  In infinite dimension the two are
incomparable: `P(I-Q)P` compact says the principal angles accumulate only at
`0`, while `PQP` compact says they accumulate only at `pi/2`, and neither
implies the other unless `P` itself is compact.

The repair is exact rather than approximate, because `P (I - Q) P = P P_{Vᗮ} P`:
the defect block of the pair `(U, V)` *is* the cosine block of the pair
`(U, Vᗮ)`.  So the printed corollary is the compiled one applied to
`(U, Vᗮ)`, once one knows that complementing the second subspace preserves
pair-equivalence and merely permutes the four elementary Halmos summands.
-/

variable {U₁ V₁ U₂ V₂}

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection] in
/-- Complementing the second subspace of each pair preserves unitary
equivalence of ordered pairs. -/
theorem pairOfSubspacesUnitaryEquivalent_orthogonal_right
    (h : PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ᗮ U₂ V₂ᗮ := by
  obtain ⟨e, hU, hV⟩ := h
  refine ⟨e, hU, ?_⟩
  have hmap : V₁ᗮ.map (e.toLinearEquiv : H₁ →ₗ[𝕜] H₂) =
      (V₁.map (e.toLinearEquiv : H₁ →ₗ[𝕜] H₂))ᗮ :=
    Submodule.map_orthogonal_equiv V₁ e
  have hcoe : (e.toLinearEquiv : H₁ →ₗ[𝕜] H₂) = e.toLinearMap := rfl
  rw [hcoe] at hmap
  rw [hmap, hV]

variable (U₁ V₁ U₂ V₂)

omit [CompleteSpace H₁] [CompleteSpace H₂] [U₁.HasOrthogonalProjection]
  [U₂.HasOrthogonalProjection] in
theorem pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ᗮ U₂ V₂ᗮ ↔
      PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ := by
  refine ⟨fun h => ?_, pairOfSubspacesUnitaryEquivalent_orthogonal_right⟩
  have h' := pairOfSubspacesUnitaryEquivalent_orthogonal_right h
  rwa [Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal] at h'

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Transport a nonempty isometric equivalence of submodules along equalities
of those submodules.  Needed because the two summand families below are equal
as submodules but the `≃ₗᵢ` type former does not rewrite. -/
private theorem nonempty_linearIsometryEquiv_congr
    {X X' : Submodule 𝕜 H₁} {Y Y' : Submodule 𝕜 H₂}
    (hX : X = X') (hY : Y = Y') (h : Nonempty (X ≃ₗᵢ[𝕜] Y)) :
    Nonempty (X' ≃ₗᵢ[𝕜] Y') :=
  h.map fun f =>
    ((LinearIsometryEquiv.ofEq X' X hX.symm).trans f).trans
      (LinearIsometryEquiv.ofEq Y Y' hY)

omit [U₁.HasOrthogonalProjection] [U₂.HasOrthogonalProjection] [CompleteSpace H₁]
  [CompleteSpace H₂] in
/-- Complementing the second subspace permutes the four elementary Halmos
summands: `U ⊓ V` swaps with `U ⊓ Vᗮ`, and `Uᗮ ⊓ V` with `Uᗮ ⊓ Vᗮ`. -/
theorem sameHalmosTrivialDimensions_orthogonal_right_iff :
    SameHalmosTrivialDimensions U₁ V₁ᗮ U₂ V₂ᗮ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ := by
  have hVV1 : V₁ᗮᗮ = V₁ := Submodule.orthogonal_orthogonal V₁
  have hVV2 : V₂ᗮᗮ = V₂ := Submodule.orthogonal_orthogonal V₂
  have e1 : U₁ ⊓ V₁ᗮᗮ = U₁ ⊓ V₁ := by rw [hVV1]
  have e2 : U₂ ⊓ V₂ᗮᗮ = U₂ ⊓ V₂ := by rw [hVV2]
  have e3 : U₁ᗮ ⊓ V₁ᗮᗮ = U₁ᗮ ⊓ V₁ := by rw [hVV1]
  have e4 : U₂ᗮ ⊓ V₂ᗮᗮ = U₂ᗮ ⊓ V₂ := by rw [hVV2]
  constructor
  · rintro ⟨hc, hs, ht, he⟩
    exact ⟨nonempty_linearIsometryEquiv_congr e1 e2 hs, hc,
      nonempty_linearIsometryEquiv_congr e3 e4 he, ht⟩
  · rintro ⟨hc, hs, ht, he⟩
    exact ⟨hs, nonempty_linearIsometryEquiv_congr e1.symm e2.symm hc,
      he, nonempty_linearIsometryEquiv_congr e3.symm e4.symm ht⟩

/-! The converse direction reconstructs the pair from the cosine block through the
polar decomposition of the Halmos cross block, so it carries the functional-calculus
hypotheses of `Geometry/Halmos/GenericReconstruction.lean`.  They are found by typeclass
inference at `𝕜 = ℂ` and at `𝕜 = ℝ` alike. -/

variable [Algebra ℝ (genericLeftHalf U₁ V₁ →L[𝕜]
    genericLeftHalf U₁ V₁)]
  [IsScalarTower ℝ 𝕜 (genericLeftHalf U₁ V₁ →L[𝕜]
    genericLeftHalf U₁ V₁)]
  [ContinuousFunctionalCalculus ℝ
    (genericLeftHalf U₁ V₁ →L[𝕜]
      genericLeftHalf U₁ V₁) IsSelfAdjoint]
variable [Algebra ℝ (genericLeftHalf U₂ V₂ →L[𝕜]
    genericLeftHalf U₂ V₂)]
  [IsScalarTower ℝ 𝕜 (genericLeftHalf U₂ V₂ →L[𝕜]
    genericLeftHalf U₂ V₂)]
  [ContinuousFunctionalCalculus ℝ
    (genericLeftHalf U₂ V₂ →L[𝕜]
      genericLeftHalf U₂ V₂) IsSelfAdjoint]

/-- **Operator-level Halmos classification, both directions.**  This is the
constructive spine of Davis--Kahan Theorem 3.1 and needs no direct-integral
presentation, no compactness, no finite dimension and no separability.

Grounded by `:=` on
`pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant`,
so there is a single source of truth.  The forward direction restricts a
pair-equivalence to the `U`-half of the generic part; the converse is bricks (1)
and (2) — brick (1) reconstructs the generic-part unitary from the cosine block
alone (`Geometry/Halmos/GenericReconstruction`), brick (2) glues it to the four
elementary summand isometries (`Geometry/Halmos/Assembly`). -/
theorem twoProjection_operator_classification :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosOperatorInvariant U₁ V₁ U₂ V₂ := by
  rw [pairOfSubspacesUnitaryEquivalent_iff_sameHalmosCosineBlockInvariant
    U₁ V₁ U₂ V₂]
  constructor
  · rintro ⟨hc, hs, ht, he, hg⟩
    exact ⟨⟨hc, hs, ht, he⟩, hg⟩
  · rintro ⟨⟨hc, hs, ht, he⟩, hg⟩
    exact ⟨hc, hs, ht, he, hg⟩

/-! ### Corollary 3.1, the decreasing eigenvalue list

The paper's Corollary 3.1 replaces the operator invariant of Theorem 3.1 by the
*decreasing eigenvalue list* of the angle operator.  Everything here is stated
over an arbitrary `RCLike` field, exactly like the operator-level spine above:
the eigenvalues of a compact positive self-adjoint operator are real, so the
list is `ℝ`-valued whatever the scalar field is, and only the embedding of an
eigenvalue back into the field changes with `𝕜`. -/

/-- Ordered eigenvalue data for a compact positive contraction: the
approximation-number sequence of `A`.

For a compact **positive** operator this is exactly the ordered eigenvalue list
*with multiplicity* — `aₙ(A)` is the `n`-th largest singular value, and singular
values coincide with eigenvalues when the operator is positive, so a repeated
eigenvalue is repeated in the sequence.  That is the implementation this
declaration's earlier open body was documented as wanting.

The list is `ℝ`-valued over every scalar field, because the eigenvalues of a
compact positive self-adjoint operator are real.

Note the definition is total: it is stated for every `A`, and only *means* the
angle eigenvalue list under the compactness and positivity hypotheses that the
consumers carry.  This mirrors `approximationNumber` itself, which is total in
the same way. -/
noncomputable def compactAngleEigenvalueList
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [CompleteSpace K] (A : K →L[𝕜] K) : ℕ → ℝ :=
  fun n => A.approximationNumber n

/-- **Approximation numbers are a unitary invariant.**  Conjugating by a linear isometric
equivalence sandwiches the operator between two contractions in both directions, so no
approximation number can move. -/
theorem approximationNumber_eq_of_boundedOperatorsUnitaryEquivalent
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    (h : BoundedOperatorsUnitaryEquivalent A B) (n : ℕ) :
    A.approximationNumber n = B.approximationNumber n := by
  obtain ⟨U, hU⟩ := h
  have hUapp : ∀ x, B (U x) = U (A x) := fun x => (hU x).symm
  have hUnorm : ‖(U : E →L[𝕜] F)‖ ≤ 1 :=
    U.toLinearIsometry.norm_toContinuousLinearMap_le
  have hUsnorm : ‖(U.symm : F →L[𝕜] E)‖ ≤ 1 :=
    U.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  have hBfact : B = (U : E →L[𝕜] F) ∘L A ∘L (U.symm : F →L[𝕜] E) := by
    ext y
    change B y = U (A (U.symm y))
    rw [← hUapp (U.symm y), U.apply_symm_apply]
  have hAfact : A = (U.symm : F →L[𝕜] E) ∘L B ∘L (U : E →L[𝕜] F) := by
    ext x
    change A x = U.symm (B (U x))
    rw [hUapp x, U.symm_apply_apply]
  refine le_antisymm ?_ ?_
  · conv_lhs => rw [hAfact]
    exact TauCeti.ApproximationNumber.approximationNumber_comp_contractions_le
      (U.symm : F →L[𝕜] E) (U : E →L[𝕜] F) hUsnorm hUnorm n
  · conv_lhs => rw [hBfact]
    exact TauCeti.ApproximationNumber.approximationNumber_comp_contractions_le
      (U : E →L[𝕜] F) (U.symm : F →L[𝕜] E) hUnorm hUsnorm n

/-- Davis--Kahan 1970, Corollary 3.1: when the cross-projection is compact, the
angle eigenvalue lists and elementary multiplicities classify the pair. -/
theorem corollary3_1_compact_angleList_classification
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L projection V₁ ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L projection V₂ ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (genericCosineBlock U₁ V₁) =
        compactAngleEigenvalueList
          (genericCosineBlock U₂ V₂) := by
  have hpos₁ : ∀ x, 0 ≤ RCLike.re
      ⟪genericCosineBlock U₁ V₁ x, x⟫_𝕜 := by
    intro x
    rw [re_inner_genericCosineBlock]
    positivity
  have hpos₂ : ∀ x, 0 ≤ RCLike.re
      ⟪genericCosineBlock U₂ V₂ x, x⟫_𝕜 := by
    intro x
    rw [re_inner_genericCosineBlock]
    positivity
  rw [twoProjection_operator_classification U₁ V₁ U₂ V₂]
  constructor
  · rintro ⟨htriv, hgen⟩
    refine ⟨htriv, ?_⟩
    funext n
    exact approximationNumber_eq_of_boundedOperatorsUnitaryEquivalent hgen n
  · rintro ⟨htriv, hlist⟩
    refine ⟨htriv, ?_⟩
    obtain ⟨W, hW⟩ :=
      TauCeti.exists_linearIsometryEquiv_intertwining_of_approximationNumber_eq
        (isCompactOperator_genericCosineBlock U₁ V₁ hcompact₁)
        (isSelfAdjoint_genericCosineBlock U₁ V₁)
        hpos₁
        (eigenspace_genericCosineBlock_zero U₁ V₁)
        (isCompactOperator_genericCosineBlock U₂ V₂ hcompact₂)
        (isSelfAdjoint_genericCosineBlock U₂ V₂)
        hpos₂
        (eigenspace_genericCosineBlock_zero U₂ V₂)
        (fun n => congrFun hlist n)
    exact ⟨W, hW⟩

end OperatorClassification

/-! ## Corollary 3.1 with the printed compactness hypothesis, over an arbitrary field

The defect-block form of Corollary 3.1 is the cosine-block form applied to `(U, Vᗮ)`, so it
is field-generic exactly as that form is.  It is separated from `section
OperatorClassification` only because the reconstruction functional calculus it needs is the
one on the generic left half of `(U, Vᗮ)`, while that section's calculus variables are
pinned to `(U, V)`; carrying both would attach four hypotheses that this statement never
uses. -/

section DefectBlockClassification

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule 𝕜 H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule 𝕜 H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

variable [Algebra ℝ (genericLeftHalf U₁ V₁ᗮ →L[𝕜]
    genericLeftHalf U₁ V₁ᗮ)]
  [IsScalarTower ℝ 𝕜 (genericLeftHalf U₁ V₁ᗮ →L[𝕜]
    genericLeftHalf U₁ V₁ᗮ)]
  [ContinuousFunctionalCalculus ℝ
    (genericLeftHalf U₁ V₁ᗮ →L[𝕜]
      genericLeftHalf U₁ V₁ᗮ) IsSelfAdjoint]
variable [Algebra ℝ (genericLeftHalf U₂ V₂ᗮ →L[𝕜]
    genericLeftHalf U₂ V₂ᗮ)]
  [IsScalarTower ℝ 𝕜 (genericLeftHalf U₂ V₂ᗮ →L[𝕜]
    genericLeftHalf U₂ V₂ᗮ)]
  [ContinuousFunctionalCalculus ℝ
    (genericLeftHalf U₂ V₂ᗮ →L[𝕜]
      genericLeftHalf U₂ V₂ᗮ) IsSelfAdjoint]

/-- **Davis--Kahan 1970, Corollary 3.1, with the printed hypothesis.**

The compactness assumption is on the *defect* block `P (I - Q) P`, as printed,
and the classifying list is the eigenvalue list of the corresponding
sine-square angle operator. -/
theorem corollary3_1_compact_defectBlock_angleList_classification
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L
        (ContinuousLinearMap.id 𝕜 H₁ - projection V₁) ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L
        (ContinuousLinearMap.id 𝕜 H₂ - projection V₂) ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (genericCosineBlock U₁ V₁ᗮ) =
        compactAngleEigenvalueList
          (genericCosineBlock U₂ V₂ᗮ) := by
  have hperp₁ : projection V₁ᗮ =
      ContinuousLinearMap.id 𝕜 H₁ - projection V₁ := by
    show V₁ᗮ.starProjection = ContinuousLinearMap.id 𝕜 H₁ - V₁.starProjection
    rw [Submodule.starProjection_orthogonal' V₁]
    rfl
  have hperp₂ : projection V₂ᗮ =
      ContinuousLinearMap.id 𝕜 H₂ - projection V₂ := by
    show V₂ᗮ.starProjection = ContinuousLinearMap.id 𝕜 H₂ - V₂.starProjection
    rw [Submodule.starProjection_orthogonal' V₂]
    rfl
  have h₁ : IsCompactOperator (projection U₁ ∘L projection V₁ᗮ ∘L projection U₁) := by
    rwa [hperp₁]
  have h₂ : IsCompactOperator (projection U₂ ∘L projection V₂ᗮ ∘L projection U₂) := by
    rwa [hperp₂]
  rw [← pairOfSubspacesUnitaryEquivalent_orthogonal_right_iff U₁ V₁ U₂ V₂,
    ← sameHalmosTrivialDimensions_orthogonal_right_iff U₁ V₁ U₂ V₂]
  exact corollary3_1_compact_angleList_classification U₁ V₁ᗮ U₂ V₂ᗮ h₁ h₂

end DefectBlockClassification


/-! ## From the generic cosine block to the ambient block

Corollary 3.1's classifying invariant is the eigenvalue list of the *generic* cosine
block `genericCosineBlock U V`, an operator on the `U`-half of the generic part, while a
realization is naturally computed for the *ambient* block `P_U P_V P_U` on the whole
space.  When the four elementary Halmos summands are trivial the two carry the same
eigenvalue list, because the generic part is then everything and the ambient block is the
extension of the generic block by zero off `U`. -/

section GenericAmbientBridge


variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

omit [CompleteSpace H] [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- With the four elementary Halmos summands trivial, the generic part is everything and
the `U`-half of it is `U` itself. -/
theorem genericLeftHalf_eq_of_halmosTrivialPart_eq_bot
    (h : halmosTrivialPart U V = ⊥) : genericLeftHalf U V = U := by
  have hgen : halmosGenericPart U V = ⊤ := by
    show (halmosTrivialPart U V)ᗮ = ⊤
    rw [h]
    exact Submodule.bot_orthogonal_eq_top
  show U ⊓ halmosGenericPart U V = U
  rw [hgen, inf_top_eq]

/-- The orthogonal projection onto the `U`-half of the generic part is the projection onto
`U` when the four elementary Halmos summands are trivial. -/
theorem starProjection_genericLeftHalf_eq_of_halmosTrivialPart_eq_bot
    (h : halmosTrivialPart U V = ⊥) (x : H) :
    (genericLeftHalf U V).starProjection x = U.starProjection x :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((genericLeftHalf_eq_of_halmosTrivialPart_eq_bot U V h).ge (U.starProjection_apply_mem x))
    fun w hw =>
      Submodule.starProjection_inner_eq_zero x w
        ((genericLeftHalf_eq_of_halmosTrivialPart_eq_bot U V h).le hw)

/-- **The ambient block is the generic cosine block extended by zero.**

`genericCosineBlock U V` is the compression of `P_V` to the `U`-half of the generic part;
when the four elementary Halmos summands are trivial that half is `U`, and transporting the
block back to the ambient space by the inclusion and the orthogonal projection reproduces
`P_U P_V P_U` exactly. -/
theorem subtypeL_comp_genericCosineBlock_comp_orthogonalProjectionOnto
    (h : halmosTrivialPart U V = ⊥) :
    (genericLeftHalf U V).subtypeL ∘L genericCosineBlock U V ∘L
        (genericLeftHalf U V).orthogonalProjectionOnto =
      U.starProjection ∘L V.starProjection ∘L U.starProjection := by
  have hproj := starProjection_genericLeftHalf_eq_of_halmosTrivialPart_eq_bot U V h
  refine ContinuousLinearMap.ext fun x => ?_
  have hcoe : ∀ m : genericLeftHalf U V,
      ((genericCosineBlock U V m : genericLeftHalf U V) : H) =
        (genericLeftHalf U V).starProjection (V.starProjection (m : H)) := fun m => by
    simp [genericCosineBlock, DavisKahanExt.compressOperator]
  calc ((genericLeftHalf U V).subtypeL ∘L genericCosineBlock U V ∘L
          (genericLeftHalf U V).orthogonalProjectionOnto) x
      = (genericLeftHalf U V).starProjection
          (V.starProjection ((genericLeftHalf U V).starProjection x)) :=
        hcoe ((genericLeftHalf U V).orthogonalProjectionOnto x)
    _ = U.starProjection (V.starProjection (U.starProjection x)) := by
        rw [hproj, hproj]
    _ = (U.starProjection ∘L V.starProjection ∘L U.starProjection) x := rfl

/-- **The bridge between Corollary 3.1's two cosine blocks.**

The generic cosine block and the ambient block `P_U P_V P_U` have the same
approximation-number sequence — hence the same `compactAngleEigenvalueList` — whenever the
four elementary Halmos summands are trivial.

Mathematically this is "extension by zero preserves approximation numbers": off the generic
part the ambient block vanishes, so the two operators carry the same nonzero singular data.
The general fact is
`TauCeti.ApproximationNumber.approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto`;
nothing about angles is reproved here. -/
theorem approximationNumber_genericCosineBlock_eq_ambient
    (h : halmosTrivialPart U V = ⊥) (n : ℕ) :
    (genericCosineBlock U V).approximationNumber n =
      (U.starProjection ∘L V.starProjection ∘L U.starProjection).approximationNumber n := by
  rw [← subtypeL_comp_genericCosineBlock_comp_orthogonalProjectionOnto U V h,
    TauCeti.ApproximationNumber.approximationNumber_subtypeL_comp_comp_orthogonalProjectionOnto
      (genericLeftHalf U V) (genericCosineBlock U V) n]

/-- The `compactAngleEigenvalueList` form of
`approximationNumber_genericCosineBlock_eq_ambient`. -/
theorem compactAngleEigenvalueList_genericCosineBlock_eq_ambient
    (h : halmosTrivialPart U V = ⊥) :
    compactAngleEigenvalueList (genericCosineBlock U V) =
      compactAngleEigenvalueList
        (U.starProjection ∘L V.starProjection ∘L U.starProjection) :=
  funext fun n => approximationNumber_genericCosineBlock_eq_ambient U V h n

end GenericAmbientBridge

section Classification

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℂ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-! Instantiating the field-generic Halmos classification at `𝕜 = ℂ` asks typeclass
inference for `ContinuousFunctionalCalculus ℝ (M →L[ℂ] M) IsSelfAdjoint` with `M` the
`U`-half of the generic part.  Mathlib supplies it through the C⋆-algebra structure on
bounded operators, but reaching it from a subspace coercion needs one more level of
pending synthesis than the default allows; the instance is found at depth `3`. -/
set_option maxSynthPendingDepth 3

/-! **Davis--Kahan 1970, Theorem 3.1 in the paper's multiplicity phrasing** is
`TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification`, in
`DavisKahan/Sources/DavisKahan1970/Section3Classification.lean`, together with its real
analogue.  It is a wrapper over `twoProjection_operator_classification` below and the
promoted spectral-multiplicity classification
`TauCeti.sameSpectralMultiplicity_iff_operatorUnitaryEquiv`; it lives with the other
source-facing Section 3 statements rather than here. -/

/-- **Davis--Kahan 1970, Corollary 3.1 with the printed hypothesis, over a complex Hilbert
space.**

The `𝕜 = ℂ` instance of `corollary3_1_compact_defectBlock_angleList_classification`,
grounded on it by `:=`, with no added hypothesis.

It is recorded separately because the generic form *carries* the reconstruction functional
calculus on `↥(genericLeftHalf U Vᗮ)` as a hypothesis, and typeclass inference finds that
instance for an arbitrary pair but not at every concrete one.  A consumer that instantiates
the corollary at a specific pair therefore goes through this form, where the instance was
already discharged. -/
theorem corollary3_1_compact_defectBlock_angleList_classification_complex
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L
        (ContinuousLinearMap.id ℂ H₁ - projection V₁) ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L
        (ContinuousLinearMap.id ℂ H₂ - projection V₂) ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (genericCosineBlock U₁ V₁ᗮ) =
        compactAngleEigenvalueList
          (genericCosineBlock U₂ V₂ᗮ) :=
  corollary3_1_compact_defectBlock_angleList_classification U₁ V₁ U₂ V₂ hcompact₁ hcompact₂


end Classification

/-! ## Theorem 3.1, the realization half -/

section Realization


variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Davis--Kahan 1970, Theorem 3.1, the realization half — the paper's sentence
(ii).**

The classification half (`twoProjection_operator_classification`, and
`TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification` in the paper's
multiplicity phrasing) says that the angle datum determines the pair.  This says the converse of the *existence* kind: every
admissible angle datum is *attained*.  Given `cos Θ₀, sin Θ₀` on `E`,
`cos Θ₁, sin Θ₁` on `F` and the intertwiner `J₀` that matches their spectral
multiplicities away from the angle `0`, the two subspaces

`U = E`-factor,  `V = W₀ E` with `W₀ x = (cos Θ₀ x, J₀ sin Θ₀ x)`

of `E ⊕₂ F` satisfy, in order:

1. the compression of `P_V` to `U` is `cos² Θ₀`;
2. the compression of `P_Vᗮ` to `Uᗮ` is `cos² Θ₁`;
3. `U ⊓ V` is the angle-`0` eigenspace on the `P`-side;
4. `Uᗮ ⊓ Vᗮ` is the angle-`0` eigenspace on the `Pᗮ`-side;
5. `U ⊓ Vᗮ` is the angle-`π/2` eigenspace on the `P`-side;
6. `Uᗮ ⊓ V` is the angle-`π/2` eigenspace on the `Pᗮ`-side;
7. the two crossed defects are isometric.

Items 3--7 are the mathematical content of the theorem's hypothesis: the
`π/2` multiplicities are *forced* to agree, because `J₀` restricts to a linear
isometric equivalence between them, while the `0` multiplicities are the two
kernels of `sin Θ₀` and `sin Θ₁`, which `J₀` never sees.  That the latter are
genuinely unconstrained is witnessed by
`theorem3_1_realization_zeroAngle_unconstrained`.

Grounded by `:=` on `Geometry/Halmos/Realization.lean`, so there is a single
source of truth.  The block matrix behind item 1 and item 2 is
`starProjection_targetSubspace_apply`, which reproduces equation (3.7) of the
source, both off-diagonal entries positive. -/
theorem theorem3_1_realization (d : HalmosAngleDatum 𝕜 E F) :
    (∀ x : E, (sourceSubspace 𝕜 E F).starProjection
        (d.targetSubspace.starProjection (modelInl 𝕜 E F x)) =
          modelInl 𝕜 E F (d.cos₀ (d.cos₀ x))) ∧
      (∀ y : F, (sourceSubspace 𝕜 E F)ᗮ.starProjection
        ((d.targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y)) =
          modelInr 𝕜 E F (d.cos₁ (d.cos₁ y))) ∧
      halmosCommonPart (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.sin₀ : E →ₗ[𝕜] E)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.sin₁ : F →ₗ[𝕜] F)) ∧
      halmosSourceDefect (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.cos₀ : E →ₗ[𝕜] E)) ∧
      halmosTargetDefect (sourceSubspace 𝕜 E F) d.targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker (d.cos₁ : F →ₗ[𝕜] F)) ∧
      Nonempty (↥(halmosSourceDefect (sourceSubspace 𝕜 E F) d.targetSubspace) ≃ₗᵢ[𝕜]
        ↥(halmosTargetDefect (sourceSubspace 𝕜 E F) d.targetSubspace)) :=
  ⟨d.compress_source_eq, d.compress_sourceOrthogonal_eq, d.halmosCommonPart_eq,
    d.halmosExteriorPart_eq, d.halmosSourceDefect_eq, d.halmosTargetDefect_eq,
    d.nonempty_halmosSourceDefect_equiv_targetDefect⟩

section OfAngles

variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
  [ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]
  [Algebra ℝ (F →L[𝕜] F)] [IsScalarTower ℝ 𝕜 (F →L[𝕜] F)]
  [ContinuousFunctionalCalculus ℝ (F →L[𝕜] F) IsSelfAdjoint]

/-- **Davis--Kahan 1970, Theorem 3.1, sentence (ii), in the printed shape: stated
from the angle operators rather than from a packaged datum.**

`theorem3_1_realization` consumes a `HalmosAngleDatum`, which carries
`cos Θ₀, sin Θ₀, cos Θ₁, sin Θ₁` and the intertwiner as five independent fields.
The paper does not.  It says "given such `Θⱼ` acting on spaces `Hⱼ`", where
"such" refers to the theorem's own sentence "these are arbitrary Hermitian
operators satisfying the following conditions: `0 ≤ Θⱼ ≤ π/2`; ... and the
spectral multiplicity functions of the `Θⱼ` are the same except for a possible
difference in the multiplicity of `{0}`", and then extracts from that last
condition "some isometry `J₀` of `closure (ran Θ₀)` onto `closure (ran Θ₁)` such
that `J₀ Θ₀ J₀⁻¹` agrees on its domain with `Θ₁`".  So the printed data are two
Hermitian operators and one intertwining partial isometry — and that is this
statement's hypothesis list.  The datum is built inside the proof by
`HalmosAngleDatum.ofIntertwinedAngles`, and each
`cos Θⱼ`, `sin Θⱼ` in the conclusion is the continuous functional calculus of
`Θⱼ` rather than an opaque field, so the seven conjuncts of
`theorem3_1_realization` are read here directly off `Θ₀`, `Θ₁` and `J`.

**The two partial-isometry hypotheses are the paper's, not an artifact.**
`hisom` and `hcoisom` say that `J` is isometric on `ran sin Θ₀` and co-isometric
onto `ran sin Θ₁`; that is the content of the printed `J₀`, and it is a
multiplicity statement, invisible to a functional calculus of one operator at a
time.  Everything else the datum needs is derived.

**On the spectral confinement.**  `_hspec₀` and `_hspec₁` are the printed
`0 ≤ Θⱼ ≤ π/2`.  They are taken as hypotheses here and are deliberately unused in
the proof, hence the underscores.  They belong here rather than on the
constructor: `HalmosAngleDatum` records no nonnegativity, and none of the ten
fields `ofIntertwinedAngles` derives needs one — `cos² + sin² = 1` and
`J f(Θ₀) = f(Θ₁) J` hold over all of `ℝ` — so assuming confinement there would
narrow the constructor for nothing.  What confinement buys is that the statement
*reads* as the printed sentence: on `[0, π/2]` one has `sin t = 0 ↔ t = 0` and
`cos t = 0 ↔ t = π/2`, so conjuncts 3--4 exhibit the two angle-`0` spaces and
conjuncts 5--6 the two angle-`π/2` spaces, which is what Davis and Kahan mean by
calling the `Θⱼ` angle operators.  Dropping the two hypotheses would leave the
same theorem with the same proof and a weaker reading; keeping them costs
nothing, so they are kept.

`RCLike`-generic.  The real case is therefore an instantiation and not a second
theorem: `theorem3_1_realization_ofAngles_real`. -/
theorem theorem3_1_realization_ofAngles
    {Θ₀ : E →L[𝕜] E} {Θ₁ : F →L[𝕜] F}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (_hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (_hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (J : E →L[𝕜] F) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
    (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
    (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁) :
    (∀ x : E, (sourceSubspace 𝕜 E F).starProjection
        ((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace.starProjection (modelInl 𝕜 E F x)) =
          modelInl 𝕜 E F (cfc Real.cos Θ₀ (cfc Real.cos Θ₀ x))) ∧
      (∀ y : F, (sourceSubspace 𝕜 E F)ᗮ.starProjection
        (((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y)) =
          modelInr 𝕜 E F (cfc Real.cos Θ₁ (cfc Real.cos Θ₁ y))) ∧
      halmosCommonPart (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.sin Θ₀ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.sin Θ₁ : F →L[𝕜] F) : F →ₗ[𝕜] F)) ∧
      halmosSourceDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.cos Θ₀ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ∧
      halmosTargetDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.cos Θ₁ : F →L[𝕜] F) : F →ₗ[𝕜] F)) ∧
      Nonempty (↥(halmosSourceDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace) ≃ₗᵢ[𝕜]
        ↥(halmosTargetDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace)) :=
  theorem3_1_realization (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom)

end OfAngles

/-- **The multiplicity at angle `0` is genuinely unconstrained.**

The all-`0` datum over an arbitrary pair `(E, F)` of Hilbert spaces
realizes `U = V`, whose angle-`0` spaces are the whole of `E` on the `P`-side and
the whole of `F` on the `Pᗮ`-side.  `E` and `F` are unrelated, so no admissibility
condition at angle `0` can be imposed — in contrast to the angle `π/2`, where
item 7 of `theorem3_1_realization` forces the two multiplicities to agree.
Together the two statements are why Davis and Kahan's hypothesis is asymmetric
between `0` and `π/2`. -/
theorem theorem3_1_realization_zeroAngle_unconstrained
    (𝕜 : Type*) [RCLike 𝕜]
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (F : Type v) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] :
    halmosCommonPart (sourceSubspace 𝕜 E F) (trivialHalmosAngleDatum 𝕜 E F).targetSubspace =
        sourceSubspace 𝕜 E F ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F)
          (trivialHalmosAngleDatum 𝕜 E F).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F)) ⊤ :=
  ⟨trivial_halmosCommonPart_eq 𝕜 E F, trivial_halmosExteriorPart_eq 𝕜 E F⟩

/-- **Davis--Kahan 1970, Corollary 3.1, the realization sentence.**

The classification half says that the compactness hypothesis plus the angle
eigenvalue list determines the pair.  This is the sentence that says the list is
otherwise *arbitrary*: given any

`π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0`,

the pair

`U = ` the `E`-factor of `ℓ²(ℕ, 𝕜) ⊕₂ ℓ²(ℕ, 𝕜)`,  `V = (angleSequenceDatum 𝕜 θ).targetSubspace`

realizes it.  The witness is exhibited rather than asserted to exist: `V` is the
image of `U` under the direct rotation built from the diagonal operators
`cos Θ = diag (cos θₙ)` and `sin Θ = diag (sin θₙ)`, so the whole construction is
`theorem3_1_realization` applied to a datum, not a new geometric argument.

The four conclusions are, in order:

1. **the printed compactness hypothesis holds** — what is proved compact is the
   *defect* block `P (1 - Q) P`, which is `sin² Θ` on the `E`-factor, and
   `θₙ → 0` makes its coefficients vanish.  Corollary 3.1 as printed assumes
   exactly this block, and the census records that it is incomparable with
   `P Q P` in infinite dimension, so the choice is stated rather than left
   implicit.  (`P Q P` is `cos² Θ` here, with coefficients tending to `1`; that
   this makes it non-compact is not asserted as proved.);
2. **the angle list is the prescribed one**: the classifying list of the defect
   block, in the sense of `compactAngleEigenvalueList`, is `n ↦ sin² θₙ`.  The
   map `θ ↦ sin² θ` is strictly monotone on `[0, π/2]`, so this carries exactly
   the information of the printed decreasing sequence `θ`;
3. and 4. **the angle-`0` multiplicities**, on the two sides, are the kernels of
   `sin Θ` — here equal, because the datum puts the same diagonal on both sides.

This witness realizes the two sides' angle-`0` multiplicities *equal*, and
realizes only the multiplicities the sequence `θ` itself produces.  An arbitrary
and independently prescribed pair of angle-`0` multiplicities is
`corollary3_1_realization_zeroMultiplicity`, which adds
`trivialHalmosAngleDatum` on two further spaces by `HalmosAngleDatum.prod`. -/
theorem corollary3_1_realization (𝕜 : Type*) [RCLike 𝕜] (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0)) :
    IsCompactOperator
        ((sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection ∘L
          (ContinuousLinearMap.id 𝕜 (AngleSequenceAmbient 𝕜) -
            (angleSequenceDatum 𝕜 θ).targetSubspace.starProjection) ∘L
          (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection) ∧
      compactAngleEigenvalueList
          ((sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection ∘L
            (ContinuousLinearMap.id 𝕜 (AngleSequenceAmbient 𝕜) -
              (angleSequenceDatum 𝕜 θ).targetSubspace.starProjection) ∘L
            (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜)).starProjection) =
        (fun n => Real.sin (θ n) ^ 2) ∧
      halmosCommonPart (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
          (angleSequenceDatum 𝕜 θ).targetSubspace =
        Submodule.map
          (modelInl 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜) :
            AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceAmbient 𝕜)
          (LinearMap.ker (angleSinOp 𝕜 θ : AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
          (angleSequenceDatum 𝕜 θ).targetSubspace =
        Submodule.map
          (modelInr 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜) :
            AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceAmbient 𝕜)
          (LinearMap.ker (angleSinOp 𝕜 θ : AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜)) :=
  ⟨isCompactOperator_angleSequenceDefectBlock hlim,
    funext fun n => approximationNumber_angleSequenceDefectBlock hθ0 hθ2 hanti n,
    (angleSequenceDatum 𝕜 θ).halmosCommonPart_eq,
    (angleSequenceDatum 𝕜 θ).halmosExteriorPart_eq⟩

/-- **Davis--Kahan 1970, Corollary 3.1, the realization sentence with prescribed
angle-`0` multiplicities.**

The paper's sentence is: the eigenvalues of `Θ₀` are an arbitrary sequence
`π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0` *together with a possible eigenvalue `0`*, and those of
`Θ₁` are the same except perhaps for the multiplicity of `0`.  Here `Z₀` and `Z₁`
are that eigenvalue's two multiplicities: arbitrary Hilbert spaces, chosen
independently of each other and of `θ`.

The pair is again exhibited rather than asserted to exist.  It is
`theorem3_1_realization` applied to
`(angleSequenceDatum 𝕜 θ).prod (trivialHalmosAngleDatum 𝕜 Z₀ Z₁)`: the sequence
on one summand and the all-`0` datum on the other.  The four conclusions are the
printed compactness hypothesis on the *defect* block `P (1 - Q) P` (not on
`P Q P` — see `corollary3_1_realization`), the prescribed angle list, and the two
angle-`0` eigenspaces, which come out as the prescribed `Z₀` and `Z₁`.

`hne` — no prescribed angle is itself `0` — is used only by the last two
conclusions, and is the paper's own reading: the angle `0` is carried by `Z₀` and
`Z₁`, separately from the sequence.  The first two conclusions hold without it. -/
theorem corollary3_1_realization_zeroMultiplicity (𝕜 : Type*) [RCLike 𝕜] (θ : ℕ → ℝ)
    (Z₀ : Type*) [NormedAddCommGroup Z₀] [InnerProductSpace 𝕜 Z₀] [CompleteSpace Z₀]
    (Z₁ : Type*) [NormedAddCommGroup Z₁] [InnerProductSpace 𝕜 Z₁] [CompleteSpace Z₁]
    (hθ0 : ∀ n, 0 ≤ θ n) (hθ2 : ∀ n, θ n ≤ Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0)) (hne : ∀ n, θ n ≠ 0) :
    IsCompactOperator
        ((sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection ∘L
          (ContinuousLinearMap.id 𝕜
              (WithLp 2 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) ×
                WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))) -
            (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace.starProjection) ∘L
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection) ∧
      compactAngleEigenvalueList
          ((sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
                (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection ∘L
            (ContinuousLinearMap.id 𝕜
                (WithLp 2 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) ×
                  WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))) -
              (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace.starProjection) ∘L
            (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
                (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁))).starProjection) =
        (fun n => Real.sin (θ n) ^ 2) ∧
      halmosCommonPart
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)))
          (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace =
        Submodule.map
          (modelInl 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) :
            WithLp 2 (AngleSequenceSpace 𝕜 × Z₀) →ₗ[𝕜] _)
          (Submodule.map
            (modelInr 𝕜 (AngleSequenceSpace 𝕜) Z₀ :
              Z₀ →ₗ[𝕜] WithLp 2 (AngleSequenceSpace 𝕜 × Z₀)) ⊤) ∧
      halmosExteriorPart
          (sourceSubspace 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
            (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)))
          (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).targetSubspace =
        Submodule.map
          (modelInr 𝕜 (WithLp 2 (AngleSequenceSpace 𝕜 × Z₀))
              (WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) :
            WithLp 2 (AngleSequenceSpace 𝕜 × Z₁) →ₗ[𝕜] _)
          (Submodule.map
            (modelInr 𝕜 (AngleSequenceSpace 𝕜) Z₁ :
              Z₁ →ₗ[𝕜] WithLp 2 (AngleSequenceSpace 𝕜 × Z₁)) ⊤) := by
  refine ⟨isCompactOperator_angleSequenceZeroDefectBlock 𝕜 θ Z₀ Z₁ hlim,
    funext fun n =>
      approximationNumber_angleSequenceZeroDefectBlock 𝕜 θ Z₀ Z₁ hθ0 hθ2 hanti n,
    ?_, ?_⟩
  · refine (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).halmosCommonPart_eq.trans ?_
    rw [angleSequenceZeroDatum_sin₀, ker_blockMap_angleSinOp 𝕜 θ hθ0 hθ2 hne Z₀]
  · refine (angleSequenceZeroDatum 𝕜 θ Z₀ Z₁).halmosExteriorPart_eq.trans ?_
    rw [angleSequenceZeroDatum_sin₁, ker_blockMap_angleSinOp 𝕜 θ hθ0 hθ2 hne Z₁]

end Realization

/-! ## Corollary 3.1: realization composed with classification

The realization sentence computes the angle list of the *ambient* defect block
`P (1 - Q) P`, while the classification sentence's invariant is the eigenvalue list of the
*generic* cosine block of the pair `(U, Vᗮ)`.  The realized pair puts no mass on any of the
four elementary Halmos summands once no prescribed angle is `0` or `π/2`, so
`approximationNumber_genericCosineBlock_eq_ambient` identifies the two lists and the two
halves compose.

**Which compact object.**  Both halves here are on the *defect* block `P (1 - Q) P`, as
printed.  Nothing below compares `P (1 - Q) P` with `P Q P`; the census's record that the
two compactness hypotheses are incomparable in infinite dimension is untouched.

**Recorded narrowing.**  The printed sentence allows `π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0`, that is,
angles equal to `π/2` and a possible eigenvalue `0`.  The statements below assume
`0 < θₙ < π/2` strictly.  This is a *narrowing* of the source hypothesis, and it is the
exact hypothesis that makes the four elementary summands vanish, so that the generic
invariant and the ambient list coincide.  The angle-`0` multiplicities are realized
separately and unconstrained by `corollary3_1_realization_zeroMultiplicity`, and the angle
`π/2` is the elementary summand `U ⊓ Vᗮ`, so neither is lost from the paper's picture —
they are carried by `SameHalmosTrivialDimensions` rather than by the list. -/

section RealizationClassification


/-- **The realized pair's generic invariant is the prescribed angle list.**

The classifying invariant of Corollary 3.1's defect-block form, evaluated on the pair
realized by `angleSequenceDatum`, is `n ↦ sin² θₙ`.  Grounded by `:=` on the realization
sentence's approximation-number computation and on
`approximationNumber_genericCosineBlock_eq_ambient`; no angle mathematics is redone. -/
theorem compactAngleEigenvalueList_genericCosineBlock_angleSequenceDatum
    (𝕜 : Type*) [RCLike 𝕜] (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 < θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) (hanti : Antitone θ) :
    compactAngleEigenvalueList
        (genericCosineBlock
          (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
          ((angleSequenceDatum 𝕜 θ).targetSubspace)ᗮ) =
      fun n => Real.sin (θ n) ^ 2 := by
  have hθ0' : ∀ n, 0 ≤ θ n := fun n => (hθ0 n).le
  have hθ2' : ∀ n, θ n ≤ Real.pi / 2 := fun n => (hθ2 n).le
  have hne : ∀ n, θ n ≠ 0 := fun n => (hθ0 n).ne'
  have hsin : LinearMap.ker
      ((angleSinOp 𝕜 θ : AngleSequenceSpace 𝕜 →L[𝕜] AngleSequenceSpace 𝕜) :
        AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜) = ⊥ :=
    ker_angleSinOp_eq_bot 𝕜 θ hθ0' hθ2' hne
  have hcos : LinearMap.ker
      ((angleCosOp 𝕜 θ : AngleSequenceSpace 𝕜 →L[𝕜] AngleSequenceSpace 𝕜) :
        AngleSequenceSpace 𝕜 →ₗ[𝕜] AngleSequenceSpace 𝕜) = ⊥ :=
    ker_angleCosOp_eq_bot 𝕜 θ hθ0' hθ2
  -- The four elementary Halmos summands of the realized pair are trivial.
  have hcommon : halmosCommonPart
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosCommonPart
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosCommonPart_eq,
      angleSequenceDatum_sin₀, hsin, Submodule.map_bot]
  have hsource : halmosSourceDefect
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosSourceDefect
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosSourceDefect_eq,
      angleSequenceDatum_cos₀, hcos, Submodule.map_bot]
  have htarget : halmosTargetDefect
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosTargetDefect
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosTargetDefect_eq,
      angleSequenceDatum_cos₁, hcos, Submodule.map_bot]
  have hexterior : halmosExteriorPart
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      (angleSequenceDatum 𝕜 θ).targetSubspace = ⊥ := by
    rw [show halmosExteriorPart
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace = _ from
      (angleSequenceDatum 𝕜 θ).halmosExteriorPart_eq,
      angleSequenceDatum_sin₁, hsin, Submodule.map_bot]
  have htriv : halmosTrivialPart
      (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
      ((angleSequenceDatum 𝕜 θ).targetSubspace)ᗮ = ⊥ := by
    rw [halmosTrivialPart_orthogonal_right, show halmosTrivialPart
        (sourceSubspace 𝕜 (AngleSequenceSpace 𝕜) (AngleSequenceSpace 𝕜))
        (angleSequenceDatum 𝕜 θ).targetSubspace =
      (halmosCommonPart _ _ ⊔ halmosSourceDefect _ _) ⊔
        (halmosTargetDefect _ _ ⊔ halmosExteriorPart _ _) from rfl,
      hcommon, hsource, htarget, hexterior, bot_sup_eq, bot_sup_eq]
  -- The bridge, then the realization's own computation of the ambient list.
  rw [compactAngleEigenvalueList_genericCosineBlock_eq_ambient _ _ htriv,
    Submodule.starProjection_orthogonal (angleSequenceDatum 𝕜 θ).targetSubspace]
  exact funext fun n =>
    approximationNumber_angleSequenceDefectBlock hθ0' hθ2' hanti n

/-- **Davis--Kahan 1970, Corollary 3.1: the realization sentence composed with the
classification sentence.**

Given a prescribed angle sequence `π/2 > θ₁ ≥ θ₂ ≥ ⋯ → 0` with every `θₙ` strictly between
`0` and `π/2`, an arbitrary pair `(U₂, V₂)` with the printed compact defect block is
unitarily equivalent to the realized pair exactly when its four elementary Halmos
multiplicities are trivial and its angle list is `n ↦ sin² θₙ`.

This is the statement the two halves of Corollary 3.1 were built to meet.  Both hypotheses
and both conclusions are on the *defect* block `P (1 - Q) P`, as printed.  The strict
inequalities `0 < θₙ < π/2` are a recorded narrowing of the printed sequence bound; see the
section note above. -/
theorem corollary3_1_prescribedAngleSequence_classification (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 < θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0))
    {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection]
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L
        (ContinuousLinearMap.id ℂ H₂ - V₂.starProjection) ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent
        (sourceSubspace ℂ (AngleSequenceSpace ℂ) (AngleSequenceSpace ℂ))
        (angleSequenceDatum ℂ θ).targetSubspace U₂ V₂ ↔
      SameHalmosTrivialDimensions
        (sourceSubspace ℂ (AngleSequenceSpace ℂ) (AngleSequenceSpace ℂ))
        (angleSequenceDatum ℂ θ).targetSubspace U₂ V₂ ∧
      compactAngleEigenvalueList (genericCosineBlock U₂ V₂ᗮ) =
        fun n => Real.sin (θ n) ^ 2 := by
  rw [corollary3_1_compact_defectBlock_angleList_classification_complex _ _ U₂ V₂
      (isCompactOperator_angleSequenceDefectBlock hlim) hcompact₂,
    compactAngleEigenvalueList_genericCosineBlock_angleSequenceDatum ℂ θ hθ0 hθ2 hanti]
  exact and_congr_right fun _ => eq_comm

end RealizationClassification

/-! ## Section 3 over a real Hilbert space

The statements above are field-generic, so the real forms are instantiations
rather than new theorems.  They are recorded by name because the census tracks
the paper's results at the paper's scope, and because they are the machine
check that the `𝕜 = ℝ` instantiation really is inhabited: each one forces
typeclass inference to find
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`.

Davis and Kahan work on a Hilbert space over `ℝ` or `ℂ` throughout, so the real
scope is the source scope, not an extension of it. -/

section RealScalars

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
  [CompleteSpace H₂]
variable (U₁ V₁ : Submodule ℝ H₁) [U₁.HasOrthogonalProjection]
  [V₁.HasOrthogonalProjection]
variable (U₂ V₂ : Submodule ℝ H₂) [U₂.HasOrthogonalProjection]
  [V₂.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, Theorem 3.1, the operator-level classification, over a
real Hilbert space.**

The `𝕜 = ℝ` instance of `twoProjection_operator_classification`.  No
compactness, no finite dimension, no separability. -/
theorem twoProjection_operator_classification_real :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosOperatorInvariant U₁ V₁ U₂ V₂ :=
  twoProjection_operator_classification U₁ V₁ U₂ V₂

/-! ### Theorem 3.1, sentence (ii), over a real Hilbert space

`theorem3_1_realization_ofAngles` is `RCLike`-generic, so its real form is an
instantiation and not a theorem.  It is recorded as an `example` rather than by
name deliberately: it adds no declaration, and it fails loudly if the `𝕜 = ℝ`
hypothesis block ever stops being inhabited.  That block is the only thing that
could have made the real case cost something — the wrapper needs
`ContinuousFunctionalCalculus ℝ (Hⱼ →L[ℝ] Hⱼ) IsSelfAdjoint` on *both* spaces to
form `cos Θⱼ` and `sin Θⱼ`, and instance search supplies it from
`ContinuousLinearMap.instContinuousFunctionalCalculusRealIsSelfAdjoint`, in
unrestricted dimension.  Two of the seven conjuncts are read off below: the
angle-`π/2` space on the `P`-side, and the isometry between the two crossed
defects that forces the two `π/2` multiplicities to agree. -/

example {Θ₀ : H₁ →L[ℝ] H₁} {Θ₁ : H₂ →L[ℝ] H₂}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (J : H₁ →L[ℝ] H₂) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
    (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
    (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁) :
    halmosSourceDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
      Submodule.map (modelInl ℝ H₁ H₂ : H₁ →ₗ[ℝ] WithLp 2 (H₁ × H₂))
        (LinearMap.ker ((cfc Real.cos Θ₀ : H₁ →L[ℝ] H₁) : H₁ →ₗ[ℝ] H₁)) ∧
    Nonempty (↥(halmosSourceDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
          hcoisom).targetSubspace) ≃ₗᵢ[ℝ]
      ↥(halmosTargetDefect (sourceSubspace ℝ H₁ H₂)
        (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
          hcoisom).targetSubspace)) :=
  ⟨(theorem3_1_realization_ofAngles hΘ₀ hΘ₁ hspec₀ hspec₁ J hJ hisom hcoisom).2.2.2.2.1,
    (theorem3_1_realization_ofAngles hΘ₀ hΘ₁ hspec₀ hspec₁ J hJ hisom hcoisom).2.2.2.2.2.2⟩

/-- **Davis--Kahan 1970, Corollary 3.1, over a real Hilbert space.**

The `𝕜 = ℝ` instance of
`pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData`:
with `P_U P_V P_U` compact on both sides, the four elementary Halmos
multiplicities together with the multiplicity of every angle are a complete
invariant. -/
theorem corollary3_1_compact_classification_real
    (hc₁ : IsCompactOperator (projection U₁ ∘L projection V₁ ∘L projection U₁))
    (hc₂ : IsCompactOperator (projection U₂ ∘L projection V₂ ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameCompactAngleData U₁ V₁ U₂ V₂ :=
  pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData
    U₁ V₁ U₂ V₂ hc₁ hc₂

/-- **Davis--Kahan 1970, Corollary 3.1 in the paper's decreasing eigenvalue-list
phrasing, over a real Hilbert space.**

The `𝕜 = ℝ` instance of `corollary3_1_compact_angleList_classification`.

**The angle list stays `ℝ`-valued.**  `compactAngleEigenvalueList` has codomain
`ℕ → ℝ` over every scalar field, because the eigenvalues of a compact positive
self-adjoint operator are real; passing to real scalars changes only how such an
eigenvalue is embedded back into the field, never what the list records.

**The compactness hypothesis is the generic theorem's.**  It is
`P_U P_V P_U` compact, not the printed defect block `P (I - Q) P`.  Those two are
incomparable in infinite dimension; that is a pre-existing question recorded on
this source row, and the real form inherits it unchanged.  The printed
hypothesis is carried by
`corollary3_1_compact_defectBlock_angleList_classification`, which is the same
theorem applied to `(U, Vᗮ)`. -/
theorem corollary3_1_compact_angleList_classification_real
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L projection V₁ ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L projection V₂ ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (genericCosineBlock U₁ V₁) =
        compactAngleEigenvalueList
          (genericCosineBlock U₂ V₂) :=
  corollary3_1_compact_angleList_classification U₁ V₁ U₂ V₂ hcompact₁ hcompact₂

/-- **Davis--Kahan 1970, Corollary 3.1 with the printed hypothesis, over a real Hilbert
space.**

The `𝕜 = ℝ` instance of `corollary3_1_compact_defectBlock_angleList_classification`,
grounded on it by `:=`, with no added hypothesis: the compactness is of the *defect* block
`P (I - Q) P`, as printed, and the classifying list is the eigenvalue list of the
corresponding sine-square angle operator.

The reconstruction functional calculus that the generic form carries is synthesized here at
`ℝ`, not assumed.  As over `ℂ`, the `PQP` versus `P (I - Q) P` question recorded on this
source row is untouched: this is the printed object on both sides. -/
theorem corollary3_1_compact_defectBlock_angleList_classification_real
    (hcompact₁ : IsCompactOperator
      (projection U₁ ∘L
        (ContinuousLinearMap.id ℝ H₁ - projection V₁) ∘L projection U₁))
    (hcompact₂ : IsCompactOperator
      (projection U₂ ∘L
        (ContinuousLinearMap.id ℝ H₂ - projection V₂) ∘L projection U₂)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      compactAngleEigenvalueList
          (genericCosineBlock U₁ V₁ᗮ) =
        compactAngleEigenvalueList
          (genericCosineBlock U₂ V₂ᗮ) :=
  corollary3_1_compact_defectBlock_angleList_classification U₁ V₁ U₂ V₂ hcompact₁ hcompact₂

/-- **Davis--Kahan 1970, Corollary 3.1: the realization sentence composed with the
classification sentence, over a real Hilbert space.**

The `𝕜 = ℝ` instance of `corollary3_1_prescribedAngleSequence_classification`, assembled
from the same two halves: the realization `corollary3_1_realization` is already
`RCLike`-generic, and the classification half is now
`corollary3_1_compact_defectBlock_angleList_classification_real`.

Both hypotheses and both conclusions are on the *defect* block `P (1 - Q) P`, as printed.
The strict inequalities `0 < θₙ < π/2` are the same **recorded narrowing** of the printed
sequence bound `π/2 ≥ θ₁ ≥ θ₂ ≥ ⋯ → 0` that the complex form carries, and for the same
reason: strictness is exactly what makes the four elementary Halmos summands vanish, so
that the generic invariant and the ambient list coincide.  The angle-`0` and angle-`π/2`
data are not lost — they are the elementary summands, carried by
`SameHalmosTrivialDimensions`. -/
theorem corollary3_1_prescribedAngleSequence_classification_real (θ : ℕ → ℝ)
    (hθ0 : ∀ n, 0 < θ n) (hθ2 : ∀ n, θ n < Real.pi / 2) (hanti : Antitone θ)
    (hlim : Filter.Tendsto θ Filter.atTop (nhds 0))
    (hcompact₂ : IsCompactOperator
      (U₂.starProjection ∘L
        (ContinuousLinearMap.id ℝ H₂ - V₂.starProjection) ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent
        (sourceSubspace ℝ (AngleSequenceSpace ℝ) (AngleSequenceSpace ℝ))
        (angleSequenceDatum ℝ θ).targetSubspace U₂ V₂ ↔
      SameHalmosTrivialDimensions
        (sourceSubspace ℝ (AngleSequenceSpace ℝ) (AngleSequenceSpace ℝ))
        (angleSequenceDatum ℝ θ).targetSubspace U₂ V₂ ∧
      compactAngleEigenvalueList (genericCosineBlock U₂ V₂ᗮ) =
        fun n => Real.sin (θ n) ^ 2 := by
  rw [corollary3_1_compact_defectBlock_angleList_classification_real _ _ U₂ V₂
      (isCompactOperator_angleSequenceDefectBlock hlim) hcompact₂,
    compactAngleEigenvalueList_genericCosineBlock_angleSequenceDatum ℝ θ hθ0 hθ2 hanti]
  exact and_congr_right fun _ => eq_comm

/-! ### Proposition 3.2 over a real Hilbert space

The three statements below are the `𝕜 = ℝ` instances of the generic
`section NonacuteExistence` theorems, each grounded by `:=` on the generic
theorem and each carrying exactly the generic theorem's hypotheses.  In
particular the real forms assume no finite dimension, no separability and no
compactness, and they do **not** add a nondegeneracy hypothesis on the crossed
defects: `¬ TauCeti.IsAcute U₁ V₁` already forces one of them to be nonzero,
by `TauCeti.isAcute_iff_inf_orthogonal_eq_bot`.

They are *not* obtained by descending the complex theorem.  That route is
refuted -- transporting the forward direction produces an isometry of the
complexified defect spaces, and nothing recovers a real one from it -- so the
whole polar and direct-rotation stack under `DavisKahan/Geometry/Polar/` was
made `RCLike`-generic instead, which is what these instances read off. -/

/-- **Davis--Kahan 1970, Proposition 3.2, over a real Hilbert space.**

The `𝕜 = ℝ` instance of `proposition3_2_exists_iff_crossedDefectsEquivalent`: a
direct rotation of the pair exists exactly when the two crossed intersections
admit a linear isometric equivalence, which is the cardinal-free form of the
paper's equal-dimension condition (3.5). -/
theorem proposition3_2_exists_iff_crossedDefectsEquivalent_real :
    (∃ T : H₁ →L[ℝ] H₁, IsPaperDirectRotation U₁ V₁ T) ↔
      CrossedDefectsEquivalent U₁ V₁ :=
  proposition3_2_exists_iff_crossedDefectsEquivalent U₁ V₁

/-- **Davis--Kahan 1970, Proposition 3.2, the injective parameterization, over a
real Hilbert space.**

The `𝕜 = ℝ` instance of `proposition3_2_parameterized_nonuniqueness`. -/
theorem proposition3_2_parameterized_nonuniqueness_real
    (hdefect : CrossedDefectsEquivalent U₁ V₁) :
    ∃ build :
        (halmosSourceDefect U₁ V₁ ≃ₗᵢ[ℝ] halmosTargetDefect U₁ V₁) →
          (H₁ →L[ℝ] H₁),
      (∀ J, IsPaperDirectRotation U₁ V₁ (build J)) ∧
      Function.Injective build :=
  proposition3_2_parameterized_nonuniqueness U₁ V₁ hdefect

/-- **Davis--Kahan 1970, Proposition 3.2, second printed sentence, over a real
Hilbert space: "It is not unique."**

The `𝕜 = ℝ` instance of `proposition3_2_not_unique`.  Over `ℝ` the two witnesses
are still `build J` and `build (-J)`; the sign change is available because the
scalar field has characteristic zero, which `RCLike` supplies. -/
theorem proposition3_2_not_unique_real
    (hdefect : CrossedDefectsEquivalent U₁ V₁)
    (hnonacute : ¬ TauCeti.IsAcute U₁ V₁) :
    ∃ T₁ T₂ : H₁ →L[ℝ] H₁,
      IsPaperDirectRotation U₁ V₁ T₁ ∧ IsPaperDirectRotation U₁ V₁ T₂ ∧
        T₁ ≠ T₂ :=
  proposition3_2_not_unique U₁ V₁ hdefect hnonacute

/-- **Proposition 3.2's nonuniqueness in literal `∃!` form, over a real Hilbert
space.**

The `𝕜 = ℝ` instance of `proposition3_2_not_existsUnique`. -/
theorem proposition3_2_not_existsUnique_real
    (hdefect : CrossedDefectsEquivalent U₁ V₁)
    (hnonacute : ¬ TauCeti.IsAcute U₁ V₁) :
    ¬ ∃! T : H₁ →L[ℝ] H₁, IsPaperDirectRotation U₁ V₁ T :=
  proposition3_2_not_existsUnique U₁ V₁ hdefect hnonacute

end RealScalars

end Section3
end Frontier
end DavisKahan
end TauCeti