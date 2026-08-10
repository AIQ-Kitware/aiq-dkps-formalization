/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Geometry.Angle.PaperOperatorAngleReal
import DavisKahan.Sources.DavisKahan1970.SinTwoThetaWholeSpace
import DavisKahan.Sources.DavisKahan1970.TanThetaWholeSpace
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaWholeSpace
import DavisKahan.SpectralTheory.Complexification.FormTransport
import DavisKahan.SpectralTheory.Complexification.SubmoduleEquiv
import DavisKahan.SpectralTheory.Complexification.Spectrum
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.ComplexificationGauge

/-!
# The ambient halves of the Section 2 theorems over a **real** Hilbert space

Standing assumption 1 of Davis--Kahan 1970 is that the Hilbert space is "real or
complex".  The three ambient (whole-space) conclusions

`δ ‖tan Θ‖ ≤ ‖H‖`,  `δ ‖sin 2Θ‖ ≤ 2‖H‖`,  `δ ‖tan 2Θ‖ ≤ 2‖H‖`

are proved over `ℂ` in `TanThetaWholeSpace.lean`, `SinTwoThetaWholeSpace.lean`
and `TanTwoThetaWholeSpace.lean`.  This module states and proves them over a real
Hilbert space, with **no** loss:

* the space, the operators, the subspaces and the angle operators are all real
  (`DavisKahan/Geometry/Angle/PaperOperatorAngleReal.lean` supplies the real
  angle operators, and proves they are the real restrictions of the complex
  ones);
* the constants `δ`, `1` and `2` are unchanged;
* ideal membership is *concluded*, exactly as in the complex statements, not
  assumed;
* every source unitarily invariant norm is covered at once, because
  `PaperUnitaryInvariantNorm.gauge_complexify` says the gauge of a real operator
  and of its complexification agree.

## How the transport works

There is no perturbation theory here.  The real configuration is complexified,
the complex theorem is applied verbatim, and the conclusion is read back.  Three
kinds of hypothesis have to travel, and all three were already available:

* quadratic form bounds and invariance/off-diagonality conditions, by
  `DavisKahan/SpectralTheory/Complexification/FormTransport.lean`;
* compressions to a subspace, by `complexifySubmoduleEquiv` — the adapter
  identifying `RealComplexification ↥Z` with `↥(complexifySubmodule Z)`, whose
  module docstring names the two lifts this file performs;
* the real spectrum of a compression, by `realSpectrum_conjEquiv` and
  `realSpectrum_complexify`, assembled here as
  `spectrum_compressOperator_complexifySubmodule`.

## Main results

* `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real`
* `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`
* `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real`

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: standing assumption 1, the four
  theorems of Section 2, and their proofs in Sections 6 and 7.
-/

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Experimental.ExactSinTheta
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Experimental.Foundation
open TauCeti.DavisKahan.Experimental.Foundation.RealComplexification

open scoped InnerProductSpace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete.  `local instance` does not propagate through imports,
so it is reinstalled here, on both scalar fields. -/
local instance instCompleteSpaceCoeOfHasOrthogonalProjectionRealWholeSpace
    {𝕜 : Type*} [RCLike 𝕜] {G : Type v} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (Z : Submodule 𝕜 G) [Z.HasOrthogonalProjection] : CompleteSpace Z :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection Z).completeSpace_coe

/-! ### Transporting the compression hypotheses -/

section Compression

variable (Z : Submodule ℝ E) [Z.HasOrthogonalProjection]

/-- The real orthogonal compression of an operator to a closed subspace.

This is the real-scalar spelling of `compressOperator`, and it is that operator:
`DavisKahanExt.compressOperator` is `RCLike`-generic, and at `𝕜 = ℝ` its body is
this one, so `compressOperatorReal Z A = compressOperator Z A` holds by `rfl` and
`compressOperator_eq_restrict_of_invariant` applies to it verbatim.  (`ℂ`-only
spellings such as `theorem63Compression` are a separate matter; it is Mathlib's
functional calculus, not the compression, that forces those.)  The two names
should eventually be one; until then, do not restate a compression fact for both. -/
def compressOperatorReal (A : E →L[ℝ] E) : Z →L[ℝ] Z :=
  Z.orthogonalProjectionOnto ∘L A ∘L Z.subtypeL

omit [CompleteSpace E] in
/-- **Compressing to a complexified subspace is a unitary conjugate of the
complexified real compression.** -/
theorem compressOperator_complexifySubmodule (A : E →L[ℝ] E) :
    compressOperator (complexifySubmodule Z) (complexify A) =
      RealComplexification.conjEquiv (complexifySubmoduleEquiv Z)
        (complexify (compressOperatorReal Z A)) := by
  refine ContinuousLinearMap.ext fun z => ?_
  have h := orthogonalProjectionOnto_complexify_apply Z A
    ((complexifySubmoduleEquiv Z).symm z)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h

omit [CompleteSpace E] in
/-- **The real spectrum of a compression survives complexification.**  Stated
with the subspace as a hypothesis so that it applies to `(complexifySubmodule Z)ᗮ`
as written, without a dependent rewrite under the projection instance. -/
theorem realSpectrum_compressOperator_complexifySubmodule
    {W : Submodule ℂ (RealComplexification E)} [W.HasOrthogonalProjection]
    (A : E →L[ℝ] E) (hW : W = complexifySubmodule Z) :
    realSpectrum (compressOperator W (complexify A)) =
      realSpectrum (compressOperatorReal Z A) := by
  subst hW
  rw [compressOperator_complexifySubmodule Z A,
    RealComplexification.realSpectrum_conjEquiv,
    RealComplexification.realSpectrum_complexify]

omit [CompleteSpace E] in
/-- A real upper form bound on a compression transports to the complexified
compression with the same constant. -/
theorem re_inner_compressOperator_le (A : E →L[ℝ] E) {alpha : ℝ}
    (h : ∀ z : Z, ⟪compressOperatorReal Z A z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (z : complexifySubmodule Z) :
    RCLike.re ⟪compressOperator (complexifySubmodule Z) (complexify A) z, z⟫_ℂ ≤
      alpha * ‖z‖ ^ 2 := by
  obtain ⟨w, rfl⟩ : ∃ w, (complexifySubmoduleEquiv Z) w = z :=
    ⟨_, (complexifySubmoduleEquiv Z).apply_symm_apply z⟩
  rw [compressOperator_complexifySubmodule Z A,
    RealComplexification.conjEquiv_apply, LinearIsometryEquiv.symm_apply_apply,
    (complexifySubmoduleEquiv Z).inner_map_map, LinearIsometryEquiv.norm_map,
    re_inner_complexify, TauCeti.RealComplexification.norm_sq]
  calc ⟪compressOperatorReal Z A (re w), re w⟫_ℝ +
        ⟪compressOperatorReal Z A (im w), im w⟫_ℝ
      ≤ alpha * ‖re w‖ ^ 2 + alpha * ‖im w‖ ^ 2 :=
        add_le_add (h _) (h _)
    _ = alpha * (‖re w‖ ^ 2 + ‖im w‖ ^ 2) := by ring

end Compression

/-! ### The three ambient theorems over a real Hilbert space -/

variable {A H T B : E →L[ℝ] E} {U V : Submodule ℝ E}
  [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **Davis--Kahan 1970, the whole-space `tan Θ` theorem over a REAL Hilbert
space, for every source unitarily invariant norm**: `δ ‖tan Θ‖ ≤ ‖H‖`, the
second conclusion of the Section 2 tangent theorem.

No dimension hypothesis, no compactness hypothesis; `[U.HasOrthogonalProjection]`
is the formal encoding of the paper's "closed subspace".  As in the complex
statement, uniform transversality `‖sin Θ‖ < 1` is assumed — that is what makes
`tan Θ` the tangent — and membership of `tan Θ` in the norm's ideal is
concluded. -/
theorem tanTheta_wholeSpace_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
    (hT : IsSelfAdjoint T) (hA : IsSelfAdjoint A)
    (hV : T.Reduces V) (hAU : ∀ x ∈ U, A x ∈ U)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hCompressionUpper : ∀ z : U, ⟪compressOperatorReal U T z, z⟫_ℝ ≤
      alpha * ‖z‖ ^ 2)
    (hUnwantedLower : ∀ y ∈ Vᗮ, (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ)
    (htr : ‖paperSinAngleOperatorR U V‖ < 1)
    (hMem : N.Mem (T - A)) :
    N.Mem (paperTanAngleOperatorR U V) ∧
      delta * N.gauge (paperTanAngleOperatorR U V) ≤ N.gauge (T - A) := by
  have htrC : ‖sinAngleOperatorC (complexifySubmodule U)
      (complexifySubmodule V)‖ < 1 := by
    rwa [← complexify_paperSinAngleOperatorR U V, norm_complexify]
  have hMemC : N.Mem (complexify T - complexify A) := by
    rw [← complexify_sub]
    exact (PaperUnitaryInvariantNorm.mem_complexify_iff N (T - A)).2 hMem
  obtain ⟨hmemC, hboundC⟩ :=
    tanTheta_wholeSpace_paperUINorm (E := RealComplexification E) N
      (T := complexify T) (A := complexify A)
      (U := complexifySubmodule U) (V := complexifySubmodule V)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
        ((complexify_isSelfAdjoint_iff T).2 hT))
      ((complexify_isSelfAdjoint_iff A).2 hA)
      ((complexify_reduces_iff T V).2 hV)
      (fun z hz => mapsTo_complexifySubmodule hAU hz)
      hdelta
      (fun z => re_inner_compressOperator_le U T hCompressionUpper z)
      (fun y hy => by
        rw [← complexifySubmodule_orthogonal V] at hy
        exact le_re_inner_of_mem_complexifySubmodule hUnwantedLower hy)
      htrC hMemC
  rw [← complexify_paperTanAngleOperatorR U V] at hmemC hboundC
  rw [← complexify_sub] at hboundC
  refine ⟨(PaperUnitaryInvariantNorm.mem_complexify_iff N _).1 hmemC, ?_⟩
  rwa [PaperUnitaryInvariantNorm.gauge_complexify,
    PaperUnitaryInvariantNorm.gauge_complexify] at hboundC

/-- **Davis--Kahan 1970, the whole-space `sin 2Θ` theorem over a REAL Hilbert
space, for every source unitarily invariant norm**: `δ ‖sin 2Θ‖ ≤ 2‖H‖`, the
second conclusion of the Section 2 `sin 2Θ` theorem and equation (7.5). -/
theorem sinTwoTheta_wholeSpace_paperUINorm_real
    (N : PaperUnitaryInvariantNorm)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hU : A.Reduces U) (hV : B.Reduces V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperatorReal U A) ⊆ Set.Icc a b)
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperatorReal Uᗮ A),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    N.Mem (paperSinTwoAngleOperatorR U V) ∧
      d * N.gauge (paperSinTwoAngleOperatorR U V) ≤ 2 * N.gauge (B - A) := by
  have hMemC : N.Mem (complexify B - complexify A) := by
    rw [← complexify_sub]
    exact (PaperUnitaryInvariantNorm.mem_complexify_iff N (B - A)).2 hMem
  obtain ⟨hmemC, hboundC⟩ :=
    sinTwoTheta_wholeSpace_paperUINorm (E := RealComplexification E) N
      (A := complexify A) (B := complexify B)
      (U := complexifySubmodule U) (V := complexifySubmodule V)
      ((complexify_isSelfAdjoint_iff A).2 hA)
      ((complexify_isSelfAdjoint_iff B).2 hB)
      ((complexify_reduces_iff A U).2 hU)
      ((complexify_reduces_iff B V).2 hV)
      hd hab
      (fun r hr => by
        -- `realSpectrum` is `spectrum` over the *native* scalar field, so it is
        -- free of the real-algebra diamond that a bare `spectrum ℝ` rewrite
        -- would have to cross here.
        have hr' : r ∈ realSpectrum
            (compressOperator (complexifySubmodule U) (complexify A)) := hr
        rw [realSpectrum_compressOperator_complexifySubmodule U A rfl] at hr'
        exact hUspec hr')
      (fun r hr => by
        have hr' : r ∈ realSpectrum
            (compressOperator (complexifySubmodule U)ᗮ (complexify A)) := hr
        rw [realSpectrum_compressOperator_complexifySubmodule (E := E) Uᗮ A
          (W := (complexifySubmodule U)ᗮ)
          (complexifySubmodule_orthogonal U).symm] at hr'
        exact hUspec' r hr')
      hMemC
  rw [← complexify_paperSinTwoAngleOperatorR U V] at hmemC hboundC
  rw [← complexify_sub] at hboundC
  refine ⟨(PaperUnitaryInvariantNorm.mem_complexify_iff N _).1 hmemC, ?_⟩
  rwa [PaperUnitaryInvariantNorm.gauge_complexify,
    PaperUnitaryInvariantNorm.gauge_complexify] at hboundC

/-- **Davis--Kahan 1970, the whole-space `tan 2Θ` theorem over a REAL Hilbert
space, for every source unitarily invariant norm**: `δ ‖tan 2Θ‖ ≤ 2‖H‖`, the
second conclusion of the Section 2 double-angle tangent theorem.

As in the complex statement the quarter-angle branch is *concluded* from the
four ordered form bounds, not assumed, and membership of `tan 2Θ` in the norm's
ideal is concluded as well. -/
theorem tanTwoTheta_wholeSpace_paperUINorm_real
    (N : PaperUnitaryInvariantNorm) {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    (hab : a < b)
    (hUhigh : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hUperpLow : ∀ x ∈ Uᗮ, ⟪A x, x⟫_ℝ ≤ a * ‖x‖ ^ 2)
    (hVhigh : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ ⟪(A + H) x, x⟫_ℝ)
    (hVperpLow : ∀ x ∈ Vᗮ, ⟪(A + H) x, x⟫_ℝ ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hHmem : N.Mem H) :
    N.Mem (paperTanTwoAngleOperatorR U V) ∧
      (b - a) * N.gauge (paperTanTwoAngleOperatorR U V) ≤ 2 * N.gauge H := by
  have hsum : complexify A + complexify H = complexify (A + H) :=
    (complexify_add A H).symm
  obtain ⟨hmemC, hboundC⟩ :=
    tanTwoTheta_wholeSpace_paperUINorm (E := RealComplexification E) N
      (A := complexify A) (H := complexify H)
      (U := complexifySubmodule U) (V := complexifySubmodule V)
      ((complexify_isSelfAdjoint_iff A).2 hA)
      ((complexify_isSelfAdjoint_iff H).2 hH)
      (fun z hz => mapsTo_complexifySubmodule hAU hz)
      (fun z hz => by
        rw [hsum]
        exact mapsTo_complexifySubmodule hAplusH_V hz)
      hab
      (fun z hz => le_re_inner_of_mem_complexifySubmodule hUhigh hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal U] at hz
        exact re_inner_le_of_mem_complexifySubmodule hUperpLow hz)
      (fun z hz => by
        rw [hsum]
        exact le_re_inner_of_mem_complexifySubmodule hVhigh hz)
      (fun z hz => by
        rw [← complexifySubmodule_orthogonal V] at hz
        rw [hsum]
        exact re_inner_le_of_mem_complexifySubmodule hVperpLow hz)
      (fun z hz => mapsTo_orthogonal_complexifySubmodule U hHU hz)
      (fun z hz => mapsTo_of_mem_orthogonal_complexifySubmodule U hHUperp hz)
      ((PaperUnitaryInvariantNorm.mem_complexify_iff N H).2 hHmem)
  rw [← complexify_paperTanTwoAngleOperatorR U V] at hmemC hboundC
  refine ⟨(PaperUnitaryInvariantNorm.mem_complexify_iff N _).1 hmemC, ?_⟩
  rwa [PaperUnitaryInvariantNorm.gauge_complexify,
    PaperUnitaryInvariantNorm.gauge_complexify] at hboundC

end

end DavisKahan1970
end TauCeti
