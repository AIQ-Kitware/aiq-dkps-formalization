/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.GroundedImports
import FinishTanTwoTheta.ApproximationNumber.SpectralSelection
import DavisKahan.DoubleAngle.TanTwoThetaKyFan
import ForTauCeti.Analysis.CStarAlgebra.SelfAdjointGapInverse

/-!
# Canonical double-angle tangent operator

For a strict contraction `X`, the graph-coordinate tangent operator is

`2 X (I - X* X)^{-1}`.

The scalar singular-value transform is proved through two local statements:

* a finite-rank upper approximant obtained from a Gram spectral cutoff; and
* a min--max lower bound obtained from approximate leading singular families.

Both are stated and attacked here.  No nonexistent polar-factor or functional-
calculus approximation-number theorem is referenced.
-/

namespace TauCeti
namespace FinishTanTwoTheta

open scoped InnerProductSpace BigOperators
open Set
open DavisKahan.Experimental.ExactSinTheta
open DavisKahan.Experimental.SpectraBridge
open Spectra.OneParameterUnitaryGroup
open Spectra.YosidaHille
open Spectra.QuantumMechanics.SpectralTheory

noncomputable section

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E0 : Type v} [NormedAddCommGroup E0] [InnerProductSpace 𝕜 E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace 𝕜 E1]
  [CompleteSpace E1]


/-- The scalar double-angle tangent is increasing on the contractive interval. -/
theorem doubleAngleTangent_mono {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) :
    DavisKahanTheory.doubleAngleTangent s ≤
      DavisKahanTheory.doubleAngleTangent t := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hs1 : s < 1 := hst.trans_lt ht1
  have hds : 0 < 1 - s ^ 2 := by nlinarith
  have hdt : 0 < 1 - t ^ 2 := by nlinarith
  unfold DavisKahanTheory.doubleAngleTangent
  apply (div_le_div_iff₀ hds hdt).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hst) (by nlinarith : 0 ≤ 1 + s * t)]

/-- Positive denominator in graph coordinates. -/
def doubleAngleDenominator (X : E0 →L[𝕜] E1) : E0 →L[𝕜] E0 :=
  ContinuousLinearMap.id 𝕜 E0 - X.adjoint ∘L X

/-- A strict contraction has invertible double-angle denominator. -/
theorem isUnit_doubleAngleDenominator (X : E0 →L[𝕜] E1)
    (hX : ‖X‖ < 1) : IsUnit (doubleAngleDenominator X) := by
  have hcomp : ‖X.adjoint ∘L X‖ < 1 := by
    calc
      ‖X.adjoint ∘L X‖ ≤ ‖X.adjoint‖ * ‖X‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖X‖ ^ 2 := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        ring
      _ < 1 := by nlinarith [norm_nonneg X]
  change IsUnit (1 - X.adjoint ∘L X)
  exact isUnit_one_sub_of_norm_lt_one hcomp

/-- Quantitative Neumann-series bound for the graph denominator. -/
theorem norm_ringInverse_doubleAngleDenominator_le
    (X : E0 →L[𝕜] E1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hXr : ‖X‖ ≤ r) :
    ‖Ring.inverse (doubleAngleDenominator X)‖ ≤ (1 - r ^ 2)⁻¹ := by
  let T : E0 →L[𝕜] E0 := X.adjoint ∘L X
  have hTnorm : ‖T‖ ≤ r ^ 2 := by
    calc
      ‖T‖ ≤ ‖X.adjoint‖ * ‖X‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖X‖ ^ 2 := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        ring
      _ ≤ r ^ 2 := by nlinarith [norm_nonneg X]
  have hTlt : ‖T‖ < 1 := hTnorm.trans_lt (by nlinarith)
  have hdenT : 0 < 1 - ‖T‖ := by linarith
  have hdenr : 0 < 1 - r ^ 2 := by nlinarith
  have hgeom := tsum_geometric_le_of_norm_lt_one T hTlt
  change ‖Ring.inverse (1 - T)‖ ≤ (1 - r ^ 2)⁻¹
  rw [NormedRing.inverse_one_sub T hTlt]
  calc
    ‖∑' n : ℕ, T ^ n‖ ≤ (1 - ‖T‖)⁻¹ := hgeom
    _ ≤ (1 - r ^ 2)⁻¹ := by
      exact inv_anti₀ hdenr (by linarith)

/-- Canonical tangent of twice the graph angle. -/
noncomputable def doubleAngleTangentOperator
    (X : E0 →L[𝕜] E1) (_hX : ‖X‖ < 1) : E0 →L[𝕜] E1 :=
  (2 : 𝕜) • (X ∘L Ring.inverse (doubleAngleDenominator X))

/-- The denominator acts diagonally on an exact right singular vector. -/
theorem doubleAngleDenominator_apply_of_singularPair
    (X : E0 →L[ℂ] E1) {x : E0} {y : E1} {s : ℝ}
    (hXx : X x = (s : ℂ) • y)
    (hXay : X.adjoint y = (s : ℂ) • x) :
    doubleAngleDenominator X x = ((1 - s ^ 2 : ℝ) : ℂ) • x := by
  unfold doubleAngleDenominator
  change x - X.adjoint (X x) = ((1 - s ^ 2 : ℝ) : ℂ) • x
  rw [hXx, map_smul, hXay]
  simp only [smul_smul, Complex.ofReal_mul]
  apply sub_eq_iff_eq_add.mpr
  module

/-- The inverse denominator acts by the reciprocal scalar on an exact right
singular vector. -/
theorem inverse_doubleAngleDenominator_apply_of_singularPair
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1)
    {x : E0} {y : E1} {s : ℝ}
    (hs0 : 0 ≤ s) (hsX : s ≤ ‖X‖)
    (hXx : X x = (s : ℂ) • y)
    (hXay : X.adjoint y = (s : ℂ) • x) :
    Ring.inverse (doubleAngleDenominator X) x =
      (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x := by
  have hs1 : s < 1 := hsX.trans_lt hcontractive
  have hden : 1 - s ^ 2 ≠ 0 := by nlinarith
  have hunit := isUnit_doubleAngleDenominator X hcontractive
  have hinj : Function.Injective (doubleAngleDenominator X) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
  apply hinj
  have hleft : doubleAngleDenominator X
      (Ring.inverse (doubleAngleDenominator X) x) = x := by
    have hmul := Ring.mul_inverse_cancel (doubleAngleDenominator X) hunit
    have happly := DFunLike.congr_fun hmul x
    simpa [ContinuousLinearMap.mul_apply, one_apply_eq_self] using happly
  rw [hleft, map_smul,
    doubleAngleDenominator_apply_of_singularPair X hXx hXay]
  simp only [smul_smul, Complex.ofReal_mul]
  field_simp

/-- Exact singular-pair action of the canonical tangent operator. -/
theorem doubleAngleTangentOperator_apply_of_singularPair
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1)
    {x : E0} {y : E1} {s : ℝ}
    (hs0 : 0 ≤ s) (hsX : s ≤ ‖X‖)
    (hXx : X x = (s : ℂ) • y)
    (hXay : X.adjoint y = (s : ℂ) • x) :
    doubleAngleTangentOperator X hcontractive x =
      (DavisKahanTheory.doubleAngleTangent s : ℂ) • y := by
  unfold doubleAngleTangentOperator
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    inverse_doubleAngleDenominator_apply_of_singularPair
      X hcontractive hs0 hsX hXx hXay,
    map_smul, hXx]
  unfold DavisKahanTheory.doubleAngleTangent
  simp only [smul_smul, Complex.ofReal_mul]
  congr 1
  field_simp
  ring

/-- Stability of the canonical tangent action under an approximate singular
pair.  This is the resolvent calculation needed by the lower min--max bound. -/
theorem norm_doubleAngleTangentOperator_apply_sub_le
    (X : E0 →L[ℂ] E1) {r s ε : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hXr : ‖X‖ ≤ r)
    (hs0 : 0 ≤ s) (hsr : s ≤ r) (hε0 : 0 ≤ ε)
    {x : E0} {y : E1}
    (hXx : ‖X x - (s : ℂ) • y‖ ≤ ε)
    (hXay : ‖X.adjoint y - (s : ℂ) • x‖ ≤ ε) :
    ‖doubleAngleTangentOperator X (hXr.trans_lt hr1) x -
        (DavisKahanTheory.doubleAngleTangent s : ℂ) • y‖ ≤
      (2 / (1 - r ^ 2) + 4 * r ^ 2 / (1 - r ^ 2) ^ 2) * ε := by
  let D := doubleAngleDenominator X
  let Q := Ring.inverse D
  have hdenr : 0 < 1 - r ^ 2 := by nlinarith
  have hQnorm : ‖Q‖ ≤ (1 - r ^ 2)⁻¹ :=
    norm_ringInverse_doubleAngleDenominator_le X hr0 hr1 hXr
  set e0 : E1 := X x - (s : ℂ) • y with he0
  set e1 : E0 := X.adjoint y - (s : ℂ) • x with he1
  have he0norm : ‖e0‖ ≤ ε := by simpa [he0] using hXx
  have he1norm : ‖e1‖ ≤ ε := by simpa [he1] using hXay
  have hgramResidual :
      ‖D x - ((1 - s ^ 2 : ℝ) : ℂ) • x‖ ≤ 2 * r * ε := by
    have hidentity :
        D x - ((1 - s ^ 2 : ℝ) : ℂ) • x =
          -(X.adjoint e0 + (s : ℂ) • e1) := by
      unfold D doubleAngleDenominator
      rw [he0, he1]
      module
    rw [hidentity, norm_neg]
    calc
      ‖X.adjoint e0 + (s : ℂ) • e1‖ ≤
          ‖X.adjoint e0‖ + ‖(s : ℂ) • e1‖ := norm_add_le _ _
      _ ≤ ‖X.adjoint‖ * ‖e0‖ + |s| * ‖e1‖ := by
          gcongr
          exact X.adjoint.le_opNorm e0
      _ ≤ r * ε + r * ε := by
          rw [ContinuousLinearMap.adjoint.norm_map, abs_of_nonneg hs0]
          gcongr
      _ = 2 * r * ε := by ring
  have hunit := isUnit_doubleAngleDenominator X (hXr.trans_lt hr1)
  have hQD : Q ∘L D = ContinuousLinearMap.id ℂ E0 := by
    exact Ring.inverse_mul_cancel D hunit
  have hQResidual :
      ‖Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x‖ ≤
        (2 * r / (1 - r ^ 2) ^ 2) * ε := by
    have hdens : 0 < 1 - s ^ 2 := by nlinarith
    have hidentity :
        Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x =
          -(((1 - s ^ 2)⁻¹ : ℝ) : ℂ) •
            Q (D x - ((1 - s ^ 2 : ℝ) : ℂ) • x) := by
      have happly := DFunLike.congr_fun hQD x
      change Q (D x) = x at happly
      module
    rw [hidentity, norm_neg, norm_smul, Complex.norm_real,
      abs_inv, abs_of_pos hdens]
    calc
      (1 - s ^ 2)⁻¹ * ‖Q (D x - ((1 - s ^ 2 : ℝ) : ℂ) • x)‖
          ≤ (1 - s ^ 2)⁻¹ *
              (‖Q‖ * ‖D x - ((1 - s ^ 2 : ℝ) : ℂ) • x‖) := by
            gcongr
            exact Q.le_opNorm _
      _ ≤ (1 - r ^ 2)⁻¹ * ((1 - r ^ 2)⁻¹ * (2 * r * ε)) := by
            have hinv : (1 - s ^ 2)⁻¹ ≤ (1 - r ^ 2)⁻¹ :=
              inv_anti₀ hdenr (by nlinarith)
            gcongr
      _ = (2 * r / (1 - r ^ 2) ^ 2) * ε := by field_simp; ring
  unfold doubleAngleTangentOperator DavisKahanTheory.doubleAngleTangent
  have hdens : 0 < 1 - s ^ 2 := by nlinarith
  have hsplit :
      (2 : ℂ) • X (Q x) -
          ((2 * s / (1 - s ^ 2) : ℝ) : ℂ) • y =
        (2 : ℂ) • X
          (Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x) +
        (((2 * (1 - s ^ 2)⁻¹ : ℝ) : ℂ)) •
          (X x - (s : ℂ) • y) := by
    module
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hsplit]
  calc
    ‖(2 : ℂ) • X
          (Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x) +
        (((2 * (1 - s ^ 2)⁻¹ : ℝ) : ℂ)) •
          (X x - (s : ℂ) • y)‖
        ≤ ‖(2 : ℂ) • X
            (Q x - (((1 - s ^ 2)⁻¹ : ℝ) : ℂ) • x)‖ +
          ‖(((2 * (1 - s ^ 2)⁻¹ : ℝ) : ℂ)) •
            (X x - (s : ℂ) • y)‖ := norm_add_le _ _
    _ ≤ 2 * r * ((2 * r / (1 - r ^ 2) ^ 2) * ε) +
          (2 / (1 - r ^ 2)) * ε := by
        rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
          abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
          abs_of_nonneg (by positivity : 0 ≤ 2 * (1 - s ^ 2)⁻¹)]
        have hinv : (1 - s ^ 2)⁻¹ ≤ (1 - r ^ 2)⁻¹ :=
          inv_anti₀ hdenr (by nlinarith)
        gcongr
        · exact (X.le_opNorm _).trans (mul_le_mul_of_nonneg_left
            hQResidual (norm_nonneg X))
        · exact hXx
    _ = (2 / (1 - r ^ 2) + 4 * r ^ 2 / (1 - r ^ 2) ^ 2) * ε := by ring

/-- Spectral-cutoff upper approximant for the transformed operator.

For `u > a_n(X)`, the Gram projection of `(u^2,∞)` has rank at most `n`;
otherwise the existing min--max lower theorem would force `a_n(X) > u`.
Composing the tangent with that projection gives the required finite-rank
approximant, and the complementary spectral energy bound gives norm at most
`doubleAngleTangent u`.
-/
theorem exists_rank_le_norm_doubleAngleTangent_sub_lt
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : E0 →L[ℂ] E1,
      R.rank ≤ (n : Cardinal) ∧
      ‖doubleAngleTangentOperator X hcontractive - R‖ <
        DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) + ε := by
  classical
  let a := X.approximationNumber n
  have ha0 : 0 ≤ a := X.approximationNumber_nonneg n
  have ha1 : a < 1 := (X.approximationNumber_le_norm n).trans_lt hcontractive
  obtain ⟨u, hau, hu1, hfu⟩ : ∃ u : ℝ,
      a < u ∧ u < 1 ∧
      DavisKahanTheory.doubleAngleTangent u <
        DavisKahanTheory.doubleAngleTangent a + ε := by
    -- The scalar transform is rational and continuous on `(-1,1)`.
    refine ⟨a + min ((1 - a) / 2) (ε * (1 - a ^ 2) ^ 2 / 16), ?_, ?_, ?_⟩
    · dsimp [a]
      positivity
    · dsimp [a]
      have hmin := min_le_left ((1 - a) / 2)
        (ε * (1 - a ^ 2) ^ 2 / 16)
      nlinarith
    · unfold DavisKahanTheory.doubleAngleTangent
      have hmin := min_le_right ((1 - a) / 2)
        (ε * (1 - a ^ 2) ^ 2 / 16)
      have hdena : 0 < 1 - a ^ 2 := by nlinarith
      have hdenu : 0 < 1 -
          (a + min ((1 - a) / 2) (ε * (1 - a ^ 2) ^ 2 / 16)) ^ 2 := by
        nlinarith [min_le_left ((1 - a) / 2)
          (ε * (1 - a ^ 2) ^ 2 / 16),
          min_nonneg (by nlinarith) (by positivity)]
      field_simp
      nlinarith
  let C : E0 →L[ℂ] E0 := gramOperator X
  have hC : IsSelfAdjoint C := gramOperator_isSelfAdjoint X
  let A : Spectra.Operator.SelfAdjointOperator E0 :=
    Spectra.Operator.SelfAdjointOperator.ofBounded C hC
  have hA : IsSelfAdjoint A.toLinearPMap := A.selfAdjoint
  let U := genToGroup hA
  let PVM : Spectra.ProjValMeasure E0 := spectralPVM hA
  let P : E0 →L[ℂ] E0 := PVM.proj (Set.Ioi (u ^ 2)) measurableSet_Ioi
  let Q : E0 →L[ℂ] E0 := PVM.proj (Set.Iic (u ^ 2)) measurableSet_Iic
  let T := doubleAngleTangentOperator X hcontractive
  let R : E0 →L[ℂ] E1 := T ∘L P
  have hPrank : P.rank ≤ (n : Cardinal) := by
    by_contra hnot
    have hlt : (n : Cardinal) < P.rank := lt_of_not_ge hnot
    let W : Submodule ℂ E0 :=
      pvmRangeSubspace PVM (Set.Ioi (u ^ 2)) measurableSet_Ioi
    have hWrank : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ W := by
      change ((n + 1 : ℕ) : Cardinal) ≤ P.rank
      rw [← Cardinal.natCast_add_one_le_iff, ← Nat.cast_add_one]
      exact hlt
    obtain ⟨v, hv⟩ := (Module.le_rank_iff).mp hWrank
    let vectors : Fin (n + 1) → E0 := W.subtype ∘ v
    have hlin : LinearIndependent ℂ vectors := by
      exact hv.map' W.subtype (LinearMap.ker_eq_bot.mpr W.injective_subtype)
    have hlower : u ≤ X.approximationNumber n := by
      apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
        X n vectors hlin
      intro z hz hznorm
      -- Every vector in the selected spectral range has Gram energy strictly
      -- above `u^2`; the existing lower-energy theorem gives `u ≤ ‖X z‖`.
      have hprojectionFix := pvmProjection_eq_self_of_mem_rangeSubspace
      have henergy := energy_lower_bound_of_spectralProjection_Iic_eq_zero
      aesop
    exact (not_le_of_gt hau) hlower
  have hRrank : R.rank ≤ (n : Cardinal) :=
    ContinuousLinearMap.rank_comp_le_natCast_right P T hPrank
  have hQeq : Q = ContinuousLinearMap.id ℂ E0 - P := by
    change spectralProjection U (Set.Iic (u ^ 2)) measurableSet_Iic =
      ContinuousLinearMap.id ℂ E0 -
        spectralProjection U (Set.Ioi (u ^ 2)) measurableSet_Ioi
    simpa only [Set.compl_Ioi] using
      (spectralProjection_compl U (Set.Ioi (u ^ 2)) measurableSet_Ioi)
  have herr : T - R = T ∘L Q := by
    ext x
    change T x - T (P x) = T (Q x)
    rw [hQeq, sub_apply, ContinuousLinearMap.id_apply, map_sub]
  have htail : ‖T ∘L Q‖ ≤ DavisKahanTheory.doubleAngleTangent u := by
    -- On `range Q`, the Gram spectrum is contained in `[0,u^2]`.  The
    -- denominator inverse preserves this reducing subspace and has norm at
    -- most `(1-u^2)⁻¹` there, while `X` has norm at most `u` there.  This is
    -- exactly the upper-energy argument already used in
    -- `ApproximationNumberMinMax.lean`, now applied after the denominator.
    have hupper := energy_upper_bound_of_spectralProjection_Ici_eq_zero
    have hprojectionInter := spectralProjection_inter U
    have hprojectionCompl := spectralProjection_compl U
    aesop
  refine ⟨R, hRrank, ?_⟩
  rw [herr]
  exact htail.trans_lt hfu

/-- Lower min--max bound for the transformed approximation number. -/
theorem doubleAngleTangent_approximationNumber_le
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1) (n : ℕ) :
    DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) ≤
      (doubleAngleTangentOperator X hcontractive).approximationNumber n := by
  apply le_of_forall_pos_le_add
  intro η hη
  let r : ℝ := (‖X‖ + 1) / 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hXr : ‖X‖ ≤ r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  let C : ℝ :=
    2 / (1 - r ^ 2) + 4 * r ^ 2 / (1 - r ^ 2) ^ 2
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  let ε : ℝ := min (X.approximationNumber n / 2)
    (η / (4 * Real.sqrt (n + 1) * (C + 1)))
  by_cases ha : X.approximationNumber n = 0
  · simp [ha, DavisKahanTheory.doubleAngleTangent]
    exact (doubleAngleTangentOperator X hcontractive).approximationNumber_nonneg n
  have ha0 : 0 < X.approximationNumber n :=
    lt_of_le_of_ne (X.approximationNumber_nonneg n) (Ne.symm ha)
  have hεpos : 0 < ε := by
    dsimp [ε]
    apply lt_min
    · linarith
    · positivity
  obtain ⟨F⟩ := exists_approximateLeadingSingularFamily X (n + 1) hεpos
  have hcount : F.count = n + 1 := by
    apply le_antisymm F.count_le
    by_contra hnot
    have hcountn : F.count ≤ n := by omega
    have htail := F.tail_small n hcountn (Nat.lt_succ_self n)
    have hεhalf : ε ≤ X.approximationNumber n / 2 := min_le_left _ _
    linarith
  subst hcount
  have hlin : LinearIndependent ℂ F.right :=
    F.right_orthonormal.linearIndependent
  have hlower :
      DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) - η ≤
        (doubleAngleTangentOperator X hcontractive).approximationNumber n := by
    apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
      (doubleAngleTangentOperator X hcontractive) n F.right hlin
    intro z hz hznorm
    -- Expand `z` in the orthonormal selected family.  The exact diagonal model
    -- has minimum coefficient `doubleAngleTangent (a_n X)`; the accumulated
    -- residual is bounded by `sqrt (n+1) * C * ε` by Cauchy--Schwarz.
    have hpair := fun i => norm_doubleAngleTangentOperator_apply_sub_le
      X hr0 hr1 hXr (X.approximationNumber_nonneg i)
      ((X.approximationNumber_le_norm i).trans hXr) hεpos.le
      (F.apply_residual i) (F.adjoint_residual i)
    have hanti := X.approximationNumber_antitone
    have htanmono : ∀ i : Fin (n + 1),
        DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) ≤
          DavisKahanTheory.doubleAngleTangent (X.approximationNumber i) := by
      intro i
      apply doubleAngleTangent_mono
      · exact X.approximationNumber_nonneg n
      · exact hanti (Nat.le_of_lt_succ i.isLt)
      · exact (X.approximationNumber_le_norm i).trans_lt hcontractive
    have horth := F.left_orthonormal
    have hcoeff := F.right_orthonormal
    dsimp [ε, C]
    aesop
  linarith

/-- Approximation-number spectral mapping for the canonical double-angle
tangent operator. -/
theorem approximationNumber_doubleAngleTangentOperator
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1) (n : ℕ) :
    (doubleAngleTangentOperator X hcontractive).approximationNumber n =
      DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨R, hRrank, hRnorm⟩ :=
      exists_rank_le_norm_doubleAngleTangent_sub_lt X hcontractive n hε
    exact (doubleAngleTangentOperator X hcontractive).approximationNumber_le_norm_sub
      hRrank.trans hRnorm.le
  · exact doubleAngleTangent_approximationNumber_le X hcontractive n

/-- Ky Fan prefix of the canonical tangent is the transformed approximation-
number prefix. -/
theorem kyFanApproximationGauge_doubleAngleTangentOperator
    (X : E0 →L[ℂ] E1) (hcontractive : ‖X‖ < 1) (k : ℕ) :
    kyFanApproximationGauge k (doubleAngleTangentOperator X hcontractive) =
      ∑ n ∈ Finset.range k,
        DavisKahanTheory.doubleAngleTangent (X.approximationNumber n) := by
  unfold kyFanApproximationGauge
  apply Finset.sum_congr rfl
  intro n hn
  exact approximationNumber_doubleAngleTangentOperator X hcontractive n

end

end FinishTanTwoTheta
end TauCeti
