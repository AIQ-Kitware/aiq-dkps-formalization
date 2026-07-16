/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.GenuineUnbounded
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The honest unbounded `sin Θ` layer: unitary-invariant ideal scope

Ideal-gauge companion to `SinTheta/GenuineUnbounded.lean`, lifting the
operator-norm unbounded `sin Θ` endpoint to the paper's unitary-invariant
norm scope over any `RectangularSymmetricIdealFamily`.

Main results, all fully proved:

* `exists_bounded_shift_extension`: a symmetric closed operator whose
  quadratic form lies in `[β, α]` admits a bounded extension of its shift
  by the center `c = (α+β)/2`, of norm at most the radius `r = (α-β)/2` —
  the continuous extension along the dense domain embedding of the shifted
  graph map.
* `mem_and_gauge_le_of_boundedLeft_exteriorRight`: the ideal-gauge
  constant-one Sylvester estimate in the `sin Θ` orientation — bounded
  interval block on the left (through its shift extension), exterior closed
  block on the right through a proof-carrying bounded shifted right inverse.
  The solution is exhibited as the ideal-gauge limit of the Neumann
  iteration `Y = S Y J - C J`, membership coming from the family's
  `gauge_complete` field and operator-norm limit uniqueness.
* `sinTheta_unbounded_gauge`: **the unbounded Davis--Kahan `sin Θ` theorem
  at unitary-invariant ideal scope** — for the paper-shaped
  `UnboundedSinThetaData` with the trial block's form in `[β, α]`, the
  complementary block's shifted resolvent bounded by `((α-β)/2 + δ)⁻¹`,
  and the projected residual in the ideal, the projected angle operator is
  in the ideal with `δ ‖X⋆ F₁‖_N ≤ ‖R⋆ F₁‖_N`.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **Bounded extension of the centered interval block.**  A symmetric closed
operator whose quadratic form lies in `[β, α]` has a bounded shift `B - c`
on its dense domain (`c = (α+β)/2`, radius `r = (α-β)/2`), which therefore
extends to a bounded operator on the whole space with the same norm bound
and agreeing with `B - c` on the domain. -/
theorem exists_bounded_shift_extension
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    (hsym : B.IsSymmetric) {β α : ℝ} (hβα : β ≤ α)
    (hlow : SemiboundedBelow B β) (hhigh : SemiboundedAbove B α) :
    ∃ S : F →L[𝕜] F, ‖S‖ ≤ (α - β) / 2 ∧
      ∀ y : B.domain, S (y : F) =
        B.toLinearMap y - (((α + β) / 2 : ℝ) : 𝕜) • (y : F) := by
  have hr0 : (0 : ℝ) ≤ (α - β) / 2 := by linarith
  set g : B.domain →ₗ[𝕜] F :=
    B.toLinearMap - (((α + β) / 2 : ℝ) : 𝕜) • B.domain.subtype with hgdef
  have hgapply : ∀ y : B.domain,
      g y = B.toLinearMap y - (((α + β) / 2 : ℝ) : 𝕜) • (y : F) := by
    intro y
    simp [hgdef, LinearMap.sub_apply, LinearMap.smul_apply]
  have hgbound : ∀ y : B.domain, ‖g y‖ ≤ (α - β) / 2 * ‖y‖ := by
    intro y
    rw [hgapply y]
    exact ForMathlib.DavisKahanExt.ClosedOperator.norm_shift_apply_le_of_form_bounds
      hsym hβα hlow hhigh y
  set f : B.domain →L[𝕜] F := g.mkContinuous ((α - β) / 2) hgbound with hfdef
  have hrange : Set.range ((B.domain.subtypeL : B.domain →L[𝕜] F)) =
      (B.domain : Set F) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hdense : DenseRange ((B.domain.subtypeL : B.domain →L[𝕜] F)) := by
    show Dense (Set.range _)
    rw [hrange]
    exact B.dense_domain
  have hui : IsUniformInducing ((B.domain.subtypeL : B.domain →L[𝕜] F)) :=
    isometry_subtype_coe.isUniformInducing
  refine ⟨f.extend (B.domain.subtypeL), ?_, ?_⟩
  · have h1 : ‖f.extend (B.domain.subtypeL)‖ ≤ ((1 : NNReal) : ℝ) * ‖f‖ := by
      refine ContinuousLinearMap.opNorm_extend_le f hdense fun x => ?_
      rw [NNReal.coe_one, one_mul]
      exact le_of_eq rfl
    have h2 : ‖f‖ ≤ (α - β) / 2 :=
      LinearMap.mkContinuous_norm_le g hr0 hgbound
    calc ‖f.extend (B.domain.subtypeL)‖
        ≤ ((1 : NNReal) : ℝ) * ‖f‖ := h1
      _ = ‖f‖ := by rw [NNReal.coe_one, one_mul]
      _ ≤ (α - β) / 2 := h2
  · intro y
    have h := ContinuousLinearMap.extend_eq f hdense hui y
    calc (f.extend (B.domain.subtypeL)) (y : F)
        = f y := h
      _ = B.toLinearMap y - (((α + β) / 2 : ℝ) : 𝕜) • (y : F) := hgapply y

/-- **Ideal-gauge constant-one Sylvester estimate, `sin Θ` orientation.**
`S` is the bounded shift extension of the interval block (`‖S‖ ≤ ρ`), the
closed block `Λ` is exterior through a bounded shifted right inverse `J`
of norm at most `(ρ + δ)⁻¹`, and the shifted equation
`S (Y y) - (Y (Λ y) - c Y y) = C y` holds on the domain of `Λ`.  If `C`
belongs to the rectangular symmetric ideal family, then so does `Y`, with
`δ · gauge Y ≤ gauge C` — by the Neumann iteration `Y = S Y J - C J` in the
ideal gauge. -/
theorem mem_and_gauge_le_of_boundedLeft_exteriorRight
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {S : F →L[𝕜] F}
    {Λ : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := G)}
    {Y C : G →L[𝕜] F} {c ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hSnorm : ‖S‖ ≤ ρ)
    {J : G →L[𝕜] G} (hdom : ∀ z : G, J z ∈ Λ.domain)
    (hres : ∀ z : G,
      Λ.toLinearMap ⟨J z, hdom z⟩ - ((c : ℝ) : 𝕜) • J z = z)
    (hJnorm : ‖J‖ ≤ (ρ + δ)⁻¹)
    (hEq : ∀ y : Λ.domain,
      S (Y (y : G)) -
        (Y (Λ.toLinearMap y) - ((c : ℝ) : 𝕜) • Y (y : G)) = C (y : G))
    (hC : N.Mem C) :
    N.Mem Y ∧ δ * N.gauge Y ≤ N.gauge C := by
  have hρδ : (0 : ℝ) < ρ + δ := by linarith
  set q : ℝ := ρ * (ρ + δ)⁻¹ with hqdef
  have hq0 : 0 ≤ q := mul_nonneg hρ (inv_nonneg.mpr hρδ.le)
  have hq1 : q < 1 := by
    rw [hqdef, ← div_eq_mul_inv]
    exact (div_lt_one hρδ).mpr (by linarith)
  -- the bounded fixed-point identity `Y = S Y J - C J`
  have hfix : Y = S ∘L Y ∘L J + -(C ∘L J) := by
    ext z
    have hres' : Λ.toLinearMap ⟨J z, hdom z⟩ =
        z + ((c : ℝ) : 𝕜) • J z := sub_eq_iff_eq_add.mp (hres z)
    have h1 := hEq ⟨J z, hdom z⟩
    rw [hres', map_add, map_smul] at h1
    have h2 : S (Y (J z)) - Y z = C (J z) := by
      calc S (Y (J z)) - Y z
          = S (Y (J z)) -
              (Y z + ((c : ℝ) : 𝕜) • Y (J z) -
                ((c : ℝ) : 𝕜) • Y (J z)) := by abel
        _ = C (J z) := h1
    have h3 : S (Y (J z)) = C (J z) + Y z := sub_eq_iff_eq_add.mp h2
    show Y z = (S ∘L Y ∘L J) z + (-(C ∘L J)) z
    simp only [ContinuousLinearMap.comp_apply, neg_apply]
    rw [h3]
    abel
  -- the Neumann contraction `W ↦ S W J`
  set T : (G →L[𝕜] F) → (G →L[𝕜] F) := fun W => S ∘L W ∘L J with hTdef
  have hTadd : ∀ W Z : G →L[𝕜] F, T (W + Z) = T W + T Z := by
    intro W Z
    simp only [hTdef]
    simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  have hTnorm : ∀ W : G →L[𝕜] F, ‖T W‖ ≤ q * ‖W‖ := by
    intro W
    calc ‖T W‖ ≤ ‖S‖ * ‖W‖ * ‖J‖ :=
          RectangularSymmetricIdealFamily.opNorm_comp_comp_le S W J
      _ ≤ ρ * ‖W‖ * (ρ + δ)⁻¹ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hSnorm (norm_nonneg W))
            hJnorm (norm_nonneg J) (mul_nonneg hρ (norm_nonneg W))
      _ = q * ‖W‖ := by rw [hqdef]; ring
  have hTmem : ∀ W : G →L[𝕜] F, N.Mem W → N.Mem (T W) := fun W hW =>
    N.comp_mem S J hW
  have hTgauge : ∀ W : G →L[𝕜] F, N.Mem W →
      N.gauge (T W) ≤ q * N.gauge W := by
    intro W hW
    calc N.gauge (T W) ≤ ‖S‖ * N.gauge W * ‖J‖ := N.gauge_comp_le S J hW
      _ ≤ ρ * N.gauge W * (ρ + δ)⁻¹ :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right hSnorm (N.gauge_nonneg hW))
            hJnorm (norm_nonneg J)
            (mul_nonneg hρ (N.gauge_nonneg hW))
      _ = q * N.gauge W := by rw [hqdef]; ring
  -- the Neumann iterates and their partial sums
  have hbasemem : N.Mem (-(C ∘L J)) := N.neg_mem (N.comp_right_mem J hC)
  set t : ℕ → G →L[𝕜] F := fun n => T^[n] (-(C ∘L J)) with htdef
  have ht0 : t 0 = -(C ∘L J) := rfl
  have htsucc : ∀ n, t (n + 1) = T (t n) := by
    intro n
    simp only [htdef, Function.iterate_succ_apply']
  have htmem : ∀ n, N.Mem (t n) := by
    intro n
    induction n with
    | zero => exact hbasemem
    | succ n ih => rw [htsucc]; exact hTmem _ ih
  set g₀ : ℝ := N.gauge (-(C ∘L J)) with hg₀def
  have htgauge : ∀ n, N.gauge (t n) ≤ q ^ n * g₀ := by
    intro n
    induction n with
    | zero => simp [htdef, hg₀def]
    | succ n ih =>
        rw [htsucc, pow_succ]
        calc N.gauge (T (t n)) ≤ q * N.gauge (t n) := hTgauge _ (htmem n)
          _ ≤ q * (q ^ n * g₀) := mul_le_mul_of_nonneg_left ih hq0
          _ = q ^ n * q * g₀ := by ring
  set P : ℕ → G →L[𝕜] F := fun n => ∑ k ∈ Finset.range n, t k with hPdef
  have hPmem : ∀ n, N.Mem (P n) := by
    intro n
    simp only [hPdef]
    exact N.finset_sum_mem (Finset.range n) t fun k _ => htmem k
  set Gs : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, q ^ k * g₀ with hGdef
  have hgap : ∀ {m n : ℕ}, n ≤ m → N.gauge (P m - P n) ≤ Gs m - Gs n := by
    intro m n hnm
    have hsum : P m - P n = ∑ k ∈ Finset.Ico n m, t k :=
      (Finset.sum_Ico_eq_sub _ hnm).symm
    have hG : ∑ k ∈ Finset.Ico n m, q ^ k * g₀ = Gs m - Gs n :=
      Finset.sum_Ico_eq_sub _ hnm
    rw [hsum, ← hG]
    calc N.gauge (∑ k ∈ Finset.Ico n m, t k)
        ≤ ∑ k ∈ Finset.Ico n m, N.gauge (t k) :=
          N.gauge_finset_sum_le (Finset.Ico n m) t fun k _ => htmem k
      _ ≤ ∑ k ∈ Finset.Ico n m, q ^ k * g₀ :=
          Finset.sum_le_sum fun k _ => htgauge k
  have hGcauchy : CauchySeq Gs := by
    have hsummable : Summable fun k : ℕ => q ^ k * g₀ :=
      (summable_geometric_of_lt_one hq0 hq1).mul_right g₀
    exact hsummable.hasSum.tendsto_sum_nat.cauchySeq
  have hPcauchy : ∀ ε : ℝ, 0 < ε → ∃ N₀, ∀ m n, N₀ ≤ m → N₀ ≤ n →
      N.gauge (P m - P n) < ε := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.mp hGcauchy ε hε
    refine ⟨N₀, fun m n hm hn => ?_⟩
    rcases le_total n m with h | h
    · refine lt_of_le_of_lt (hgap h) ?_
      calc Gs m - Gs n ≤ |Gs m - Gs n| := le_abs_self _
        _ = dist (Gs m) (Gs n) := (Real.dist_eq _ _).symm
        _ < ε := hN₀ m hm n hn
    · have hswap : N.gauge (P m - P n) = N.gauge (P n - P m) := by
        rw [show P m - P n = -(P n - P m) from by abel,
          N.gauge_neg (N.sub_mem (hPmem n) (hPmem m))]
      rw [hswap]
      refine lt_of_le_of_lt (hgap h) ?_
      calc Gs n - Gs m ≤ |Gs n - Gs m| := le_abs_self _
        _ = dist (Gs n) (Gs m) := (Real.dist_eq _ _).symm
        _ < ε := hN₀ n hn m hm
  obtain ⟨L, hLmem, hLlim⟩ := N.gauge_complete P hPmem hPcauchy
  -- the partial sums converge to `L` in operator norm
  have hPL : Filter.Tendsto P Filter.atTop (nhds L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => N.opNorm_le_gauge (N.sub_mem (hPmem n) hLmem)) ?_
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hLlim ε hε
    refine ⟨N₀, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (N.gauge_nonneg (N.sub_mem (hPmem n) hLmem))]
    exact hN₀ n hn
  -- the partial sums converge to `Y` in operator norm
  have hfix' : Y = t 0 + T Y := by
    conv_lhs => rw [hfix]
    rw [ht0]
    abel
  have hchain : ∀ n, T^[n] Y = t n + T^[n + 1] Y := by
    intro n
    induction n with
    | zero => simpa using hfix'
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hTadd, ← htsucc,
          ← Function.iterate_succ_apply' T (n + 1) Y]
  have hYP : ∀ n, Y = P n + T^[n] Y := by
    intro n
    induction n with
    | zero => simp [hPdef]
    | succ n ih =>
        have hPsucc : P (n + 1) = P n + t n := Finset.sum_range_succ _ _
        rw [hPsucc]
        calc Y = P n + T^[n] Y := ih
          _ = P n + (t n + T^[n + 1] Y) := by rw [hchain n]
          _ = P n + t n + T^[n + 1] Y := by abel
  have htail : ∀ n, ‖T^[n] Y‖ ≤ q ^ n * ‖Y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', pow_succ]
        calc ‖T (T^[n] Y)‖ ≤ q * ‖T^[n] Y‖ := hTnorm _
          _ ≤ q * (q ^ n * ‖Y‖) := mul_le_mul_of_nonneg_left ih hq0
          _ = q ^ n * q * ‖Y‖ := by ring
  have hPY : Filter.Tendsto P Filter.atTop (nhds Y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n, ‖P n - Y‖ ≤ q ^ n * ‖Y‖ := by
      intro n
      have hPnY : P n - Y = -(T^[n] Y) := by
        conv_lhs => rw [hYP n]
        abel
      rw [hPnY, norm_neg]
      exact htail n
    refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖Y‖
  have hYL : Y = L := tendsto_nhds_unique hPY hPL
  have hYmem : N.Mem Y := by rw [hYL]; exact hLmem
  -- the gauge estimate by absorption through the fixed point
  have hgauge : N.gauge Y ≤ (ρ + δ)⁻¹ * (ρ * N.gauge Y + N.gauge C) := by
    conv_lhs => rw [hfix]
    calc N.gauge (S ∘L Y ∘L J + -(C ∘L J))
        ≤ N.gauge (S ∘L Y ∘L J) + N.gauge (-(C ∘L J)) :=
          N.gauge_add_le (N.comp_mem S J hYmem) hbasemem
      _ ≤ ‖S‖ * N.gauge Y * ‖J‖ + N.gauge (C ∘L J) :=
          add_le_add (N.gauge_comp_le S J hYmem)
            (le_of_eq (N.gauge_neg (N.comp_right_mem J hC)))
      _ ≤ ρ * N.gauge Y * (ρ + δ)⁻¹ + N.gauge C * (ρ + δ)⁻¹ := by
          refine add_le_add
            (mul_le_mul
              (mul_le_mul_of_nonneg_right hSnorm (N.gauge_nonneg hYmem))
              hJnorm (norm_nonneg J)
              (mul_nonneg hρ (N.gauge_nonneg hYmem))) ?_
          exact (N.gauge_comp_right_le_mul J hC).trans
            (mul_le_mul_of_nonneg_left hJnorm (N.gauge_nonneg hC))
      _ = (ρ + δ)⁻¹ * (ρ * N.gauge Y + N.gauge C) := by ring
  refine ⟨hYmem, ?_⟩
  have hkey := mul_le_mul_of_nonneg_left hgauge hρδ.le
  rw [← mul_assoc, mul_inv_cancel₀ hρδ.ne', one_mul] at hkey
  linarith

/-- **The unbounded Davis--Kahan `sin Θ` theorem at unitary-invariant ideal
scope.**  For the paper-shaped `UnboundedSinThetaData` with the trial
block's quadratic form in `[β, α]` and the complementary block's shifted
resolvent bounded by `((α-β)/2 + δ)⁻¹`, if the projected residual
`R⋆ ∘ F₁` lies in the rectangular symmetric ideal family `N`, then so does
`X⋆ ∘ F₁`, with `δ · gauge (X⋆ ∘ F₁) ≤ gauge (R⋆ ∘ F₁)`. -/
theorem sinTheta_unbounded_gauge
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
    (hA : D.A.IsSelfAdjoint) (hA₀ : D.A₀.IsSelfAdjoint)
    (hΛ₁ : D.Λ₁.IsSelfAdjoint)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (hA₀low : SemiboundedBelow D.A₀ β) (hA₀high : SemiboundedAbove D.A₀ α)
    (hΛres : TwoSidedShiftedInverseBound D.Λ₁ ((α + β) / 2)
      ((α - β) / 2 + δ))
    (hC : N.Mem (D.residual.adjoint ∘L D.F₁)) :
    N.Mem (D.X.adjoint ∘L D.F₁) ∧
      δ * N.gauge (D.X.adjoint ∘L D.F₁) ≤
        N.gauge (D.residual.adjoint ∘L D.F₁) := by
  obtain ⟨S, hSnorm, hSeq⟩ :=
    exists_bounded_shift_extension hA₀.isSymmetric hβα hA₀low hA₀high
  obtain ⟨J, hdom, _hleft, hright, hJnorm⟩ := hΛres
  have hEqu := unbounded_adjoint_residual_block_identity D hA hA₀ hΛ₁
  have hρ : (0 : ℝ) ≤ (α - β) / 2 := by linarith
  have hEq' : ∀ y : D.Λ₁.domain,
      S ((D.X.adjoint ∘L D.F₁) (y : G)) -
        ((D.X.adjoint ∘L D.F₁) (D.Λ₁.toLinearMap y) -
          (((α + β) / 2 : ℝ) : 𝕜) • (D.X.adjoint ∘L D.F₁) (y : G)) =
      (-(D.residual.adjoint ∘L D.F₁)) (y : G) := by
    intro y
    have h1 := hEqu.equation y
    have h2 := hSeq ⟨(D.X.adjoint ∘L D.F₁) (y : G), hEqu.mapsTo_domain y⟩
    rw [h2]
    calc D.A₀.toLinearMap
          ⟨(D.X.adjoint ∘L D.F₁) (y : G), hEqu.mapsTo_domain y⟩ -
            (((α + β) / 2 : ℝ) : 𝕜) • (D.X.adjoint ∘L D.F₁) (y : G) -
          ((D.X.adjoint ∘L D.F₁) (D.Λ₁.toLinearMap y) -
            (((α + β) / 2 : ℝ) : 𝕜) • (D.X.adjoint ∘L D.F₁) (y : G))
        = D.A₀.toLinearMap
            ⟨(D.X.adjoint ∘L D.F₁) (y : G), hEqu.mapsTo_domain y⟩ -
          (D.X.adjoint ∘L D.F₁) (D.Λ₁.toLinearMap y) := by abel
      _ = (-(D.residual.adjoint ∘L D.F₁)) (y : G) := h1
  have hmain := mem_and_gauge_le_of_boundedLeft_exteriorRight N hρ hδ
    hSnorm hdom hright hJnorm hEq' (N.neg_mem hC)
  refine ⟨hmain.1, ?_⟩
  have hgC : N.gauge (-(D.residual.adjoint ∘L D.F₁)) =
      N.gauge (D.residual.adjoint ∘L D.F₁) := N.gauge_neg hC
  calc δ * N.gauge (D.X.adjoint ∘L D.F₁)
      ≤ N.gauge (-(D.residual.adjoint ∘L D.F₁)) := hmain.2
    _ = N.gauge (D.residual.adjoint ∘L D.F₁) := hgC

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
