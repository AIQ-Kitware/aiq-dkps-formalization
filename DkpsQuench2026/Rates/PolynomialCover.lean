/-
Polynomial finite covers for compact finite-dimensional perspective ranges.

This module is deliberately below the rest of `DkpsQuench2026.QueryEfficiency`: it depends
only on the core coverage definitions, so the polynomial-cover theorem can be
compiled and reviewed independently of response and spectral regularity.
-/

import DkpsQuench2026.Probability.Coverage

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench2026

universe u v

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]

/-- Compactness of the perspective range supplies a nonnegative uniform norm
bound.  Kept private because the public copy already lives in the spectral
regularity layer; this lower module must not depend on that layer. -/
private theorem exists_perspective_norm_bound_for_polynomial_cover
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ)) :
    ∃ B : Real, 0 ≤ B ∧ ∀ f, ‖ψ f‖ ≤ B := by
  obtain ⟨r, hr⟩ := hcompact.isBounded.subset_closedBall 0
  refine ⟨max 0 r, le_max_left _ _, fun f => ?_⟩
  have hmem : ψ f ∈ Metric.closedBall (0 : Vec d) r := hr ⟨f, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
  exact hmem.trans (le_max_right _ _)

/-- Polynomial finite covers for a compact subset of finite-dimensional
Euclidean space, with centers pulled back to models.

The proof quantizes the bounded compact range into occupied coordinate cells
and chooses one model from each occupied cell.  The important conclusion is the
exponent `d`; the constant is existential and may absorb the diameter of the
compact range.

The `max 1 ρ⁻¹` form handles large radii and avoids separate early-stage cases.
-/
theorem exists_polynomial_perspective_covers_of_isCompact_range
    {d : Nat}
    (ψ : Model Q X → Vec d)
    (hcompact : IsCompact (Set.range ψ)) :
    ∃ C : Real, 0 ≤ C ∧ ∀ ρ : Real, 0 < ρ →
      ∃ centers : Finset (Model Q X),
        PerspectiveFiniteCover ψ ρ centers ∧
        ((centers.card : Nat) : Real) ≤ C * (max 1 ρ⁻¹) ^ d := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨1, zero_le_one, fun ρ hρ => ?_⟩
    by_cases hmodel : Nonempty (Model Q X)
    · let f0 : Model Q X := Classical.choice hmodel
      refine ⟨{f0}, ?_, by simp⟩
      intro f
      refine ⟨f0, by simp, ?_⟩
      have hψ : ψ f0 = ψ f := Subsingleton.elim _ _
      simp [hψ, hρ]
    · let : IsEmpty (Model Q X) := ⟨fun f => hmodel ⟨f⟩⟩
      refine ⟨∅, ?_, by simp⟩
      intro f
      exact isEmptyElim f
  · obtain ⟨B, hB0, hB⟩ :=
      exists_perspective_norm_bound_for_polynomial_cover ψ hcompact
    let D : Real := (d : Real) + 1
    let A : Real := 2 * B * D + 2
    have hDpos : 0 < D := by
      dsimp [D]
      positivity
    have hA0 : 0 ≤ A := by
      dsimp [A]
      positivity
    refine ⟨A ^ d, pow_nonneg hA0 d, ?_⟩
    intro ρ hρ
    let δ : Real := ρ / D
    have hδ : 0 < δ := div_pos hρ hDpos
    let scale : Real := 2 * B * D * ρ⁻¹
    let N : Nat := ⌈scale⌉₊
    let key : Model Q X → Fin d → Nat := fun f i =>
      ⌊(ψ f i + B) / δ⌋₊
    let keys : Finset (Fin d → Nat) :=
      Finset.Icc 0 (fun _ => N)
    have hcoord_abs (f : Model Q X) (i : Fin d) : |ψ f i| ≤ B := by
      calc
        |ψ f i| = ‖ψ f i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ψ f‖ := PiLp.norm_apply_le (ψ f) i
        _ ≤ B := hB f
    have hscaled_upper : 2 * B / δ = scale := by
      dsimp [δ, scale]
      field_simp [ne_of_gt hρ, ne_of_gt hDpos]
    have hkey_mem (f : Model Q X) : key f ∈ keys := by
      apply Finset.mem_Icc.mpr
      constructor
      · intro i
        exact Nat.zero_le _
      · intro i
        have hxi_lower : -B ≤ ψ f i := (abs_le.mp (hcoord_abs f i)).1
        have hxi_upper : ψ f i ≤ B := (abs_le.mp (hcoord_abs f i)).2
        have hnum0 : 0 ≤ ψ f i + B := by linarith
        have hnum_le : ψ f i + B ≤ 2 * B := by linarith
        have hy0 : 0 ≤ (ψ f i + B) / δ := div_nonneg hnum0 hδ.le
        have hy_le : (ψ f i + B) / δ ≤ scale := by
          rw [← hscaled_upper]
          exact (div_le_div_iff_of_pos_right hδ).mpr hnum_le
        have hscale_ceil : scale ≤ (N : Real) := by
          dsimp [N]
          exact Nat.le_ceil scale
        dsimp [key]
        exact Nat.floor_le_of_le (hy_le.trans hscale_ceil)
    let occupied : Finset (Fin d → Nat) :=
      keys.filter (fun k => ∃ f, key f = k)
    have hoccupied_witness :
        ∀ k : {k // k ∈ occupied}, ∃ f : Model Q X, key f = k.1 := by
      intro k
      exact (Finset.mem_filter.mp k.2).2
    choose rep hrep using hoccupied_witness
    let centers : Finset (Model Q X) := occupied.attach.image rep
    refine ⟨centers, ?_, ?_⟩
    · intro f
      have hkocc : key f ∈ occupied := by
        exact Finset.mem_filter.mpr ⟨hkey_mem f, ⟨f, rfl⟩⟩
      let k : {k // k ∈ occupied} := ⟨key f, hkocc⟩
      refine ⟨rep k, ?_, ?_⟩
      · dsimp [centers]
        exact Finset.mem_image.mpr ⟨k, by simp [k], rfl⟩
      · have hkey_eq : key (rep k) = key f := by
          simpa [k] using hrep k
        have hcoord (i : Fin d) : |(ψ (rep k) - ψ f) i| < δ := by
          have hfloor :
              ⌊(ψ (rep k) i + B) / δ⌋₊ =
                ⌊(ψ f i + B) / δ⌋₊ := by
            simpa [key] using congrFun hkey_eq i
          have hg_lower : -B ≤ ψ (rep k) i :=
            (abs_le.mp (hcoord_abs (rep k) i)).1
          have hf_lower : -B ≤ ψ f i := (abs_le.mp (hcoord_abs f i)).1
          have hyg0 : 0 ≤ (ψ (rep k) i + B) / δ := by
            exact div_nonneg (by linarith) hδ.le
          have hyf0 : 0 ≤ (ψ f i + B) / δ := by
            exact div_nonneg (by linarith) hδ.le
          have hg_floor_le :
              (⌊(ψ (rep k) i + B) / δ⌋₊ : Real) ≤
                (ψ (rep k) i + B) / δ := Nat.floor_le hyg0
          have hf_floor_le :
              (⌊(ψ f i + B) / δ⌋₊ : Real) ≤
                (ψ f i + B) / δ := Nat.floor_le hyf0
          have hg_lt :
              (ψ (rep k) i + B) / δ <
                (⌊(ψ (rep k) i + B) / δ⌋₊ : Real) + 1 :=
            Nat.lt_floor_add_one _
          have hf_lt :
              (ψ f i + B) / δ <
                (⌊(ψ f i + B) / δ⌋₊ : Real) + 1 :=
            Nat.lt_floor_add_one _
          have habs_scaled :
              |(ψ (rep k) i + B) / δ - (ψ f i + B) / δ| < 1 := by
            rw [abs_lt]
            constructor
            · rw [hfloor] at hg_floor_le
              linarith
            · rw [hfloor] at hg_lt
              linarith
          have habs_div : |(ψ (rep k) i - ψ f i) / δ| < 1 := by
            convert habs_scaled using 1
            ring
          rw [abs_div, abs_of_pos hδ] at habs_div
          have := (div_lt_iff₀ hδ).mp habs_div
          simpa using this
        have hsum_le :
            ∑ i : Fin d, ((ψ (rep k) - ψ f) i) ^ 2 ≤
              (d : Real) * δ ^ 2 := by
          calc
            ∑ i : Fin d, ((ψ (rep k) - ψ f) i) ^ 2
                ≤ ∑ _i : Fin d, δ ^ 2 := by
                  apply Finset.sum_le_sum
                  intro i _hi
                  have hi := hcoord i
                  nlinarith [abs_nonneg ((ψ (rep k) - ψ f) i),
                    sq_nonneg ((ψ (rep k) - ψ f) i),
                    sq_nonneg (|(ψ (rep k) - ψ f) i|),
                    sq_abs ((ψ (rep k) - ψ f) i)]
            _ = (d : Real) * δ ^ 2 := by simp
        have hd0 : 0 ≤ (d : Real) := Nat.cast_nonneg d
        have hcoef : (d : Real) < D ^ 2 := by
          dsimp [D]
          nlinarith [sq_nonneg (d : Real)]
        have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
        have hdim : (d : Real) * δ ^ 2 < D ^ 2 * δ ^ 2 :=
          mul_lt_mul_of_pos_right hcoef hδsq
        have hρ_eq : ρ = D * δ := by
          dsimp [δ]
          field_simp [ne_of_gt hDpos]
        have hnorm_sq : ‖ψ (rep k) - ψ f‖ ^ 2 < ρ ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          calc
            ∑ i : Fin d, ((ψ (rep k) - ψ f) i) ^ 2
                ≤ (d : Real) * δ ^ 2 := hsum_le
            _ < D ^ 2 * δ ^ 2 := hdim
            _ = ρ ^ 2 := by rw [hρ_eq]; ring
        nlinarith [norm_nonneg (ψ (rep k) - ψ f)]
    · have hcenters_card : centers.card ≤ occupied.card := by
        dsimp [centers]
        simpa using (Finset.card_image_le :
          (occupied.attach.image rep).card ≤ occupied.attach.card)
      have hoccupied_card : occupied.card ≤ keys.card := by
        dsimp [occupied]
        exact Finset.card_filter_le _ _
      have hkeys_card : keys.card = (N + 1) ^ d := by
        dsimp [keys]
        rw [Pi.card_Icc]
        simp
      have hcard_nat : centers.card ≤ (N + 1) ^ d := by
        calc
          centers.card ≤ occupied.card := hcenters_card
          _ ≤ keys.card := hoccupied_card
          _ = (N + 1) ^ d := hkeys_card
      have hscale_nonneg : 0 ≤ scale := by
        dsimp [scale]
        positivity
      have hceil : (N : Real) < scale + 1 := by
        dsimp [N]
        exact Nat.ceil_lt_add_one hscale_nonneg
      have hscale0 : 0 ≤ 2 * B * D := by positivity
      have hbase : ((N + 1 : Nat) : Real) ≤ A * max 1 ρ⁻¹ := by
        have hmul : 2 * B * D * ρ⁻¹ ≤ 2 * B * D * max 1 ρ⁻¹ :=
          mul_le_mul_of_nonneg_left (le_max_right 1 ρ⁻¹) hscale0
        have htwo : (2 : Real) ≤ 2 * max 1 ρ⁻¹ := by
          nlinarith [le_max_left (1 : Real) ρ⁻¹]
        dsimp [scale, A] at hceil ⊢
        calc
          ((N + 1 : Nat) : Real) = (N : Real) + 1 := by norm_num
          _ ≤ 2 * B * D * ρ⁻¹ + 2 := by linarith
          _ ≤ 2 * B * D * max 1 ρ⁻¹ + 2 * max 1 ρ⁻¹ :=
            add_le_add hmul htwo
          _ = (2 * B * D + 2) * max 1 ρ⁻¹ := by ring
      calc
        ((centers.card : Nat) : Real)
            ≤ (((N + 1) ^ d : Nat) : Real) := by exact_mod_cast hcard_nat
        _ = (((N + 1 : Nat) : Real) ^ d) := by norm_num
        _ ≤ (A * max 1 ρ⁻¹) ^ d := by
          exact pow_le_pow_left₀ (by positivity) hbase d
        _ = A ^ d * (max 1 ρ⁻¹) ^ d := by rw [mul_pow]
end DkpsQuench2026
