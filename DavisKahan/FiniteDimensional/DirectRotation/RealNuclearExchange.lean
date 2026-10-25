/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6.1 Sol
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealNuclearMatching

/-!
# Nuclear pair exchange, with exact strictness

The closed nuclear pair weight is submodular on the full angle square.
Its rectangular inequality is strict precisely when both coordinate
intervals have positive length. Sum-to-product identities reduce the
comparison to monotonicity of cosine. Adjacent pairing beats either
alternative on four ordered angles. This supplies the scalar exchange
step, not yet the finite matching induction for the two sorted sums.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

private theorem nuclear_pair_sum (a b c d : ℝ) :
    realNuclearPairWeight a b + realNuclearPairWeight c d =
      8 * Real.sin ((a+b+c+d)/4) * Real.cos ((a+b-c-d)/4) := by
  unfold realNuclearPairWeight
  rw [← mul_add, Real.sin_add_sin]
  rw [show ((a+b)/2+(c+d)/2)/2 = (a+b+c+d)/4 by ring,
    show ((a+b)/2-(c+d)/2)/2 = (a+b-c-d)/4 by ring]
  ring

/-- Nuclear pair submodularity is strict on every nondegenerate rectangle,
including rectangles touching zero or the right-angle boundary. -/
theorem realNuclearPairWeight_strict_submodular
    (a A b B : ℝ) (ha : 0 ≤ a) (haA : a < A) (hA : A ≤ Real.pi/2)
    (hb : 0 ≤ b) (hbB : b < B) (hB : B ≤ Real.pi/2) :
    realNuclearPairWeight A B + realNuclearPairWeight a b <
      realNuclearPairWeight A b + realNuclearPairWeight a B := by
  let s := (A+B+a+b)/4
  let d := (A+B-a-b)/4
  let e := (A+b-a-B)/4
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hsPi : s < Real.pi := by dsimp [s]; linarith [Real.pi_pos]
  have hdPi : d ≤ Real.pi := by dsimp [d]; linarith [Real.pi_pos]
  have hed : |e| < d := by
    apply abs_lt.mpr
    constructor <;> dsimp [e, d] <;> linarith
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg e) hdPi hed
  rw [Real.cos_abs] at hcos
  have hmul := mul_lt_mul_of_pos_left hcos
    (show 0 < 8 * Real.sin s by positivity [Real.sin_pos_of_pos_of_lt_pi hs0 hsPi])
  rw [nuclear_pair_sum A B a b, nuclear_pair_sum A b a B,
    show (A+b+a+B)/4 = (A+B+a+b)/4 by ring]
  exact hmul

/-- Nuclear pair submodularity on the entire closed principal-angle square. -/
theorem realNuclearPairWeight_submodular
    (a A b B : ℝ) (ha : 0 ≤ a) (haA : a ≤ A) (hA : A ≤ Real.pi/2)
    (hb : 0 ≤ b) (hbB : b ≤ B) (hB : B ≤ Real.pi/2) :
    realNuclearPairWeight A B + realNuclearPairWeight a b ≤
      realNuclearPairWeight A b + realNuclearPairWeight a B := by
  rcases haA.eq_or_lt with rfl | haA
  · exact le_of_eq (add_comm _ _)
  rcases hbB.eq_or_lt with rfl | hbB
  · exact le_rfl
  exact (realNuclearPairWeight_strict_submodular a A b B ha haA hA hb hbB hB).le

/-- The exact strictness classification for nuclear rectangular exchange. -/
theorem realNuclearPairWeight_strict_submodular_iff
    (a A b B : ℝ) (ha : 0 ≤ a) (haA : a ≤ A) (hA : A ≤ Real.pi/2)
    (hb : 0 ≤ b) (hbB : b ≤ B) (hB : B ≤ Real.pi/2) :
    (realNuclearPairWeight A B + realNuclearPairWeight a b <
      realNuclearPairWeight A b + realNuclearPairWeight a B) ↔ a < A ∧ b < B := by
  constructor
  · intro hlt
    constructor
    · apply lt_of_le_of_ne haA
      intro heq
      subst A
      simp [add_comm] at hlt
    · apply lt_of_le_of_ne hbB
      intro heq
      subst B
      exact (lt_irrefl _) hlt
  · rintro ⟨haA, hbB⟩
    exact realNuclearPairWeight_strict_submodular a A b B ha haA hA hb hbB hB

/-- On four ordered angles, adjacent pairing costs no more than either
other perfect pairing. This includes equal, zero and right angles. -/
theorem realNuclearPairWeight_adjacent_exchange
    (a b c d : ℝ) (hd : 0 ≤ d) (hdc : d ≤ c) (hcb : c ≤ b)
    (hba : b ≤ a) (ha : a ≤ Real.pi/2) :
    realNuclearPairWeight a b + realNuclearPairWeight c d ≤
      min (realNuclearPairWeight a c + realNuclearPairWeight b d)
        (realNuclearPairWeight a d + realNuclearPairWeight b c) := by
  apply le_min
  · have h := realNuclearPairWeight_submodular d a c b hd (hdc.trans (hcb.trans hba))
      ha (hd.trans hdc) hcb (hba.trans ha)
    simpa only [realNuclearPairWeight_comm d c, realNuclearPairWeight_comm d b] using h
  · have h := realNuclearPairWeight_submodular c a d b (hd.trans hdc) (hcb.trans hba)
      ha hd (hdc.trans hcb) (hba.trans ha)
    simpa only [realNuclearPairWeight_comm c b] using h

/-- Coupling any two strictly positive nuclear angles strictly improves
their canonical rotations. No small-angle or acuteness assumption is needed. -/
theorem realNuclearPairWeight_lt_canonical_sum
    (theta psi : ℝ) (htheta : 0 < theta) (hpsi : 0 < psi)
    (hthetaPi : theta ≤ Real.pi/2) (hpsiPi : psi ≤ Real.pi/2) :
    realNuclearPairWeight theta psi <
      4 * Real.sin (theta/2) + 4 * Real.sin (psi/2) := by
  have h := realNuclearPairWeight_strict_submodular 0 theta 0 psi le_rfl htheta hthetaPi
    le_rfl hpsi hpsiPi
  simpa only [realNuclearPairWeight, add_zero, zero_add, zero_div, Real.sin_zero,
    mul_zero] using h

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
