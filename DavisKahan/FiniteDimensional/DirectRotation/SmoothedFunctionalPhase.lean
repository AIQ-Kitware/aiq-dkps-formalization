/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedNuclearAttainment
public import ForTauCeti.Analysis.InnerProductSpace.SpectralTrace
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# An explicit functional-calculus phase correction

The attaining phase factor is a scalar spectral function of the positive
cosine operator. It can therefore be specified without choosing principal
planes or eigenvectors. The existence of a paired eigenbasis is used only
to certify its cost.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The positive-branch optimal phase as a spectral function of a principal
cosine. On the spectrum `[0,1]`, its real part clips `(a/b)c` at one. -/
@[expose]
def weightedPhaseSymbol (a b : ℝ) (z : ℂ) : ℂ :=
  circlePhase 1 (optimalWeightedPhase a b (Real.arccos z.re))

/-- On a principal cosine, the optimal phase is obtained by clipping the
amplified cosine at one and taking the positive unit-circle completion.
This expression needs no inverse trigonometric function. -/
theorem weightedPhaseSymbol_eq_clip (a b c : ℝ) (hb : 0 < b) (ha : 0 ≤ a)
    (hc : c ∈ Set.Icc 0 1) :
    weightedPhaseSymbol a b (c : ℂ) =
      (min 1 (a * c / b) : ℝ) + Real.sqrt (1 - (min 1 (a * c / b)) ^ 2) * Complex.I := by
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos (by linarith [hc.1]) hc.2
  rw [weightedPhaseSymbol, Complex.ofReal_re, optimalWeightedPhase, hcos]
  by_cases hsub : b ≤ a * c
  · rw [ite_eq_left hsub, min_eq_left ((le_div_iff₀ hb).mpr (by simpa using hsub))]
    simp [circlePhase]
  · have hratio : a * c / b ≤ 1 := (div_le_one hb).mpr (le_of_not_ge hsub)
    have hratio0 : 0 ≤ a * c / b := div_nonneg (mul_nonneg ha hc.1) hb.le
    rw [ite_eq_right hsub, min_eq_right hratio]
    simp only [circlePhase, Complex.ofReal_one, one_mul, Complex.exp_ofReal_mul_I,
      Real.cos_arccos (by linarith : -1 ≤ a * c / b) hratio, Real.sin_arccos]

/-- An explicit phase factor determined entirely by the cosine operator. -/
@[expose]
def weightedPhaseFactor (a b : ℝ) (C : E →L[ℂ] E) : E →L[ℂ] E :=
  cfc (weightedPhaseSymbol a b) C

/-- The real part prescribed for every optimal phase factor: the
amplified principal cosine, clipped at one. -/
@[expose]
def clippedWeightedCosine (a b : ℝ) (C : E →L[ℂ] E) : E →L[ℂ] E :=
  cfc (fun z : ℂ => ((min 1 (a * z.re / b) : ℝ) : ℂ)) C

/-- The clipped cosine acts by the clipped scalar on every real cosine
eigenvector. Finite spectral calculus permits arbitrary multiplicities. -/
theorem clippedWeightedCosine_apply_of_apply_eq_smul_complex
    (a b c : ℝ) (C : E →L[ℂ] E) [IsStarNormal C] (x : E)
    (hx : C x = (c : ℂ) • x) :
    clippedWeightedCosine a b C x = ((min 1 (a * c / b) : ℝ) : ℂ) • x := by
  rw [clippedWeightedCosine,
    ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal _ hx]
  simp only [Complex.ofReal_re]

/-- The spectral phase factor is unitary for every finite normal operator;
the symbol has modulus one even away from the principal-cosine interval. -/
theorem weightedPhaseFactor_mem_unitary (a b : ℝ) (C : E →L[ℂ] E)
    (hC : IsStarNormal C) : weightedPhaseFactor a b C ∈ unitary (E →L[ℂ] E) := by
  apply (cfc_unitary_iff (weightedPhaseSymbol a b) C hC
    ((C.finite_spectrum ℂ).continuousOn _)).mpr
  intro z _
  change conj (circlePhase 1 _) * circlePhase 1 _ = 1
  rw [RCLike.conj_mul, norm_circlePhase 1 _ zero_le_one]
  norm_num

/-- The explicit phase factor has the prescribed action on a cosine
eigenvector with angle between zero and pi. -/
theorem weightedPhaseFactor_apply_cos (a b theta : ℝ)
    (C : E →L[ℂ] E) [IsStarNormal C] (x : E)
    (hθ : theta ∈ Set.Icc 0 Real.pi)
    (hx : C x = (Real.cos theta : ℂ) • x) :
    weightedPhaseFactor a b C x =
      circlePhase 1 (optimalWeightedPhase a b theta) • x := by
  rw [weightedPhaseFactor, ContinuousLinearMap.cfc_apply_of_apply_eq_smul_of_isStarNormal
    (weightedPhaseSymbol a b) hx]
  simp only [weightedPhaseSymbol, Complex.ofReal_re, Real.arccos_cos hθ.1 hθ.2]

/-- Every eigenvector at cosine one is fixed by the phase factor. -/
theorem weightedPhaseFactor_apply_one (a b : ℝ) (hab : b ≤ a)
    (C : E →L[ℂ] E) [IsStarNormal C] (x : E) (hx : C x = x) :
    weightedPhaseFactor a b C x = x := by
  have h := weightedPhaseFactor_apply_cos a b 0 C x
    ⟨le_rfl, Real.pi_pos.le⟩ (by simpa using hx)
  simpa [optimalWeightedPhase, hab, circlePhase] using h

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- In any paired rotation eigenbasis, the explicitly defined spectral
factor attains the weighted nuclear certificate. The formula itself does
not depend on that basis. -/
theorem weightedPhaseFactor_attains_weightedNuclear
    (a b : ℝ) (hb : 0 < b) (hab : b < a) (theta : ι → ℝ)
    (hθ : ∀ i, theta i ∈ Set.Icc 0 (Real.pi / 2))
    (e : OrthonormalBasis ((Fin 2 × ι) ⊕ κ) ℂ E)
    (C : E →L[ℂ] E) [IsStarNormal C]
    (hCp : ∀ r i, C (e (.inl (r, i))) =
      (Real.cos (theta i) : ℂ) • e (.inl (r, i)))
    (hCf : ∀ j, C (e (.inr j)) = e (.inr j))
    (A : E →ₗ[ℂ] E)
    (hA0 : ∀ i, A (e (.inl (0, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) + (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (0, i)))
    (hA1 : ∀ i, A (e (.inl (1, i))) =
      (((a * Real.cos (theta i) : ℝ) : ℂ) - (a * Real.sin (theta i)) * Complex.I) •
        e (.inl (1, i)))
    (hAf : ∀ j, A (e (.inr j)) = (a : ℂ) • e (.inr j)) :
    UnitarilyInvariantSeminorm.nuclear ℂ E E
        (A - (b : ℂ) • (weightedPhaseFactor a b C).toLinearMap) =
      (∑ i, weightedPhaseMinimum a b (theta i)) + Fintype.card κ * (a - b) := by
  obtain ⟨Z, hZp, hZf, hcost⟩ :=
    exists_unitary_attaining_weightedNuclear a b hb hab theta hθ e A hA0 hA1 hAf
  have heq : (weightedPhaseFactor a b C).toLinearMap = Z.toLinearMap := by
    apply e.toBasis.ext
    intro j
    rcases j with ⟨r, i⟩ | j
    · change weightedPhaseFactor a b C (e (.inl (r, i))) = Z (e (.inl (r, i)))
      rw [hZp]
      exact weightedPhaseFactor_apply_cos a b _ C _
        ⟨(hθ i).1, (hθ i).2.trans (by linarith [Real.pi_pos])⟩ (hCp r i)
    · change weightedPhaseFactor a b C (e (.inr j)) = Z (e (.inr j))
      rw [hZf]
      exact weightedPhaseFactor_apply_one a b hab.le C _ (hCf j)
  rw [heq]
  exact hcost

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
