/-
VENDORED SOURCE EXCERPT -- NOT PART OF THE PROJECT BUILD.

Original work:
  Dronmong, `DriftingIdentifiability/FiniteStability.lean`
  https://github.com/Dronmong/drifting-identifiability
  commit 06c699d07c2fa186ba8e708597ccdb9b8ba1c04f
  blob dc984c30c7cb4b7059bf16df31209658dfb8c6e3
  source lines 36-165
  MIT License, Copyright (c) 2026 Dronmong

Local change: this provenance wrapper was added. The source excerpt below is
otherwise copied verbatim. It depends on declarations and imports from the original project.
-/

/-- Coefficient minors restricted to the independent strict-pair index set. -/
def strictMinorVector (a b : Fin m → ℝ) (p : StrictPair m) : ℝ :=
  coefficientMinor a b p.1.1 p.1.2

/-- Linear synthesis by the strict-pair interaction vectors. -/
def interactionSynthesis (U : Fin m → Fin m → V) :
    (StrictPair m → ℝ) →ₗ[ℝ] V where
  toFun z := ∑ p, z p • U p.1.1 p.1.2
  map_add' z w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r z := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_smul, Finset.smul_sum,
      smul_eq_mul]

@[simp]
theorem interactionSynthesis_apply (U : Fin m → Fin m → V)
    (z : StrictPair m → ℝ) :
    interactionSynthesis U z = ∑ p, z p • U p.1.1 p.1.2 := rfl

/-- A quantitative and numerically testable replacement for bare linear
independence. `c` is a lower frame bound in the coefficient `ℓ¹` norm. -/
def InteractionFrameBound (U : Fin m → Fin m → V) (c : ℝ) : Prop :=
  0 < c ∧ ∀ z : StrictPair m → ℝ,
    c * (∑ p, |z p|) ≤ ‖interactionSynthesis U z‖

/-- Deterministic squared energy of the finite probe-drift vector.  This is the
population/probe quantity that a finite sampled objective should estimate. -/
def probeDriftEnergy {N : ℕ} (v : Fin N → V) : ℝ :=
  ∑ n, ‖v n‖ ^ 2

omit [NormedSpace ℝ V] in
theorem probeDriftEnergy_nonnegative {N : ℕ} (v : Fin N → V) :
    0 ≤ probeDriftEnergy v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [NormedSpace ℝ V] in
/-- Zero finite probe energy is exactly componentwise zero at every probe; no
support or continuity assumption is needed. -/
theorem probeDriftEnergy_eq_zero_iff {N : ℕ} (v : Fin N → V) :
    probeDriftEnergy v = 0 ↔ ∀ n, v n = 0 := by
  constructor
  · intro h n
    have hn : ‖v n‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).mp h
        n (Finset.mem_univ n)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  · intro h
    simp [probeDriftEnergy, h]

omit [NormedSpace ℝ V] in
/-- The sup norm of the finite probe vector is controlled by the square root
of its summed squared energy. -/
theorem norm_le_sqrt_probeDriftEnergy {N : ℕ} (v : Fin N → V) :
    ‖v‖ ≤ Real.sqrt (probeDriftEnergy v) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro n
  rw [← Real.sqrt_sq (norm_nonneg (v n))]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun i _ => sq_nonneg ‖v i‖) (Finset.mem_univ n)

/-- A positive frame bound implies qualitative linear independence. -/
theorem interactionFrameBound_linearIndependent
    (U : Fin m → Fin m → V) {c : ℝ} (hframe : InteractionFrameBound U c) :
    LinearIndependent ℝ (fun p : StrictPair m => U p.1.1 p.1.2) := by
  rw [Fintype.linearIndependent_iff]
  intro z hz p
  have hbound := hframe.2 z
  rw [interactionSynthesis_apply, hz, norm_zero] at hbound
  have hmass : (∑ q, |z q|) = 0 := by
    have hnonneg : 0 ≤ ∑ q, |z q| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    nlinarith [hframe.1]
  have hp : |z p| = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => abs_nonneg (z q))).mp hmass p
      (Finset.mem_univ p)
  exact abs_eq_zero.mp hp

/-- In finite dimension, qualitative nondegeneracy also yields some positive
frame constant.  This is an existence theorem; practical stability still
requires estimating a useful value of the constant. -/
theorem interactionFrameBound_of_linearIndependent
    [Nonempty (StrictPair m)] (U : Fin m → Fin m → V)
    (hindep : LinearIndependent ℝ (fun p : StrictPair m => U p.1.1 p.1.2)) :
    ∃ c > 0, InteractionFrameBound U c := by
  have hker : LinearMap.ker (interactionSynthesis U) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro z hz
    rw [interactionSynthesis_apply] at hz
    funext p
    exact (Fintype.linearIndependent_iff.mp hindep) z hz p
  obtain ⟨K, hKpos, hanti⟩ :=
    LinearMap.exists_antilipschitzWith (interactionSynthesis U) hker
  have hbound : ∀ z : StrictPair m → ℝ,
      ‖z‖ ≤ (K : ℝ) * ‖interactionSynthesis U z‖ := by
    intro z
    have h := hanti.le_mul_dist z 0
    rwa [dist_zero_right, map_zero, dist_zero_right] at h
  have hNpos : (0 : ℝ) < (Fintype.card (StrictPair m) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hKR : (0 : ℝ) < (K : ℝ) := hKpos
  have hprod : (0 : ℝ) < (K : ℝ) * Fintype.card (StrictPair m) :=
    mul_pos hKR hNpos
  refine ⟨((K : ℝ) * Fintype.card (StrictPair m))⁻¹,
    by positivity, by positivity, fun z => ?_⟩
  have hsum : (∑ p, |z p|) ≤
      (Fintype.card (StrictPair m) : ℝ) * ‖z‖ := by
    calc
      (∑ p : StrictPair m, |z p|) ≤ ∑ _p : StrictPair m, ‖z‖ := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm z p
      _ = (Fintype.card (StrictPair m) : ℝ) * ‖z‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hchain : (∑ p, |z p|) ≤
      (K : ℝ) * Fintype.card (StrictPair m) * ‖interactionSynthesis U z‖ :=
    calc
      (∑ p, |z p|) ≤ (Fintype.card (StrictPair m) : ℝ) * ‖z‖ := hsum
      _ ≤ (Fintype.card (StrictPair m) : ℝ) *
          ((K : ℝ) * ‖interactionSynthesis U z‖) :=
        mul_le_mul_of_nonneg_left (hbound z) hNpos.le
      _ = (K : ℝ) * Fintype.card (StrictPair m) *
          ‖interactionSynthesis U z‖ := by ring
  calc
    ((K : ℝ) * Fintype.card (StrictPair m))⁻¹ * (∑ p, |z p|)
        ≤ ((K : ℝ) * Fintype.card (StrictPair m))⁻¹ *
            ((K : ℝ) * Fintype.card (StrictPair m) *
              ‖interactionSynthesis U z‖) :=
          mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = ‖interactionSynthesis U z‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hprod), one_mul]
