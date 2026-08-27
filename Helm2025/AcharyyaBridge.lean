/-
Deterministic bridges from the Acharyya DKPS concentration scaffolds to the
Helm et al. 2025 alignment-consistency interface.

The probability/convergence bridge still needs measurability and fixed-measure
bookkeeping.  This file isolates the theorem that does not need those analytic
assumptions: Acharyya-style finite configuration error controls Helm's finite
sample `iSup` alignment error.
-/

import Acharyya2025.Bridge
import Acharyya2025.AlignedPipeline
import Acharyya2025.GramRealization
import Acharyya2025.RateChain
import Helm2025.Basic
import ForTauCeti.Probability.RigidAlignment

open scoped BigOperators Topology
open Filter MeasureTheory

namespace Helm2025.DKPS.AcharyyaBridge

open Acharyya2024

variable {Ω : Type} [MeasurableSpace Ω]

/--
Acharyya finite-configuration error controls Helm's samplewise alignment error
for the identity alignment.

This is the deterministic core needed before upgrading an Acharyya-style
high-probability configuration bound into Helm's `DKPSAlignmentConsistency`.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_iSup_le_configError
    {n d d' : Nat}
    (ψhat : (Sample n d d') → Fin (n + 1) → E d)
    (ω : Sample n d d') :
    (⨆ i : Fin (n + 1), dist (ψhat ω i) ((ω i).1))
      ≤ ConfigError (ψhat ω) (fun i : Fin (n + 1) => (ω i).1) := by
  exact ciSup_le fun i => by
    simpa [dist_eq_norm] using
      norm_config_le_ConfigError (ψhat ω) (fun i : Fin (n + 1) => (ω i).1) i

/--
The finite-sample Helm alignment error is nonnegative.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_iSup_nonneg
    {n d d' : Nat}
    (ψhat : (Sample n d d') → Fin (n + 1) → E d)
    (ω : Sample n d d') :
    0 ≤ (⨆ i : Fin (n + 1), dist (ψhat ω i) ((ω i).1)) := by
  have hle :
      dist (ψhat ω (Fin.last n)) ((ω (Fin.last n)).1)
        ≤ (⨆ i : Fin (n + 1), dist (ψhat ω i) ((ω i).1)) :=
    le_ciSup
      (Finite.bddAbove_range
        (fun i : Fin (n + 1) => dist (ψhat ω i) ((ω i).1)))
      (Fin.last n)
  exact dist_nonneg.trans hle

/--
Event-level bridge from an Acharyya-style configuration-error event to Helm's
sample-alignment-error event.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_event_of_configError_event
    {n d d' : Nat}
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    (u : Nat) :
    {ω : Sample n d d' |
      ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u}
      ⊆
    {ω : Sample n d d' |
      (⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1)) ≤ rate u} := by
  intro ω hω
  exact (sample_alignment_iSup_le_configError (ψhat u) ω).trans hω

/--
Event-level bridge from an Acharyya-style configuration-error event to the
absolute-value event used by Helm's convergence-in-probability definition.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_abs_event_of_configError_event
    {n d d' : Nat}
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    (u : Nat) :
    {ω : Sample n d d' |
      ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u}
      ⊆
    {ω : Sample n d d' |
      |(⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))| ≤ rate u} := by
  intro ω hω
  change |(⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))| ≤ rate u
  rw [abs_of_nonneg (sample_alignment_iSup_nonneg (ψhat u) ω)]
  exact (sample_alignment_iSup_le_configError (ψhat u) ω).trans hω

/--
High-probability event bridge from Acharyya-style finite configuration
concentration to Helm-style finite sample alignment-error concentration.

This deliberately stays at the high-probability event layer.  The next formal
bridge to `DKPSAlignmentConsistency` should add the fixed product measure,
measurability, and `rate → 0` assumptions needed to turn these events into
convergence in probability.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem highProb_sample_alignment_of_configError
    {n d d' : Nat}
    (P : Nat → Measure (Sample n d d'))
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    (hconfig :
      HighProbAtTop P
        (fun u =>
          {ω : Sample n d d' |
            ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u})) :
    HighProbAtTop P
      (fun u =>
        {ω : Sample n d d' |
          (⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1)) ≤ rate u}) := by
  exact HighProbAtTop.mono hconfig
    (fun u => sample_alignment_event_of_configError_event ψhat rate u)

/--
High-probability event bridge for the absolute-value version of the Helm sample
alignment error.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem highProb_abs_sample_alignment_of_configError
    {n d d' : Nat}
    (P : Nat → Measure (Sample n d d'))
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    (hconfig :
      HighProbAtTop P
        (fun u =>
          {ω : Sample n d d' |
            ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u})) :
    HighProbAtTop P
      (fun u =>
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))| ≤ rate u}) := by
  exact HighProbAtTop.mono hconfig
    (fun u => sample_alignment_abs_event_of_configError_event ψhat rate u)

/--
High-probability Acharyya-style finite configuration concentration with a
deterministic rate tending to zero gives Helm's finite-sample alignment error
convergence in probability.

The event-measurability hypothesis is the remaining analytic bridge needed to
turn event-level high-probability control into convergence in probability.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem sample_alignment_convergesInProbabilityToZero_of_highProb_configError
    {n d d' : Nat}
    (P : Measure (Sample n d d')) [IsProbabilityMeasure P]
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    -- extra (implicit) assumption beyond the paper: measurability of the sample
    -- alignment-error events (needed to pass from events to convergence in probability)
    (hgood_meas :
      ∀ u, MeasurableSet
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))| ≤ rate u})
    (hrate : Tendsto rate atTop (𝓝 0))
    (hconfig :
      HighProbAtTop (fun _u : Nat => P)
        (fun u =>
          {ω : Sample n d d' |
            ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u})) :
    -- Conclusion: the finite-sample alignment error → 0 in probability.
    ConvergesInProbabilityToZero P
      (fun u ω => (⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))) := by
  exact tendsto_measure_abs_gt_zero_of_highProb_abs_le_rate P
    (fun u ω => (⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1)))
    rate hgood_meas hrate
    (highProb_abs_sample_alignment_of_configError
      (fun _u : Nat => P) ψhat rate hconfig)

/--
Acharyya-style finite configuration concentration supplies Helm's alignment
consistency with the identity affine-isometry alignment.

This theorem is the currently cleanest formal seam between Acharyya2025 and
Helm2025: the remaining hypotheses are rate convergence, rate nonnegativity, and
measurability of the finite sample alignment events.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem alignmentConsistency_of_highProb_configError
    {n d d' : Nat}
    (P : Measure (Z d d')) [IsProbabilityMeasure P]
    (ψhat : Nat → (Sample n d d') → Fin (n + 1) → E d)
    (rate : Nat → Real)
    -- extra (implicit) assumption beyond the paper: measurability of the sample
    -- alignment-error events (needed to pass from events to convergence in probability)
    (hgood_meas :
      ∀ u, MeasurableSet
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1), dist (ψhat u ω i) ((ω i).1))| ≤ rate u})
    (hrate : Tendsto rate atTop (𝓝 0))
    (hconfig :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            ConfigError (ψhat u ω) (fun i : Fin (n + 1) => (ω i).1) ≤ rate u})) :
    -- Conclusion: the estimator ψhat satisfies Helm's alignment consistency (paper Eq. (3)).
    DKPSAlignmentConsistency n d d' P ψhat := by
  refine ⟨fun _u => AffineIsometryEquiv.refl Real (E d), ?_⟩
  simpa using
    sample_alignment_convergesInProbabilityToZero_of_highProb_configError
      (Measure.pi (fun _ : Fin (n + 1) => P))
      ψhat rate hgood_meas hrate hconfig

/-- The true latent configuration supplies positive semidefiniteness of its
population CMDS matrix whenever its entrywise Gram identity is known. -/
theorem populationCMDS_posSemidef_of_gram
    {n d d' : Nat}
    (Dpop : (Sample n d d') → Acharyya2024.DisMat (n + 1))
    (hgram : ∀ ω i j, (∑ k, (ω i).1 k * (ω j).1 k)
      = Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω) i j)
    (ω : Sample n d d') :
    (Acharyya2025.MathlibBridge.disMatToMatrix
      (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω))).PosSemidef := by
  exact (Acharyya2025.GramRealization.posSemidef_and_rank_le_of_config_gram_eq
    (Acharyya2025.MathlibBridge.disMatToMatrix
      (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω)))
    (fun i : Fin (n + 1) => (ω i).1)
    (fun i j => by
      simpa [Acharyya2025.MathlibBridge.disMatToMatrix] using hgram ω i j)).1

/-- The true latent configuration also supplies the ambient-dimension rank
bound for its population CMDS matrix. -/
theorem populationCMDS_rank_le_of_gram
    {n d d' : Nat}
    (Dpop : (Sample n d d') → Acharyya2024.DisMat (n + 1))
    (hgram : ∀ ω i j, (∑ k, (ω i).1 k * (ω j).1 k)
      = Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω) i j)
    (ω : Sample n d d') :
    (Acharyya2025.MathlibBridge.disMatToMatrix
      (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω))).rank ≤ d := by
  exact (Acharyya2025.GramRealization.posSemidef_and_rank_le_of_config_gram_eq
    (Acharyya2025.MathlibBridge.disMatToMatrix
      (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω)))
    (fun i : Fin (n + 1) => (ω i).1)
    (fun i j => by
      simpa [Acharyya2025.MathlibBridge.disMatToMatrix] using hgram ω i j)).2

/--
**Helm alignment consistency from the aligned CMDS spectral estimator — assumptions made explicit.**

Derives Helm's `DKPSAlignmentConsistency` (paper Eq. (3)) for the aligned
classical-MDS spectral estimator from two *decomposed* inputs, in place of the
former opaque `halign` primitive:

* `hgood` — a high-probability event bundling
  (i) the paper's **estimation closeness** (the sample CMDS matrix is entrywise
      `rate u`-close to the per-`ω` population CMDS matrix — the content of the
      Acharyya consistency Helm cites for Eq. (3)), and
  (ii) the **latent eigenvalue stability** `α ≤ λ_i` on the top-`d` block of the
      population CMDS matrix.
* `hpsd`/`hrank`/`hcap`/`hgram` — structural facts about the population CMDS
  matrix (PSD, rank `≤ d`, eigenvalue cap `Λ`, and the Gram realization by the
  true latents `(ω ·).1`).  These are automatic for the distance matrix of a
  centred `d`-dimensional configuration; `hgram` additionally encodes that the
  latents are centred (`classicalMDSMatrix` of a distance matrix is the *centred*
  Gram), and `hpsd` itself follows from `hgram` (Gram matrices are PSD).

**ASSUMPTION SURFACED BY THE FORMALIZATION (not stated in Helm).**  Conjunct (ii)
— the latent eigenvalue stability `α ≤ λ_d` — is **Acharyya 2025's Assumption 2**;
it is *not* among Helm's stated assumptions (A1–A4 constrain only the learning
rule and loss).  It is required because this bridge realizes the DKPS estimator
as the **classical / spectral** MDS embedding (`alignedSpectralConfig`,
Davis–Kahan), whose finite-sample stability genuinely needs an eigengap.  Helm's
own argument avoids it by citing the *asymptotic raw-stress* consistency
(Acharyya 2024), which is eigengap-free; a raw-stress variant of this bridge
would instead surface the milder identifiability condition `UniquePairProfile`.
The theory/practice MDS-variant discrepancy this exposes is exactly the kind of
hidden assumption a formalization is meant to surface.

So `halign` is no longer assumed — it is *derived* from `hgood` via the
deterministic `alignExists_of_entrywiseClose`, with the eigenvalue-stability
assumption now explicit and named.

Formalized by Claude Fable 5 (claude-fable-5[1m]); `halign` discharged to the
explicit eigenvalue-stability assumption by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
theorem alignmentConsistency_of_aligned_spectral
    {n d d' : Nat} (hd : d ≤ n + 1)
    (P : Measure (Z d d')) [IsProbabilityMeasure P]
    (Dhat : Nat → (Sample n d d') → Acharyya2024.DisMat (n + 1))
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    -- The per-ω population dissimilarity matrix (of the true latents `(ω ·).1`):
    (Dpop : (Sample n d d') → Acharyya2024.DisMat (n + 1))
    {α Λ : Real} (hα_pos : 0 < α)
    -- Structural facts about the population CMDS matrix (automatic for the distance
    -- matrix of a centred `d`-dim config; `hpsd` also follows from `hgram`):
    (hpsd : ∀ ω, (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω))).PosSemidef)
    (hrank : ∀ ω, (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω))).rank ≤ d)
    (hcap : ∀ ω l,
        (hpsd ω).isHermitian.eigenvalues₀ l ≤ Λ)
    -- Gram realization (also encodes centring of the latents):
    (hgram : ∀ ω i j, (∑ k, (ω i).1 k * (ω j).1 k)
        = Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω) i j)
    -- Vanishing perturbation rate, used below to make the explicit configuration
    -- bound tend to zero.
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hrate_zero : Tendsto (fun u => ((n + 1 : ℕ) : ℝ) * rate u) atTop (𝓝 0))
    -- measurability of the alignment-error events (implicit, beyond the paper):
    (hgood_meas :
      ∀ u, MeasurableSet
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1),
              dist
                (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
                  (fun i : Fin (n + 1) => (ω i).1)
                  (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                    (((n + 1 : ℕ) : ℝ) * rate u)) u ω i)
                ((ω i).1))|
            ≤ Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                (((n + 1 : ℕ) : ℝ) * rate u)})
    -- ★ Estimation closeness (paper's Acharyya consistency) AND the surfaced latent
    -- eigenvalue-stability (Acharyya 2025 Assumption 2, NOT among Helm's assumptions):
    (hgood :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            Acharyya2025.Bridge.EntrywiseClose
                (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))
                (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω)) (rate u)
            ∧ (∀ i : Fin (Fintype.card (Fin (n + 1))), (i : ℕ) < d →
                α ≤ (hpsd ω).isHermitian.eigenvalues₀ i)})) :
    -- Conclusion: Helm's alignment consistency (Eq. (3)) — now *derived*, with the
    -- eigenvalue-stability assumption explicit (see docstring).
    DKPSAlignmentConsistency n d d' P
      (fun u ω => Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
        (fun i : Fin (n + 1) => (ω i).1)
        (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
          (((n + 1 : ℕ) : ℝ) * rate u)) u ω) := by
  -- Derive the alignment-existence HP event directly from `hgood` via the
  -- strengthened deterministic capstone.
  have halign :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            Acharyya2025.AlignedPipeline.AlignExists hd Dhat hsym
              (fun i : Fin (n + 1) => (ω i).1)
              (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                (((n + 1 : ℕ) : ℝ) * rate u)) u ω}) := by
    refine HighProbAtTop.mono_eventually hgood ?_
    exact Filter.Eventually.of_forall fun u ω hω => by
      obtain ⟨hclose, hfloor⟩ := hω
      exact Acharyya2025.AlignedPipeline.alignExists_of_entrywiseClose
        hd Dhat (Dpop ω) hsym (hpsd ω) (hrank ω) hα_pos hfloor (fun l => hcap ω l)
        (fun i : Fin (n + 1) => (ω i).1) (hgram ω) rate u (hrate_nonneg u)
        ω hclose
  -- Transport to the ConfigError HP event, then apply the identity-alignment bridge.
  have hconfig :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            ConfigError
              (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
                (fun i : Fin (n + 1) => (ω i).1)
                (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                  (((n + 1 : ℕ) : ℝ) * rate u)) u ω)
              (fun i : Fin (n + 1) => (ω i).1)
              ≤ Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                  (((n + 1 : ℕ) : ℝ) * rate u)}) := by
    refine HighProbAtTop.mono halign (fun u ω hω => ?_)
    exact Acharyya2025.AlignedPipeline.configError_alignedSpectralConfig_le
      hd Dhat hsym (fun i : Fin (n + 1) => (ω i).1)
      (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
        (((n + 1 : ℕ) : ℝ) * rate u)) u ω hω
  have hrate_c :
      Tendsto (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
        (((n + 1 : ℕ) : ℝ) * rate u)) atTop (𝓝 0) :=
    Acharyya2025.RateChain.tendsto_configBound_comp_zero (n + 1) d α Λ hrate_zero
  exact alignmentConsistency_of_highProb_configError P
    (fun u ω => Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
      (fun i : Fin (n + 1) => (ω i).1)
      (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
        (((n + 1 : ℕ) : ℝ) * rate u)) u ω)
    (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
      (((n + 1 : ℕ) : ℝ) * rate u))
    hgood_meas hrate_c hconfig

/-- Helm alignment consistency with PSD and rank derived from the true latent
Gram identity.

Compared with `alignmentConsistency_of_aligned_spectral`, this removes two
redundant structural assumptions: a matrix represented as the Gram matrix of
the true `d`-dimensional latents is automatically positive semidefinite and has
rank at most `d`.  The eigengap floor and eigenvalue cap remain genuine
spectral-stability inputs. -/
theorem alignmentConsistency_of_aligned_spectral_of_gram
    {n d d' : Nat} (hd : d ≤ n + 1)
    (P : Measure (Z d d')) [IsProbabilityMeasure P]
    (Dhat : Nat → (Sample n d d') → Acharyya2024.DisMat (n + 1))
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (Dpop : (Sample n d d') → Acharyya2024.DisMat (n + 1))
    {α Λ : Real} (hα_pos : 0 < α)
    (hgram : ∀ ω i j, (∑ k, (ω i).1 k * (ω j).1 k)
      = Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω) i j)
    (hcap : ∀ ω l,
      (populationCMDS_posSemidef_of_gram Dpop hgram ω).isHermitian.eigenvalues₀ l ≤ Λ)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hrate_zero : Tendsto (fun u => ((n + 1 : ℕ) : ℝ) * rate u) atTop (𝓝 0))
    (hgood_meas :
      ∀ u, MeasurableSet
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1),
              dist
                (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
                  (fun i : Fin (n + 1) => (ω i).1)
                  (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                    (((n + 1 : ℕ) : ℝ) * rate u)) u ω i)
                ((ω i).1))|
            ≤ Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
                (((n + 1 : ℕ) : ℝ) * rate u)})
    (hgood :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            Acharyya2025.Bridge.EntrywiseClose
                (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))
                (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω)) (rate u)
            ∧ (∀ i : Fin (Fintype.card (Fin (n + 1))), (i : ℕ) < d →
                α ≤ (populationCMDS_posSemidef_of_gram Dpop hgram ω).isHermitian.eigenvalues₀ i)})) :
    DKPSAlignmentConsistency n d d' P
      (fun u ω => Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
        (fun i : Fin (n + 1) => (ω i).1)
        (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α Λ
          (((n + 1 : ℕ) : ℝ) * rate u)) u ω) := by
  exact alignmentConsistency_of_aligned_spectral hd P Dhat hsym Dpop hα_pos
    (fun ω => populationCMDS_posSemidef_of_gram Dpop hgram ω)
    (fun ω => populationCMDS_rank_le_of_gram Dpop hgram ω)
    hcap hgram rate hrate_nonneg hrate_zero hgood_meas hgood


/-- Helm alignment consistency with the population spectral ceiling obtained
from a uniform entrywise envelope on the random population CMDS matrices.

Unlike the fixed-population Acharyya and Quench pipelines, Helm's population
matrix depends on the latent sample `ω`, so its leading eigenvalue is itself
random and cannot serve directly as the deterministic rate parameter.  A
uniform entrywise bound `β` gives the deterministic ceiling `(n + 1) * β` for
every sample and removes the less transparent pointwise eigenvalue-cap
assumption. -/
theorem alignmentConsistency_of_aligned_spectral_of_gram_entrywiseBound
    {n d d' : Nat} (hd : d ≤ n + 1)
    (P : Measure (Z d d')) [IsProbabilityMeasure P]
    (Dhat : Nat → (Sample n d d') → Acharyya2024.DisMat (n + 1))
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (Dpop : (Sample n d d') → Acharyya2024.DisMat (n + 1))
    {α β : Real} (hα_pos : 0 < α)
    (hgram : ∀ ω i j, (∑ k, (ω i).1 k * (ω j).1 k)
      = Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω) i j)
    (hentry : ∀ ω i j,
      |Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω) i j| ≤ β)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hrate_zero : Tendsto (fun u => ((n + 1 : ℕ) : ℝ) * rate u) atTop (𝓝 0))
    (hgood_meas :
      ∀ u, MeasurableSet
        {ω : Sample n d d' |
          |(⨆ i : Fin (n + 1),
              dist
                (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
                  (fun i : Fin (n + 1) => (ω i).1)
                  (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α
                    (((n + 1 : ℕ) : ℝ) * β)
                    (((n + 1 : ℕ) : ℝ) * rate u)) u ω i)
                ((ω i).1))|
            ≤ Acharyya2025.ConfigPerturbation.configBound (n + 1) d α
                (((n + 1 : ℕ) : ℝ) * β)
                (((n + 1 : ℕ) : ℝ) * rate u)})
    (hgood :
      HighProbAtTop (fun _u : Nat => Measure.pi (fun _ : Fin (n + 1) => P))
        (fun u =>
          {ω : Sample n d d' |
            Acharyya2025.Bridge.EntrywiseClose
                (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))
                (Acharyya2025.Deterministic.classicalMDSMatrix (Dpop ω)) (rate u)
            ∧ (∀ i : Fin (Fintype.card (Fin (n + 1))), (i : ℕ) < d →
                α ≤ (populationCMDS_posSemidef_of_gram Dpop hgram ω).isHermitian.eigenvalues₀ i)})) :
    DKPSAlignmentConsistency n d d' P
      (fun u ω => Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym
        (fun i : Fin (n + 1) => (ω i).1)
        (fun u => Acharyya2025.ConfigPerturbation.configBound (n + 1) d α
          (((n + 1 : ℕ) : ℝ) * β)
          (((n + 1 : ℕ) : ℝ) * rate u)) u ω) := by
  have hcap : ∀ ω l,
      (populationCMDS_posSemidef_of_gram Dpop hgram ω).isHermitian.eigenvalues₀ l
        ≤ (((n + 1 : ℕ) : ℝ) * β) := by
    intro ω l
    apply TauCeti.Matrix.eigenvalues₀_le_of_entry_le
    intro i j
    simpa [Acharyya2025.MathlibBridge.disMatToMatrix] using hentry ω i j
  exact alignmentConsistency_of_aligned_spectral_of_gram hd P Dhat hsym Dpop
    hα_pos hgram hcap rate hrate_nonneg hrate_zero hgood_meas hgood

/-! ### The eigengap-free route

Everything above realizes the DKPS estimator as the *classical / spectral* MDS embedding, whose
finite-sample stability genuinely needs an eigengap; that is why those theorems carry the
latent eigenvalue floor `α`, which is Acharyya 2025's Assumption 2 and is **not** among Helm's
assumptions.  Helm's own argument cites Acharyya 2024's *raw-stress* consistency, which has no
spectral hypothesis at all.

The theorem below is that route.  Its only probabilistic input is convergence in probability of
the estimated pairwise distances to the true ones — exactly what raw-stress consistency
delivers — and it produces Helm's Eq. (3) with no spectral hypothesis anywhere: no eigenvalue
floor, no eigenvalue cap, no positive semidefiniteness, no rank condition, and no Gram
realization.

Two things make this possible.  `TauCeti.exists_delta_forall_exists_rigidMotion` gives a
modulus that does not depend on the configurations, so it survives a random target; and
`TauCeti.alignedConfig` performs the alignment sample by sample, so no alignment sequence has to
be quantified outside the probability.  The alignment is therefore inside the estimator, and the
constant affine isometry witnesses Eq. (3).

The price is that the conclusion is purely qualitative.  That is the right price here: Helm's
Theorems 1 and 2 conclude convergence with no rate, so nothing downstream wants one.  Quench
2026, whose capstones do carry rates, still needs a spectral gap — a quantitative
Gram-to-configuration bound is unstable without one — so its floor is not an artifact of this
substitution.
-/
theorem alignmentConsistency_of_pairwiseDist
    {n d d' : Nat}
    (P : Measure (Z d d')) [IsProbabilityMeasure P]
    -- the raw estimated configurations, before alignment
    (φ : Nat → (Sample n d d') → Fin (n + 1) → E d)
    -- the alignment slack: any positive sequence tending to zero
    (t : Nat → Real) (ht : ∀ u, 0 < t u) (ht0 : Tendsto t atTop (𝓝 0))
    -- ★ the only probabilistic input: the estimated pairwise distances converge in probability
    -- to the true ones.  This is what eigengap-free raw-stress consistency delivers.
    (hdist : ∀ δ > (0 : Real), Tendsto
      (fun u => (Measure.pi (fun _ : Fin (n + 1) => P))
        {ω : Sample n d d' |
          ¬ ∀ i j, |‖φ u ω i - φ u ω j‖ - ‖(ω i).1 - (ω j).1‖| ≤ δ}) atTop (𝓝 0)) :
    DKPSAlignmentConsistency n d d' P
      (fun u ω => TauCeti.alignedConfig (fun i : Fin (n + 1) => (ω i).1) (φ u ω) (t u)) := by
  classical
  refine ⟨fun _u => AffineIsometryEquiv.refl Real (E d), ?_⟩
  have key : ConvergesInProbabilityToZero (Measure.pi (fun _ : Fin (n + 1) => P))
      (fun u ω => ⨆ i : Fin (n + 1),
        dist (TauCeti.alignedConfig (fun i : Fin (n + 1) => (ω i).1) (φ u ω) (t u) i)
          ((ω i).1)) := by
    intro ε hε
    have hmeas : ∀ i j : Fin (n + 1),
        Measurable fun ω : Sample n d d' => ‖(ω i).1 - (ω j).1‖ :=
      fun i j => ((measurable_pi_apply i).fst.sub (measurable_pi_apply j).fst).norm
    have hAE := TauCeti.tendsto_measure_alignmentError_gt
      (Measure.pi (fun _ : Fin (n + 1) => P)) φ (fun ω i => (ω i).1) hmeas hdist
      (ε := ε / 2) (by linarith)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hAE
      (Filter.Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [Filter.Tendsto.eventually_lt_const
      (show (0 : Real) < ε / 2 by linarith) ht0] with u hu
    refine measure_mono fun ω hω => ?_
    have hbdd : BddAbove (Set.range fun i : Fin (n + 1) =>
        dist (TauCeti.alignedConfig (fun i : Fin (n + 1) => (ω i).1) (φ u ω) (t u) i)
          ((ω i).1)) := Finite.bddAbove_range _
    have hle : (⨆ i : Fin (n + 1),
        dist (TauCeti.alignedConfig (fun i : Fin (n + 1) => (ω i).1) (φ u ω) (t u) i)
          ((ω i).1))
        ≤ TauCeti.alignmentError (fun i : Fin (n + 1) => (ω i).1) (φ u ω) + t u :=
      ciSup_le fun i => TauCeti.dist_alignedConfig_le _ _ (ht u) i
    have hnn : (0 : Real) ≤ ⨆ i : Fin (n + 1),
        dist (TauCeti.alignedConfig (fun i : Fin (n + 1) => (ω i).1) (φ u ω) (t u) i)
          ((ω i).1) := le_trans dist_nonneg (le_ciSup hbdd 0)
    rw [Set.mem_ofPred_eq, gt_iff_lt, abs_of_nonneg hnn] at hω
    show ε / 2 < TauCeti.alignmentError (fun i : Fin (n + 1) => (ω i).1) (φ u ω)
    linarith
  simpa using key

end Helm2025.DKPS.AcharyyaBridge
