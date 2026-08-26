/-
Deterministic bridges from finite Acharyya DKPS concentration statements to the
Quench query-efficiency concentration hypothesis.

Quench's theorem is stated over an abstract model space and assumes a uniform
embedding-error event over all models.  Acharyya's DKPS concentration theorems
are finite-configuration statements.  The bridge therefore explicitly assumes a
factorization of the Quench embedding maps through a finite Acharyya
configuration.
-/

import Acharyya2025.AlignedPipeline
import Acharyya2025.RateChain
import DkpsQuench2026.Paper.Theorem2
import Acharyya2025.SpectralMeasurability

open scoped BigOperators Topology
open Filter MeasureTheory

namespace DkpsQuench2026

open Acharyya2024

universe u v

variable {Q : Type u}
variable {X : Type v} [MeasurableSpace X]
variable {Ω : Type} [MeasurableSpace Ω]

/--
Finite Acharyya configuration concentration gives Quench's uniform model-space
embedding concentration when the true and estimated Quench embeddings factor
through the finite configuration by an index map.

The factorization hypothesis is essential: without it, a bound over `Fin n`
cannot imply a bound over an arbitrary model type.

Formalized by Codex 5.5 High, per user-observed model label.
-/
theorem quench_uniform_embedding_error_of_finite_configError
    (μ : Nat → Measure Ω)
    (hμ : ∀ n, IsProbabilityMeasure (μ n))
    {n d : Nat}
    (indexOf : Model Q X → Fin n)
    (ψFinite : Config n d)
    (ψhatFinite : Nat → Ω → Config n d)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (c : Nat → Real)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f = ψhatFinite u ω (indexOf f))
    (hfinite :
      Acharyya2024.HighProbAtTop μ
        (fun u => {ω | ConfigError (ψhatFinite u ω) ψFinite ≤ c u})) :
    -- Conclusion: Quench's uniform model-space embedding-error event holds with high
    -- probability (lifted from the finite Acharyya configuration via the index map).
    _root_.HighProbAtTop μ hμ
      (fun u => {ω | ∀ f, ‖ψHat u ω f - ψ f‖ ≤ c u}) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hfinite δ hδ
  refine ⟨N, fun u hu => ?_⟩
  exact (hN u hu).trans (MeasureTheory.measure_mono fun ω hω f => by
    calc
      ‖ψHat u ω f - ψ f‖
          = ‖ψhatFinite u ω (indexOf f) - ψFinite (indexOf f)‖ := by
            simp [hψ f, hψHat u ω f]
      _ ≤ ConfigError (ψhatFinite u ω) ψFinite :=
            norm_config_le_ConfigError (ψhatFinite u ω) ψFinite (indexOf f)
      _ ≤ c u := hω)

/-- Frobenius finite-configuration concentration gives Quench's uniform
model-space embedding concentration without passing through the legacy
`ConfigError` row-sum metric. -/
theorem quench_uniform_embedding_error_of_finite_configFrobError
    (μ : Nat → Measure Ω)
    (hμ : ∀ n, IsProbabilityMeasure (μ n))
    {n d : Nat}
    (indexOf : Model Q X → Fin n)
    (ψFinite : Config n d)
    (ψhatFinite : Nat → Ω → Config n d)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (c : Nat → Real)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f = ψhatFinite u ω (indexOf f))
    (hfinite : Acharyya2024.HighProbAtTop μ
      (fun u => {ω |
        Acharyya2025.ConfigPerturbation.ConfigFrobError (ψhatFinite u ω) ψFinite ≤ c u})) :
    _root_.HighProbAtTop μ hμ
      (fun u => {ω | ∀ f, ‖ψHat u ω f - ψ f‖ ≤ c u}) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hfinite δ hδ
  refine ⟨N, fun u hu => ?_⟩
  exact (hN u hu).trans (MeasureTheory.measure_mono fun ω hω f => by
    calc
      ‖ψHat u ω f - ψ f‖
          = ‖ψhatFinite u ω (indexOf f) - ψFinite (indexOf f)‖ := by
            simp [hψ f, hψHat u ω f]
      _ ≤ Acharyya2025.ConfigPerturbation.ConfigFrobError
            (ψhatFinite u ω) ψFinite :=
          Acharyya2025.ConfigPerturbation.norm_config_le_ConfigFrobError
            (ψhatFinite u ω) ψFinite (indexOf f)
      _ ≤ c u := hω)

/--
**Quench uniform embedding error from the aligned CMDS spectral estimator.**

A thin, honest composition: the matrix-world spectral capstone (via
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close`)
produces a high-probability bound on `ConfigError (alignedSpectralConfig …) ψ`,
and the existing generic
`quench_uniform_embedding_error_of_finite_configError` lifts it to Quench's
uniform model-space embedding-error event, provided the Quench embedding maps
factor through the finite Acharyya configuration by an index map.

What is composed end-to-end: the entrywise CMDS-closeness HP event `hcenter` is
fed through the proved capstone to produce the aligned-`ConfigError` HP event,
which is then transported by the index-map factorization.  What is hypothesized:
the factorization data (`indexOf`, `hψ`, `hψHat`), the spectral hypotheses of the
capstone (PSD/rank/floor/cap), the Gram realization of `ψ`, and the
entrywise-closeness HP event `hcenter`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem quench_uniform_embedding_error_of_aligned_spectral
    (μ : Nat → Measure Ω)
    (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n d : Nat} (hd : d ≤ n)
    (Dhat : Nat → Ω → Acharyya2024.DisMat n) (D : Acharyya2024.DisMat n)
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (ψFinite : Config n d)
    (hψFinite : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix D i j)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hrate_zero : Filter.Tendsto (fun u => (n : Real) * rate u) Filter.atTop (nhds 0))
    (hcenter : Acharyya2024.HighProbAtTop μ (fun u => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate u)}))
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)) u ω (indexOf f)) :
    -- Conclusion: Quench's uniform model-space embedding-error event holds with high
    -- probability (lifted from the finite Acharyya configuration via the index map).
    _root_.HighProbAtTop μ hμ
      (fun u => {ω | ∀ f, ‖ψHat u ω f - ψ f‖ ≤
        Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)}) := by
  -- Capstone composition: produce the aligned-`ConfigError` HP event.
  have haligned :=
    Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_entrywise_close
      μ hd Dhat D hsym hB hrank hα_pos hfloor hΛ ψFinite hψFinite
      rate hrate_nonneg hrate_zero hcenter
  -- Lift through the index-map factorization with the existing generic theorem.
  exact quench_uniform_embedding_error_of_finite_configError
    μ hμ indexOf ψFinite
    (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
      (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
        ((n : Real) * rate u)))
    ψ ψHat
    (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
      ((n : Real) * rate u))
    hψ hψHat haligned

/-- Quench uniform embedding concentration from the paper-facing Frobenius
Acharyya spectral bound.

Compared with `quench_uniform_embedding_error_of_aligned_spectral`, the final
uniform per-model conclusion is the same shape, but its rate is
`configFrobBound` rather than `configBound = √n · configFrobBound`. -/
theorem quench_uniform_embedding_error_of_aligned_spectral_frob
    (μ : Nat → Measure Ω)
    (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n d : Nat} (hd : d ≤ n)
    (Dhat : Nat → Ω → Acharyya2024.DisMat n) (D : Acharyya2024.DisMat n)
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (ψFinite : Config n d)
    (hψFinite : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix D i j)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hrate_zero : Filter.Tendsto (fun u => (n : Real) * rate u) Filter.atTop (nhds 0))
    (hcenter : Acharyya2024.HighProbAtTop μ (fun u => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate u)}))
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfigFrob hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
          ((n : Real) * rate u)) u ω (indexOf f)) :
    _root_.HighProbAtTop μ hμ
      (fun u => {ω | ∀ f, ‖ψHat u ω f - ψ f‖ ≤
        Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
          ((n : Real) * rate u)}) := by
  have haligned :=
    Acharyya2025.AlignedPipeline.highProb_aligned_configFrobError_of_entrywise_close
      μ hd Dhat D hsym hB hrank hα_pos hfloor hΛ ψFinite hψFinite
      rate hrate_nonneg hrate_zero hcenter
  exact quench_uniform_embedding_error_of_finite_configFrobError
    μ hμ indexOf ψFinite
    (Acharyya2025.AlignedPipeline.alignedSpectralConfigFrob hd Dhat hsym ψFinite
      (fun u => Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
        ((n : Real) * rate u)))
    ψ ψHat
    (fun u => Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
      ((n : Real) * rate u))
    hψ hψHat haligned

/--
**Reusable core: query efficiency from the CMDS-entrywise high-probability event.**

Given the population spectral structure (PSD / rank / floor `α` / cap `Λ`), the
Gram realization of `ψFinite`, the entrywise-rate assumptions, the honest
*sample-matrix* measurability primitive `hDmeas` (`Measurable (fun ω => Dhat k ω)`,
trivially true), the high-probability CMDS-entrywise-closeness event `hcenter`
(the paper's Theorem 1 content), and the genuine Quench assumptions
(factorization, score Lipschitz, model coverage, MSE positivity), conclude
Theorem 2 Part 2.

The measurable high-probability sub-event is the **entrywise event itself**: it
is directly Borel (each CMDS entry is algebraic in `Dhat`,
`SpectralMeasurability.measurableSet_entrywiseClose_event`) and is *deterministically*
contained in the embedding-error event (`AlignedPipeline.alignExists_of_entrywiseClose`
— the matrix capstone produces the aligning isometry on every entrywise-close
sample).  No measurability of the eigenvector-valued raw embedding is needed; the
previously-assumed `hmeas_spec` is gone.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
theorem quench_part2_from_aligned_configError_hp
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n d : Nat} (hd : d ≤ n)
    (Dhat : Nat → Ω → Acharyya2024.DisMat n)
    (hsym : ∀ u ω, (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (D : Acharyya2024.DisMat n)
    (ψFinite : Config n d)
    -- Population spectral structure (Assumptions 1/2):
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (hψFinite_gram : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix D i j)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (_hrate_zero : Filter.Tendsto (fun u => (n : Real) * rate u) Filter.atTop (nhds 0))
    (c : Nat → Real)
    (hc_eq : c = fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
      ((n : Real) * rate u))
    -- The honest measurability primitive replacing `hmeas_spec`: the sample
    -- dissimilarity matrix is measurable in the sample (trivially dischargeable).
    (hDmeas : ∀ k, Measurable (fun ω => Dhat k ω))
    -- Theorem 1 input: high-probability entrywise CMDS-closeness event.
    (hcenter : Acharyya2024.HighProbAtTop μ (fun k => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat k ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate k)}))
    (h_c_tendsto : Filter.Tendsto c Filter.atTop (nhds 0))
    (h_c_nonneg : ∀ k, 0 ≤ c k)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite c u ω
        (indexOf f))
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    -- Conclusion: with high probability, MSE(ŷ_NN) ≤ MSE(ŷ_Q) — the NN estimator is
    -- query-efficient relative to the subset baseline ŷ_Q.  (Here the embedding-error
    -- event is *derived* from the spectral / statistical inputs, not assumed.)
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  -- The strengthened finite spectral theorem applies directly on the measurable
  -- CMDS-entrywise event; no local smallness tail restriction is required.
  set E : Nat → Set Ω := fun k => {ω |
    Acharyya2025.Bridge.EntrywiseClose
      (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat k ω))
      (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate k)} with hE_def
  have hcenter_meas : ∀ k, MeasurableSet {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat k ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate k)} := fun k =>
    Acharyya2025.SpectralMeasurability.measurableSet_entrywiseClose_event Dhat D rate k
      (hDmeas k)
  have hE_meas : ∀ k, MeasurableSet (E k) := by
    intro k
    rw [hE_def]
    exact hcenter_meas k
  have hE_sub : ∀ k, E k ⊆ {ω | ∀ f, ‖ψHat k ω f - ψ f‖ ≤ c k} := by
    intro k ω hω f
    have hclose := hω
    have hA : Acharyya2025.AlignedPipeline.AlignExists hd Dhat hsym ψFinite c k ω := by
      rw [hc_eq]
      exact Acharyya2025.AlignedPipeline.alignExists_of_entrywiseClose
        hd Dhat D hsym hB hrank hα_pos hfloor hΛ ψFinite hψFinite_gram
        rate k (hrate_nonneg k) ω hclose
    have hcfg := Acharyya2025.AlignedPipeline.configError_alignedSpectralConfig_le
      hd Dhat hsym ψFinite c k ω hA
    calc ‖ψHat k ω f - ψ f‖
        = ‖Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite c k ω
            (indexOf f) - ψFinite (indexOf f)‖ := by rw [hψHat, hψ]
      _ ≤ ConfigError
            (Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite c k ω)
            ψFinite := norm_config_le_ConfigError _ _ _
      _ ≤ _ := hcfg
  have hE_acharyya : Acharyya2024.HighProbAtTop μ E := by
    rw [hE_def]
    exact hcenter
  have hE : _root_.HighProbAtTop μ hμ E := by
    intro δ hδ
    exact hE_acharyya δ hδ
  exact highProb_queryEfficient_nn_of_subevent (Q := Q) (X := X) (d := d) Pf μ hμ
    (fun _ f => ψ f) (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub
    γ h_lipQ h_gamma_pos _ h_c_tendsto h_c_nonneg
    E hE_meas hE_sub hE h_cover h_cover_meas hMSE_Q_pos

/--
**Frobenius core: query efficiency from the CMDS-entrywise high-probability event.**

This is the paper-facing counterpart of `quench_part2_from_aligned_configError_hp`.
It uses the DK-sharpened `configFrobBound` and `alignedSpectralConfigFrob`, then
converts Frobenius control to the uniform per-model error needed by Quench via
`norm_config_le_ConfigFrobError`.  The measurable subevent remains the CMDS
entrywise event, so no eigenbasis measurability assumption is introduced.
-/
theorem quench_part2_from_aligned_configFrobError_hp
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n d : Nat} (hd : d ≤ n)
    (Dhat : Nat → Ω → Acharyya2024.DisMat n)
    (hsym : ∀ u ω, (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (D : Acharyya2024.DisMat n)
    (ψFinite : Config n d)
    -- Population spectral structure (Assumptions 1/2):
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (hψFinite_gram : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix D i j)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (_hrate_zero : Filter.Tendsto (fun u => (n : Real) * rate u) Filter.atTop (nhds 0))
    (c : Nat → Real)
    (hc_majorant : ∀ᶠ u in Filter.atTop,
      Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
        ((n : Real) * rate u) ≤ c u)
    -- The honest measurability primitive replacing `hmeas_spec`: the sample
    -- dissimilarity matrix is measurable in the sample (trivially dischargeable).
    (hDmeas : ∀ k, Measurable (fun ω => Dhat k ω))
    -- Theorem 1 input: high-probability entrywise CMDS-closeness event.
    (hcenter : Acharyya2024.HighProbAtTop μ (fun k => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat k ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate k)}))
    (h_c_tendsto : Filter.Tendsto c Filter.atTop (nhds 0))
    (h_c_nonneg : ∀ k, 0 ≤ c k)
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfigFrob hd Dhat hsym ψFinite c u ω
        (indexOf f))
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    -- Conclusion: with high probability, MSE(ŷ_NN) ≤ MSE(ŷ_Q) — the NN estimator is
    -- query-efficient relative to the subset baseline ŷ_Q.  (Here the embedding-error
    -- event is *derived* from the spectral / statistical inputs, not assumed.)
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  -- Only domination by the requested majorant remains as a tail condition.
  let side : Nat → Prop := fun k =>
    Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
      ((n : Real) * rate k) ≤ c k
  set E : Nat → Set Ω := fun k => {ω |
    Acharyya2025.Bridge.EntrywiseClose
      (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat k ω))
      (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate k) ∧ side k} with hE_def
  have hcenter_meas : ∀ k, MeasurableSet {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat k ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate k)} := fun k =>
    Acharyya2025.SpectralMeasurability.measurableSet_entrywiseClose_event Dhat D rate k
      (hDmeas k)
  have hside_meas : ∀ k, MeasurableSet {ω : Ω | side k} := by
    intro k
    by_cases hk : side k
    · simp [hk]
    · simp [hk]
  have hE_meas : ∀ k, MeasurableSet (E k) := by
    intro k
    rw [hE_def]
    exact (hcenter_meas k).inter (hside_meas k)
  have hE_sub : ∀ k, E k ⊆ {ω | ∀ f, ‖ψHat k ω f - ψ f‖ ≤ c k} := by
    intro k ω hω f
    obtain ⟨hclose, hbound⟩ := hω
    have hAexact := Acharyya2025.AlignedPipeline.alignFrobExists_of_entrywiseClose
      hd Dhat D hsym hB hrank hα_pos hfloor hΛ ψFinite hψFinite_gram
      rate k (hrate_nonneg k) ω hclose
    have hA : Acharyya2025.AlignedPipeline.AlignFrobExists hd Dhat hsym ψFinite c k ω :=
      Acharyya2025.AlignedPipeline.AlignFrobExists.mono hAexact hbound
    have hcfg := Acharyya2025.AlignedPipeline.configFrobError_alignedSpectralConfigFrob_le
      hd Dhat hsym ψFinite c k ω hA
    calc ‖ψHat k ω f - ψ f‖
        = ‖Acharyya2025.AlignedPipeline.alignedSpectralConfigFrob hd Dhat hsym ψFinite c k ω
            (indexOf f) - ψFinite (indexOf f)‖ := by rw [hψHat, hψ]
      _ ≤ Acharyya2025.ConfigPerturbation.ConfigFrobError
            (Acharyya2025.AlignedPipeline.alignedSpectralConfigFrob hd Dhat hsym ψFinite c k ω)
            ψFinite := Acharyya2025.ConfigPerturbation.norm_config_le_ConfigFrobError _ _ _
      _ ≤ _ := hcfg
  have hside_eventually : ∀ᶠ k in Filter.atTop, side k := by
    simpa [side] using hc_majorant
  have hE_acharyya : Acharyya2024.HighProbAtTop μ E := by
    refine Acharyya2024.HighProbAtTop.mono_eventually hcenter ?_
    filter_upwards [hside_eventually] with k hk
    intro ω hω
    exact ⟨hω, hk⟩
  have hE : _root_.HighProbAtTop μ hμ E := by
    intro δ hδ
    exact hE_acharyya δ hδ
  exact highProb_queryEfficient_nn_of_subevent (Q := Q) (X := X) (d := d) Pf μ hμ
    (fun _ f => ψ f) (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub
    γ h_lipQ h_gamma_pos _ h_c_tendsto h_c_nonneg
    E hE_meas hE_sub hE h_cover h_cover_meas hMSE_Q_pos


/--
**Quench Part 2 with the explicit quadratic DK envelope.**

This specializes `quench_part2_from_aligned_configFrobError_hp` to
`configFrobQuadraticMajorant`.  Since `(n : ℝ) * rate u → 0`, the operator
perturbation is eventually in `[0,1]`, where the exact sharpened Acharyya bound
is dominated by `C₁ ε + C₂ ε²`.  Quench therefore consumes a genuine
polynomial spectral concentration rate rather than the nested-square-root
internal bound.
-/
theorem quench_part2_from_aligned_configFrobQuadratic_hp
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n d : Nat} (hd : d ≤ n)
    (Dhat : Nat → Ω → Acharyya2024.DisMat n)
    (hsym : ∀ u ω, (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (D : Acharyya2024.DisMat n)
    (ψFinite : Config n d)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (hψFinite_gram : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix D i j)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hrate_zero : Filter.Tendsto (fun u => (n : Real) * rate u) Filter.atTop (nhds 0))
    (hDmeas : ∀ k, Measurable (fun ω => Dhat k ω))
    (hcenter : Acharyya2024.HighProbAtTop μ (fun k => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat k ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate k)}))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfigFrob hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configFrobQuadraticMajorant d α Λ
          ((n : Real) * rate u)) u ω (indexOf f))
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  let c : Nat → Real := fun u =>
    Acharyya2025.ConfigPerturbation.configFrobQuadraticMajorant d α Λ
      ((n : Real) * rate u)
  have hop_nonneg : ∀ u, 0 ≤ (n : Real) * rate u := fun u =>
    mul_nonneg (Nat.cast_nonneg n) (hrate_nonneg u)
  have hop_le_one : ∀ᶠ u in Filter.atTop, (n : Real) * rate u ≤ 1 :=
    (hrate_zero.eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))).mono
      (fun _ hu => hu.le)
  have hc_majorant : ∀ᶠ u in Filter.atTop,
      Acharyya2025.ConfigPerturbation.configFrobBound d α Λ ((n : Real) * rate u) ≤ c u := by
    filter_upwards [hop_le_one] with u hu
    exact Acharyya2025.ConfigPerturbation.configFrobBound_le_configFrobQuadraticMajorant
      d α Λ ((n : Real) * rate u) (hop_nonneg u) hu
  have hc_zero : Filter.Tendsto c Filter.atTop (nhds 0) := by
    have hlin := hrate_zero.const_mul
      (Acharyya2025.ConfigPerturbation.configFrobLinearCoeff d α Λ)
    have hquad := (hrate_zero.pow 2).const_mul
      (Acharyya2025.ConfigPerturbation.configFrobQuadraticCoeff d α Λ)
    simpa [c, Acharyya2025.ConfigPerturbation.configFrobQuadraticMajorant] using hlin.add hquad
  have hc_nonneg : ∀ u, 0 ≤ c u := by
    intro u
    have he : 0 ≤ (n : Real) * rate u := hop_nonneg u
    have hlin : 0 ≤ Acharyya2025.ConfigPerturbation.configFrobLinearCoeff d α Λ := by
      unfold Acharyya2025.ConfigPerturbation.configFrobLinearCoeff
      positivity
    have hquad : 0 ≤ Acharyya2025.ConfigPerturbation.configFrobQuadraticCoeff d α Λ := by
      unfold Acharyya2025.ConfigPerturbation.configFrobQuadraticCoeff
      positivity
    dsimp [c]
    unfold Acharyya2025.ConfigPerturbation.configFrobQuadraticMajorant
    exact add_nonneg (mul_nonneg hlin he) (mul_nonneg hquad (sq_nonneg _))
  apply quench_part2_from_aligned_configFrobError_hp Pf μ hμ hd Dhat hsym D ψFinite
    hB hrank hα_pos hfloor hΛ hψFinite_gram rate hrate_nonneg hrate_zero c
    hc_majorant hDmeas hcenter hc_zero hc_nonneg f_ref score Qstar Qsub γ
    indexOf ψ ψHat h_lipQ h_gamma_pos hψ
  · simpa [c] using hψHat
  · exact h_cover
  · exact h_cover_meas
  · exact hMSE_Q_pos

/--
**Query efficiency from the spectral concentration chain (Theorem 2 Part 2,
`h_conc` discharged).**

This is `DkpsQuench2026.highProb_queryEfficient_nn` with the abstract uniform
embedding-error event `h_conc` (and the rate side-conditions `h_c_tendsto`,
`h_c_nonneg`) no longer *assumed* but *derived* from the actual statistical /
spectral inputs, via `quench_uniform_embedding_error_of_aligned_spectral` and
the `RateChain` vanishing-rate lemmas.  In other words: the concentration
hypothesis is replaced by the prose assumptions that produce it (population PSD
/ rank / spectral-floor / cap structure, the entrywise CMDS-closeness
high-probability event `hcenter`, the Gram realization of `ψ`, the index-map
factorization, and the vanishing rate `(n)·rate u → 0`).

**Measurability fully discharged (no eigenbasis, no measurable selection).**
The previously-assumed `hmeas_spec` (measurability of the eigenvector-valued raw
spectral embedding — genuinely *not* provable, the eigenbasis is discontinuous
at eigenvalue crossings) is replaced by the trivially-true `hDhat_meas`
(`Measurable (fun ω => Dhat k ω)`: the sample dissimilarity matrix is measurable
in the sample).  The measurable high-probability sub-event is the CMDS-entrywise
event `hcenter` itself: directly Borel (each CMDS entry is algebraic in `Dhat`),
and *deterministically* contained in the embedding-error event (the matrix
capstone aligns every entrywise-close sample —
`AlignedPipeline.alignExists_of_entrywiseClose`).  The model-coverage assumptions
`h_cover`/`h_cover_meas` (paper Assumption 2) and the score Lipschitz /
MSE-positivity assumptions remain, as they should.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]); measurability seam
discharged by Claude Fable 5 (claude-fable-5[1m]).
-/
theorem queryEfficient_nn_of_aligned_spectral
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n d : Nat} (hd : d ≤ n)
    (Dhat : Nat → Ω → Acharyya2024.DisMat n) (D : Acharyya2024.DisMat n)
    (hsym : ∀ u ω,
      (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))).IsHermitian)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix D)).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (ψFinite : Config n d)
    (hψFinite : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix D i j)
    (rate : Nat → Real) (hrate_nonneg : ∀ u, 0 ≤ rate u)
    (hrate_zero : Filter.Tendsto (fun u => (n : Real) * rate u) Filter.atTop (nhds 0))
    (hcenter : Acharyya2024.HighProbAtTop μ (fun u => {ω |
      Acharyya2025.Bridge.EntrywiseClose
        (Acharyya2025.Deterministic.classicalMDSMatrix (Dhat u ω))
        (Acharyya2025.Deterministic.classicalMDSMatrix D) (rate u)}))
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfig hd Dhat hsym ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate u)) u ω (indexOf f))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    -- Honest measurability primitive (replacing raw-embedding measurability):
    -- the sample dissimilarity matrix is measurable in the sample.
    (hDhat_meas : ∀ k, Measurable (fun ω => Dhat k ω))
    -- Genuine model-coverage assumption (paper Assumption 2):
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    -- Conclusion: with high probability, MSE(ŷ_NN) ≤ MSE(ŷ_Q) — the NN estimator is
    -- query-efficient relative to the subset baseline ŷ_Q.  (Here the embedding-error
    -- event is *derived* from the spectral / statistical inputs, not assumed.)
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  have h_c_tendsto :
      Filter.Tendsto
        (fun k => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * rate k)) Filter.atTop (nhds 0) :=
    Acharyya2025.RateChain.tendsto_configBound_comp_zero n d α Λ hrate_zero
  have h_c_nonneg : ∀ k, 0 ≤ Acharyya2025.ConfigPerturbation.configBound n d α Λ
      ((n : Real) * rate k) := by
    intro k
    unfold Acharyya2025.ConfigPerturbation.configBound
    positivity
  exact quench_part2_from_aligned_configError_hp Pf μ hμ hd Dhat hsym D ψFinite
    hB hrank hα_pos hfloor hΛ hψFinite rate hrate_nonneg hrate_zero
    (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ ((n : Real) * rate u)) rfl
    hDhat_meas hcenter h_c_tendsto h_c_nonneg f_ref score Qstar Qsub γ
    indexOf ψ ψHat h_lipQ h_gamma_pos hψ hψHat h_cover h_cover_meas hMSE_Q_pos

/--
**Query efficiency from response-mean concentration (Theorem 2 Part 2, deeper).**

Like `queryEfficient_nn_of_aligned_spectral`, but one level deeper in the
concentration chain: instead of the packaged entrywise CMDS-closeness event
`hcenter`, this takes the paper's actual upstream input — the **uniform
response-mean closeness** high-probability event
`{ω | UniformResponseMeanClose (Xbar u ω) μ (η u)}` — and *derives* the entrywise
CMDS event internally via
`Acharyya2025.AlignedPipeline.highProb_aligned_configError_of_response_mean`
(which composes the Bridge chain response-mean → direct pairwise entrywise → CMDS).
Everything else (the choice-free measurable sub-event, the genuine Quench
assumptions) is the shared `quench_part2_from_aligned_configError_hp` core.

The residual honest primitives are the same: `hXmeas` (measurability of the
sample response-distance matrix in the sample — trivially true) and the model
coverage `h_cover`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
theorem queryEfficient_nn_of_response_mean
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Xbar : Nat → Ω → Fin n → Acharyya2024.Mat m p) (μvec : Fin n → Acharyya2024.Mat m p)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (ψFinite : Config n d)
    (hψFinite : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix (Acharyya2024.responseDist μvec) i j)
    (η R : Nat → Real)
    (hrate_nonneg : ∀ u, 0 ≤ Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
    (hrate_zero : Filter.Tendsto
      (fun u => (n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
      Filter.atTop (nhds 0))
    (hmean : Acharyya2024.HighProbAtTop μ
      (fun u => {ω | Acharyya2025.Bridge.UniformResponseMeanClose (Xbar u ω) μvec (η u)}))
    (hsample_bound : ∀ u ω i j, |Acharyya2024.responseDist (Xbar u ω) i j| ≤ R u)
    (hpopulation_bound : ∀ u i j, |Acharyya2024.responseDist μvec i j| ≤ R u)
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfig hd
        (fun u ω => Acharyya2024.responseDist (Xbar u ω))
        (fun u ω => Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
          (Xbar u ω))
        ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))) u ω
        (indexOf f))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    -- Honest measurability primitive: the sample response-distance matrix is
    -- measurable in the sample.
    (hXmeas : ∀ k, Measurable (fun ω => Acharyya2024.responseDist (Xbar k ω)))
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    -- Conclusion: with high probability, MSE(ŷ_NN) ≤ MSE(ŷ_Q) — the NN estimator is
    -- query-efficient relative to the subset baseline ŷ_Q.  (Here the embedding-error
    -- event is *derived* from the spectral / statistical inputs, not assumed.)
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  -- The CMDS-entrywise HP event derived from response-mean concentration (Bridge chain).
  have hcenter :=
    Acharyya2025.AlignedPipeline.highProb_cmdsEntrywise_of_response_mean
      μ hn Xbar μvec η R hmean hsample_bound hpopulation_bound
  have h_c_tendsto :
      Filter.Tendsto
        (fun k => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R k) (η k)))
        Filter.atTop (nhds 0) :=
    Acharyya2025.RateChain.tendsto_configBound_comp_zero n d α Λ hrate_zero
  have h_c_nonneg : ∀ k, 0 ≤ Acharyya2025.ConfigPerturbation.configBound n d α Λ
      ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R k) (η k)) := by
    intro k
    unfold Acharyya2025.ConfigPerturbation.configBound
    positivity
  exact quench_part2_from_aligned_configError_hp Pf μ hμ hd
    (fun u ω => Acharyya2024.responseDist (Xbar u ω))
    (fun u ω => Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
      (Xbar u ω))
    (Acharyya2024.responseDist μvec)
    ψFinite hB hrank hα_pos hfloor hΛ hψFinite
    (fun u => Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
    hrate_nonneg hrate_zero
    (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
      ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))) rfl
    hXmeas hcenter h_c_tendsto h_c_nonneg f_ref score Qstar Qsub γ
    indexOf ψ ψHat h_lipQ h_gamma_pos hψ hψHat h_cover h_cover_meas hMSE_Q_pos

/--
**Query efficiency from response-mean concentration using the Frobenius Acharyya rate.**

This is the DK-sharpened paper-facing variant of `queryEfficient_nn_of_response_mean`.
It follows the same response-mean → CMDS-entrywise concentration chain, but its
aligned estimator and rate use `configFrobBound`, eliminating the terminal `√n`
conversion before Quench takes the required uniform rowwise consequence.
-/
theorem queryEfficient_nn_of_response_mean_frob
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Xbar : Nat → Ω → Fin n → Acharyya2024.Mat m p) (μvec : Fin n → Acharyya2024.Mat m p)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (ψFinite : Config n d)
    (hψFinite : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix (Acharyya2024.responseDist μvec) i j)
    (η R : Nat → Real)
    (hrate_nonneg : ∀ u, 0 ≤ Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
    (hrate_zero : Filter.Tendsto
      (fun u => (n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
      Filter.atTop (nhds 0))
    (hmean : Acharyya2024.HighProbAtTop μ
      (fun u => {ω | Acharyya2025.Bridge.UniformResponseMeanClose (Xbar u ω) μvec (η u)}))
    (hsample_bound : ∀ u ω i j, |Acharyya2024.responseDist (Xbar u ω) i j| ≤ R u)
    (hpopulation_bound : ∀ u i j, |Acharyya2024.responseDist μvec i j| ≤ R u)
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfigFrob hd
        (fun u ω => Acharyya2024.responseDist (Xbar u ω))
        (fun u ω => Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
          (Xbar u ω))
        ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
          ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))) u ω
        (indexOf f))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    -- Honest measurability primitive: the sample response-distance matrix is
    -- measurable in the sample.
    (hXmeas : ∀ k, Measurable (fun ω => Acharyya2024.responseDist (Xbar k ω)))
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    -- Conclusion: with high probability, MSE(ŷ_NN) ≤ MSE(ŷ_Q) — the NN estimator is
    -- query-efficient relative to the subset baseline ŷ_Q.  (Here the embedding-error
    -- event is *derived* from the spectral / statistical inputs, not assumed.)
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  -- The CMDS-entrywise HP event derived from response-mean concentration (Bridge chain).
  have hcenter :=
    Acharyya2025.AlignedPipeline.highProb_cmdsEntrywise_of_response_mean
      μ hn Xbar μvec η R hmean hsample_bound hpopulation_bound
  have h_c_tendsto :
      Filter.Tendsto
        (fun k => Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
          ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R k) (η k)))
        Filter.atTop (nhds 0) :=
    Acharyya2025.RateChain.tendsto_configFrobBound_comp_zero d α Λ hrate_zero
  have h_c_nonneg : ∀ k, 0 ≤ Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
      ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R k) (η k)) := by
    intro k
    unfold Acharyya2025.ConfigPerturbation.configFrobBound
    positivity
  exact quench_part2_from_aligned_configFrobError_hp Pf μ hμ hd
    (fun u ω => Acharyya2024.responseDist (Xbar u ω))
    (fun u ω => Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
      (Xbar u ω))
    (Acharyya2024.responseDist μvec)
    ψFinite hB hrank hα_pos hfloor hΛ hψFinite
    (fun u => Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
    hrate_nonneg hrate_zero
    (fun u => Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
      ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u)))
    (Filter.Eventually.of_forall (fun _ => le_rfl))
    hXmeas hcenter h_c_tendsto h_c_nonneg f_ref score Qstar Qsub γ
    indexOf ψ ψHat h_lipQ h_gamma_pos hψ hψHat h_cover h_cover_meas hMSE_Q_pos

/--
**Query efficiency from iid second moments (Theorem 2 Part 2, raw-response).**

The literal bottom of the paper's concentration chain.  This is
`queryEfficient_nn_of_response_mean` with the response-mean closeness event
`hmean` itself *derived* — via Chebyshev + a union bound
(`Acharyya2025.RateChain.highProb_uniformResponseMeanClose_of_secondMoment`) —
from per-model second-moment bounds `∫ ‖X̄ᵤ ᵢ − μᵢ‖² ≤ σ2 u` with vanishing
Chebyshev ratio `n · σ2 u / (η u)² → 0`.  So the entire query-efficiency
conclusion now follows from iid second-moment hypotheses on the response means
(the only honest probabilistic input the paper assumes), together with the
spectral structure and the genuine Quench assumptions.

The residual honest primitives remain `hXmeas` (sample response-distance matrix
measurability — trivially true) and the model coverage `h_cover`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).
-/
theorem queryEfficient_nn_of_second_moment
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Xbar : Nat → Ω → Fin n → Acharyya2024.Mat m p) (μvec : Fin n → Acharyya2024.Mat m p)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (ψFinite : Config n d)
    (hψFinite : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix (Acharyya2024.responseDist μvec) i j)
    (η R : Nat → Real)
    (hrate_nonneg : ∀ u, 0 ≤ Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
    (hrate_zero : Filter.Tendsto
      (fun u => (n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
      Filter.atTop (nhds 0))
    -- iid second-moment hypotheses (replacing the assumed response-mean event):
    (σ2 : Nat → Real)
    (hint : ∀ u (i : Fin n), Integrable (fun ω => ‖Xbar u ω i - μvec i‖ ^ 2) (μ u))
    (hσ2 : ∀ u (i : Fin n), ∫ ω, ‖Xbar u ω i - μvec i‖ ^ 2 ∂(μ u) ≤ σ2 u)
    (hη_pos : ∀ u, 0 < η u)
    (hratio : Filter.Tendsto (fun u => (n : Real) * σ2 u / (η u) ^ 2) Filter.atTop (nhds 0))
    (hsample_bound : ∀ u ω i j, |Acharyya2024.responseDist (Xbar u ω) i j| ≤ R u)
    (hpopulation_bound : ∀ u i j, |Acharyya2024.responseDist μvec i j| ≤ R u)
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfig hd
        (fun u ω => Acharyya2024.responseDist (Xbar u ω))
        (fun u ω => Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
          (Xbar u ω))
        ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))) u ω
        (indexOf f))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    -- Honest measurability primitive: the sample response-distance matrix is
    -- measurable in the sample.
    (hXmeas : ∀ k, Measurable (fun ω => Acharyya2024.responseDist (Xbar k ω)))
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    -- Conclusion: with high probability, MSE(ŷ_NN) ≤ MSE(ŷ_Q) — the NN estimator is
    -- query-efficient relative to the subset baseline ŷ_Q.  (Here the embedding-error
    -- event is *derived* from the spectral / statistical inputs, not assumed.)
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  -- Derive the response-mean closeness event from second moments (Chebyshev).
  have : ∀ u, IsProbabilityMeasure (μ u) := hμ
  have hmean :=
    Acharyya2025.RateChain.highProb_uniformResponseMeanClose_of_secondMoment
      μ Xbar μvec σ2 η hint hσ2 hη_pos hratio
  exact queryEfficient_nn_of_response_mean Pf μ hμ hn hd Xbar μvec hB hrank hα_pos hfloor hΛ
    ψFinite hψFinite η R hrate_nonneg hrate_zero hmean hsample_bound
    hpopulation_bound indexOf ψ ψHat hψ hψHat f_ref score Qstar Qsub γ h_lipQ
    h_gamma_pos hXmeas h_cover h_cover_meas hMSE_Q_pos

/--
**Query efficiency from iid second moments using the Frobenius Acharyya rate.**

This is the raw-response Quench capstone for the DK-sharpened path.  It derives
response-mean concentration by Chebyshev exactly as the legacy theorem does,
then uses `queryEfficient_nn_of_response_mean_frob`, so the final concentration
rate no longer carries the compatibility-only `√n` factor.
-/
theorem queryEfficient_nn_of_second_moment_frob
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Xbar : Nat → Ω → Fin n → Acharyya2024.Mat m p) (μvec : Fin n → Acharyya2024.Mat m p)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (ψFinite : Config n d)
    (hψFinite : ∀ i j, (∑ k, ψFinite i k * ψFinite j k)
      = Acharyya2025.Deterministic.classicalMDSMatrix (Acharyya2024.responseDist μvec) i j)
    (η R : Nat → Real)
    (hrate_nonneg : ∀ u, 0 ≤ Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
    (hrate_zero : Filter.Tendsto
      (fun u => (n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
      Filter.atTop (nhds 0))
    -- iid second-moment hypotheses (replacing the assumed response-mean event):
    (σ2 : Nat → Real)
    (hint : ∀ u (i : Fin n), Integrable (fun ω => ‖Xbar u ω i - μvec i‖ ^ 2) (μ u))
    (hσ2 : ∀ u (i : Fin n), ∫ ω, ‖Xbar u ω i - μvec i‖ ^ 2 ∂(μ u) ≤ σ2 u)
    (hη_pos : ∀ u, 0 < η u)
    (hratio : Filter.Tendsto (fun u => (n : Real) * σ2 u / (η u) ^ 2) Filter.atTop (nhds 0))
    (hsample_bound : ∀ u ω i j, |Acharyya2024.responseDist (Xbar u ω) i j| ≤ R u)
    (hpopulation_bound : ∀ u i j, |Acharyya2024.responseDist μvec i j| ≤ R u)
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f = ψFinite (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfigFrob hd
        (fun u ω => Acharyya2024.responseDist (Xbar u ω))
        (fun u ω => Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
          (Xbar u ω))
        ψFinite
        (fun u => Acharyya2025.ConfigPerturbation.configFrobBound d α Λ
          ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))) u ω
        (indexOf f))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    -- Honest measurability primitive: the sample response-distance matrix is
    -- measurable in the sample.
    (hXmeas : ∀ k, Measurable (fun ω => Acharyya2024.responseDist (Xbar k ω)))
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    -- Conclusion: with high probability, MSE(ŷ_NN) ≤ MSE(ŷ_Q) — the NN estimator is
    -- query-efficient relative to the subset baseline ŷ_Q.  (Here the embedding-error
    -- event is *derived* from the spectral / statistical inputs, not assumed.)
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f) f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  -- Derive the response-mean closeness event from second moments (Chebyshev).
  have : ∀ u, IsProbabilityMeasure (μ u) := hμ
  have hmean :=
    Acharyya2025.RateChain.highProb_uniformResponseMeanClose_of_secondMoment
      μ Xbar μvec σ2 η hint hσ2 hη_pos hratio
  exact queryEfficient_nn_of_response_mean_frob Pf μ hμ hn hd Xbar μvec hB hrank hα_pos hfloor hΛ
    ψFinite hψFinite η R hrate_nonneg hrate_zero hmean hsample_bound
    hpopulation_bound indexOf ψ ψHat hψ hψHat f_ref score Qstar Qsub γ h_lipQ
    h_gamma_pos hXmeas h_cover h_cover_meas hMSE_Q_pos

/-- Fully grounded Quench capstone using the canonical population CMDS
configuration.

This removes the redundant `ψFinite` witness and entrywise Gram proof from
`queryEfficient_nn_of_second_moment`.  The finite target configuration is the
canonical PSD/rank realization, so callers only need to identify their abstract
model embedding with that canonical finite configuration. -/
theorem queryEfficient_nn_of_second_moment_canonical
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Xbar : Nat → Ω → Fin n → Acharyya2024.Mat m p)
    (μvec : Fin n → Acharyya2024.Mat m p)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).rank ≤ d)
    {α Λ : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (hΛ : ∀ l, hB.isHermitian.eigenvalues₀ l ≤ Λ)
    (η R : Nat → Real)
    (hrate_nonneg : ∀ u,
      0 ≤ Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
    (hrate_zero : Filter.Tendsto
      (fun u => (n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
      Filter.atTop (nhds 0))
    (σ2 : Nat → Real)
    (hint : ∀ u (i : Fin n),
      Integrable (fun ω => ‖Xbar u ω i - μvec i‖ ^ 2) (μ u))
    (hσ2 : ∀ u (i : Fin n),
      ∫ ω, ‖Xbar u ω i - μvec i‖ ^ 2 ∂(μ u) ≤ σ2 u)
    (hη_pos : ∀ u, 0 < η u)
    (hratio : Filter.Tendsto
      (fun u => (n : Real) * σ2 u / (η u) ^ 2) Filter.atTop (nhds 0))
    (hsample_bound : ∀ u ω i j,
      |Acharyya2024.responseDist (Xbar u ω) i j| ≤ R u)
    (hpopulation_bound : ∀ u i j,
      |Acharyya2024.responseDist μvec i j| ≤ R u)
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f =
      Acharyya2025.AlignedPipeline.canonicalCMDSConfig
        (Acharyya2024.responseDist μvec) hB hrank (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfigCanonical hd
        (fun u ω => Acharyya2024.responseDist (Xbar u ω))
        (fun u ω =>
          Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar u ω))
        (Acharyya2024.responseDist μvec) hB hrank
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α Λ
          ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u)))
        u ω (indexOf f))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    (hXmeas : ∀ k, Measurable (fun ω => Acharyya2024.responseDist (Xbar k ω)))
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f)
              f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  exact queryEfficient_nn_of_second_moment Pf μ hμ hn hd Xbar μvec hB hrank
    hα_pos hfloor hΛ
    (Acharyya2025.AlignedPipeline.canonicalCMDSConfig
      (Acharyya2024.responseDist μvec) hB hrank)
    (Acharyya2025.AlignedPipeline.canonicalCMDSConfig_gram_eq
      (Acharyya2024.responseDist μvec) hB hrank)
    η R hrate_nonneg hrate_zero σ2 hint hσ2 hη_pos hratio
    hsample_bound hpopulation_bound indexOf ψ ψHat hψ hψHat
    f_ref score Qstar Qsub γ h_lipQ h_gamma_pos hXmeas
    h_cover h_cover_meas hMSE_Q_pos


/-- Fully grounded Quench capstone with both the population CMDS configuration
and the upper spectral ceiling chosen canonically.

The only remaining spectral-size input is the positive lower floor on the
leading `d` eigenvalues.  A separate `Λ` and proof that every eigenvalue lies
below it are eliminated by using the largest population eigenvalue. -/
theorem queryEfficient_nn_of_second_moment_canonical_topEigenvalue
    [DecidableEq Q]
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ k, IsProbabilityMeasure (μ k))
    {n m p d : Nat} (hn : 0 < n) (hd : d ≤ n)
    (Xbar : Nat → Ω → Fin n → Acharyya2024.Mat m p)
    (μvec : Fin n → Acharyya2024.Mat m p)
    (hB : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).PosSemidef)
    (hrank : (Acharyya2025.MathlibBridge.disMatToMatrix
        (Acharyya2025.Deterministic.classicalMDSMatrix
          (Acharyya2024.responseDist μvec))).rank ≤ d)
    {α : Real} (hα_pos : 0 < α)
    (hfloor : ∀ i : Fin (Fintype.card (Fin n)), (i : ℕ) < d →
      α ≤ hB.isHermitian.eigenvalues₀ i)
    (η R : Nat → Real)
    (hrate_nonneg : ∀ u,
      0 ≤ Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
    (hrate_zero : Filter.Tendsto
      (fun u => (n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u))
      Filter.atTop (nhds 0))
    (σ2 : Nat → Real)
    (hint : ∀ u (i : Fin n),
      Integrable (fun ω => ‖Xbar u ω i - μvec i‖ ^ 2) (μ u))
    (hσ2 : ∀ u (i : Fin n),
      ∫ ω, ‖Xbar u ω i - μvec i‖ ^ 2 ∂(μ u) ≤ σ2 u)
    (hη_pos : ∀ u, 0 < η u)
    (hratio : Filter.Tendsto
      (fun u => (n : Real) * σ2 u / (η u) ^ 2) Filter.atTop (nhds 0))
    (hsample_bound : ∀ u ω i j,
      |Acharyya2024.responseDist (Xbar u ω) i j| ≤ R u)
    (hpopulation_bound : ∀ u i j,
      |Acharyya2024.responseDist μvec i j| ≤ R u)
    (indexOf : Model Q X → Fin n)
    (ψ : Model Q X → Vec d)
    (ψHat : Nat → Ω → Model Q X → Vec d)
    (hψ : ∀ f, ψ f =
      Acharyya2025.AlignedPipeline.canonicalCMDSConfig
        (Acharyya2024.responseDist μvec) hB hrank (indexOf f))
    (hψHat : ∀ u ω f, ψHat u ω f =
      Acharyya2025.AlignedPipeline.alignedSpectralConfigCanonical hd
        (fun u ω => Acharyya2024.responseDist (Xbar u ω))
        (fun u ω =>
          Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar u ω))
        (Acharyya2024.responseDist μvec) hB hrank
        (fun u => Acharyya2025.ConfigPerturbation.configBound n d α
          (Acharyya2025.MatrixPerturbation.topEigenvalue hn hB)
          ((n : Real) * Acharyya2025.Bridge.cmdsEntrywiseRate n m (R u) (η u)))
        u ω (indexOf f))
    (f_ref : ∀ k, Ω → Fin k → Model Q X)
    (score : Model Q X → Finset Q → ℝ)
    (Qstar Qsub : Finset Q)
    (γ : ℝ)
    (h_lipQ : ∀ (f f' : Model Q X),
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (h_gamma_pos : 0 < γ)
    (hXmeas : ∀ k, Measurable (fun ω => Acharyya2024.responseDist (Xbar k ω)))
    (h_cover : ∀ ρ > 0,
      _root_.HighProbAtTop μ hμ
        (fun k => {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ}))
    (h_cover_meas : ∀ ρ > 0, ∀ k,
      MeasurableSet {ω | ∀ f, ∃ i, ‖ψ (f_ref k ω i) - ψ f‖ ≤ ρ})
    (hMSE_Q_pos :
      0 < MSE (Q := Q) (X := X) Pf (yFull score Qstar)
        (yQ (Q := Q) (X := X) score Qsub)) :
    ∀ δ : ENNReal, 0 < δ →
      ∃ k : ℕ,
        (μ k) {ω |
          MSE (Q := Q) (X := X) Pf (yFull score Qstar)
            (fun f => yNN_paper (d := d)
              (fun u ω (_ : Finset Q) f => ψHat u ω f)
              f_ref score Qstar Qsub k ω f)
          ≤ MSE (Q := Q) (X := X) Pf (yFull score Qstar)
              (yQ (Q := Q) (X := X) score Qsub)} ≥ 1 - δ := by
  exact queryEfficient_nn_of_second_moment_canonical Pf μ hμ hn hd Xbar μvec
    hB hrank hα_pos hfloor
    (Acharyya2025.MatrixPerturbation.eigenvalues₀_le_topEigenvalue hn hB)
    η R hrate_nonneg hrate_zero σ2 hint hσ2 hη_pos hratio
    hsample_bound hpopulation_bound indexOf ψ ψHat hψ hψHat
    f_ref score Qstar Qsub γ h_lipQ h_gamma_pos hXmeas
    h_cover h_cover_meas hMSE_Q_pos

end DkpsQuench2026
