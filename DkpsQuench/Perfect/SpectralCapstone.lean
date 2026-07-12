/-
Quench capstones with probabilistic spectral regularity.

These theorems are the structural bridge between the existing proved growing
CMDS argument and the new covariance/spectral scaffold.  They differ from the
production theorem only in one essential way: eigenvalue floor and ceiling
conditions are allowed to hold on a measurable high-probability subevent rather
than for every random reference sample.
-/

import DkpsQuench.Perfect.RateSchedule

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

namespace DkpsQuench.Perfect

open Acharyya2024
open Acharyya2025.Bridge
open Acharyya2025.Deterministic
open Acharyya2025.MathlibBridge
open Acharyya2025.ConfigPerturbation
open Acharyya2025.GrowingPipeline
open Acharyya2025.GrowingResponse
open DkpsQuench.GrowingAcharyyaBridge
open DkpsQuench.GrowingResponseBridge

universe u v w

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ω : Type w} [MeasurableSpace Ω]

/-- Growing target-augmented Quench with a high-probability spectral
certificate.

Proof plan for a weaker agent:

1. copy the proof skeleton of
   `highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds`;
2. replace its event `E ∩ {good n}` by the triple intersection of the CMDS
   entry event, `Hspectral.event`, and the deterministic rate event;
3. obtain the local floor and ceiling from `Hspectral.floor` and
   `Hspectral.ceiling_bound` at the current outcome;
4. use the existing bespoke pairwise-distance theorem unchanged;
5. finish with the same radial tie-average and iid coverage theorem.

Completing this theorem removes global `hfloor` and `hceiling` premises from all
later capstones.  Do not add them back as hidden fields.

Implementation recipe (execute in this order):
1. Open the proved theorem
   `highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds` side-by-side
   and copy its local definitions for the deterministic good-rate event, CMDS
   configuration error bound, and nearest-neighbor radius.
2. Define the new witness event as
   `E n ∩ Hspectral.event n ∩ rateEvent n`; prove measurability from `hEmeas`,
   `Hspectral.measurable`, and measurability of the deterministic event.
3. Prove the intersection is high probability using `HighProbAtTop.inter`
   twice, `hE`, `Hspectral.highProb`, and the eventual deterministic rate facts
   from `Hrate.eventually_all`.
4. Inside the event, obtain entrywise CMDS closeness from `hEsub`, local spectral
   floor from `Hspectral.floor`, and local ceiling from
   `Hspectral.ceiling_bound`.
5. Feed those local facts into the same existing bespoke
   `abs_pairwiseDistance_spectralConfig_sub_le_two_configBound` invocation used
   by the production theorem; do not replace that lemma here.
6. Use `hzGram` and `hzRadial` exactly as in the production proof to convert the
   configuration error to target/reference perspective-distance error.
7. Finish with the existing iid finite-net coverage and tie-average MSE theorem;
   the final event inclusion should be identical modulo the extra spectral
   conjunct.
8. Keep all global `hfloor`/`hceiling` arguments deleted.  If the copied theorem
   requires them positionally, inline its proof rather than calling it.
-/
theorem highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds_spectralSubevents
    {d : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψmeas : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (Dhat D : ∀ n, Ω → Model Q X → DisMat (n + 1))
    (hsym : ∀ n ω f,
      (disMatToMatrix (classicalMDSMatrix (Dhat n ω f))).IsHermitian)
    (z : ∀ n, Ω → Model Q X → Config (n + 1) d)
    (hzGram : ∀ n ω f i j,
      (∑ k, z n ω f i k * z n ω f j k) =
        classicalMDSMatrix (D n ω f) i j)
    (hzRadial : ∀ n ω f (i : Fin n),
      ‖z n ω f i.castSucc - z n ω f (Fin.last n)‖ =
        ‖ψ (f_ref n ω i) - ψ f‖)
    {α : Real} (hα : 0 < α)
    (ceiling entryRate : Nat → Real)
    (Hspectral : GrowingSpectralSubevents μ hμ D z hzGram α ceiling)
    (Hrate : GrowingConfigControl (fun n => n + 1) d α ceiling entryRate)
    (E : Nat → Set Ω)
    (hEmeas : ∀ n, MeasurableSet (E n))
    (hEsub : ∀ n, E n ⊆ {ω | ∀ f,
      EntrywiseClose
        (classicalMDSMatrix (Dhat n ω f))
        (classicalMDSMatrix (D n ω f)) (entryRate n)})
    (hE : HighProbAtTop μ hμ E)
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (γ : Real)
    (hlip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => yNNTieAverage_augmentedCMDS (d := d)
        Dhat hsym f_ref score Qstar n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  let good : Nat → Prop := fun n =>
    d ≤ n + 1 ∧
    ((n + 1 : Nat) : Real) * entryRate n ≤ α / 2 ∧
    (d : Real) *
      (4 * ((n + 1 : Nat) : Real) *
        ((((n + 1 : Nat) : Real) * entryRate n)^2) / α^2) ≤ 1 / 2 ∧
    configBound (n + 1) d α (ceiling n)
      (((n + 1 : Nat) : Real) * entryRate n) ≤ Hrate.bound n
  let Es : Nat → Set Ω := fun n => E n ∩ Hspectral.event n
  let Eg : Nat → Set Ω := fun n => Es n ∩ {ω | good n}
  have hgood : ∀ᶠ n in atTop, good n := by
    filter_upwards [eventually_dimension_le_succ d, Hrate.eventually_all]
      with n hdim hsides
    exact ⟨hdim, hsides.1, hsides.2.1, hsides.2.2⟩
  have hEsMeas : ∀ n, MeasurableSet (Es n) := by
    intro n
    exact (hEmeas n).inter (Hspectral.measurable n)
  have hEs : HighProbAtTop μ hμ Es := by
    exact HighProbAtTop.inter hE Hspectral.highProb hEmeas Hspectral.measurable
  have hEgMeas : ∀ n, MeasurableSet (Eg n) := by
    intro n
    by_cases hn : good n
    · simp [Eg, hn, hEsMeas n]
    · simp [Eg, hn]
  have hEg : HighProbAtTop μ hμ Eg := by
    apply hEs.mono_eventually
    filter_upwards [hgood] with n hn
    intro ω hω
    exact ⟨hω, hn⟩
  let radialRate : Nat → Real := fun n => 2 * Hrate.bound n
  have hradialRateZero : Tendsto radialRate atTop (nhds 0) := by
    dsimp [radialRate]
    simpa using tendsto_const_nhds.mul Hrate.bound_zero
  have hradialRateNonneg : ∀ n, 0 ≤ radialRate n := by
    intro n
    dsimp [radialRate]
    exact mul_nonneg (by norm_num) (Hrate.bound_nonneg n)
  have hEgSub : ∀ n, Eg n ⊆ {ω | ∀ f i,
      |augmentedSpectralRadialDistance (d := d) Dhat hsym n ω f i -
          ‖ψ (f_ref n ω i) - ψ f‖| ≤ radialRate n} := by
    intro n ω hω f i
    rcases hω with ⟨⟨hentryEvent, hspectralEvent⟩, hdim, hsmall, hpolar, hbound⟩
    have hentry := hEsub n hentryEvent f
    have hfloor := Hspectral.floor n ω hspectralEvent f
    have hceiling := Hspectral.ceiling_bound n ω hspectralEvent f
    have hpair :=
      abs_pairwiseDistance_spectralConfig_sub_le_two_configBound
        hdim
        (disMatToMatrix (classicalMDSMatrix (D n ω f)))
        (disMatToMatrix (classicalMDSMatrix (Dhat n ω f)))
        (populationPosSemidefOfGram D z hzGram n ω f)
        (hsym n ω f)
        (populationRankLeOfGram D z hzGram n ω f)
        hα (Hrate.entry_nonneg n) hfloor hceiling
        hentry hsmall hpolar (z n ω f) (hzGram n ω f)
        i.castSucc (Fin.last n)
    have hraw : rawAugmentedSpectralConfig (d := d) Dhat hsym n ω f =
        spectralConfig
          (Matrix.toEuclideanLin
            (disMatToMatrix (classicalMDSMatrix (Dhat n ω f))))
          (Acharyya2025.MatrixPerturbation.opSym (hsym n ω f)) hdim :=
      rawAugmentedSpectralConfig_of_dimension Dhat hsym n ω f hdim
    change
      |‖rawAugmentedSpectralConfig (d := d) Dhat hsym n ω f i.castSucc -
            rawAugmentedSpectralConfig (d := d) Dhat hsym n ω f (Fin.last n)‖ -
          ‖ψ (f_ref n ω i) - ψ f‖| ≤ 2 * Hrate.bound n
    rw [hraw, ← hzRadial n ω f i]
    exact hpair.trans (mul_le_mul_of_nonneg_left hbound (by norm_num))
  exact highProbQQueryEfficient_radialTieAverage_of_compact_iid_fullSupport
    Pf μ hμ ψ hψmeas hcompact hfull
    (augmentedSpectralRadialDistance (d := d) Dhat hsym)
    f_ref hiid score Qstar Qsub γ hlip hγ
    radialRate hradialRateZero hradialRateNonneg
    Eg hEgMeas hEgSub hEg hbase

/-- Response-mean capstone with population geometry reduced to one distance
realization and spectral assumptions reduced to a high-probability certificate.

After the population-geometry and spectral-regularity modules are complete,
callers no longer provide `z`, a Gram proof, a radial proof, positive
semidefiniteness, rank, or global eigenvalue bounds.  This theorem is the direct
entry point for both raw finite-model and raw infinite-model response theorems.

Implementation recipe (execute in this order):
1. Define `Dhat := augmentedSampleResponseDist Xbar` and
   `D := fun n ω f => responseDist (μbar n ω f)`.
2. Define the CMDS entry rate exactly as in the theorem statement and obtain the
   entrywise CMDS event inclusion from
   `cmdsEntrywise_of_responseMeanClose_of_population_norm` (or the corresponding
   theorem in `GrowingResponseBridge`) using `hpopulationNorm`, `hηNonneg`, and
   the response-mean event.
3. Prove Hermitian symmetry of `Dhat` with
   `Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist`.
4. Use `centeredAugmentedPerspectiveConfig_gram_eq` and
   `centeredAugmentedPerspectiveConfig_radial` for the population geometry.
5. Invoke
   `highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds_spectralSubevents`
   with `E := augmentedUniformResponseMeanEvent Xbar μbar η`,
   `hEmeas := hmeanMeas`, and `hE := hmean`.
6. Use named arguments for `ceiling`, `entryRate`, `Hspectral`, and `Hrate`; this
   call has many same-typed arguments and positional application is fragile.
7. Finish by `simpa` after unfolding only `Dhat` and the estimator.  No new
   probability or spectral proof belongs here.
-/
theorem highProbQQueryEfficient_tieAverage_of_response_mean_realization_spectralSubevents
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψmeas : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (Xbar μbar : ∀ n, Ω → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (η B : Nat → Real)
    (hηNonneg : ∀ n, 0 ≤ η n)
    (hmeanMeas : ∀ n,
      MeasurableSet (augmentedUniformResponseMeanEvent Xbar μbar η n))
    (hmean : HighProbAtTop μ hμ
      (augmentedUniformResponseMeanEvent Xbar μbar η))
    (hpopulationNorm : ∀ n ω f i, ‖μbar n ω f i‖ ≤ B n)
    (hrealize : PerspectiveResponseRealization ψ f_ref μbar)
    {α : Real} (hα : 0 < α)
    (ceiling : Nat → Real)
    (Hspectral : GrowingSpectralSubevents μ hμ
      (fun n ω f => responseDist (μbar n ω f))
      (centeredAugmentedPerspectiveConfig ψ f_ref)
      (centeredAugmentedPerspectiveConfig_gram_eq
        ψ f_ref μbar hrealize)
      α ceiling)
    (Hrate : GrowingConfigControl (fun n => n + 1) d α ceiling
      (fun n => cmdsEntrywiseRate (n + 1) m
        (responseDistBound m (B n + η n)) (η n)))
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (γ : Real)
    (hlip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => yNNTieAverage_augmentedCMDS (d := d)
        (augmentedSampleResponseDist Xbar)
        (fun n ω f =>
          Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar n ω f))
        f_ref score Qstar n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  let Dhat : ∀ n, Ω → Model Q X → DisMat (n + 1) :=
    augmentedSampleResponseDist Xbar
  let D : ∀ n, Ω → Model Q X → DisMat (n + 1) :=
    fun n ω f => responseDist (μbar n ω f)
  let E : Nat → Set Ω := augmentedUniformResponseMeanEvent Xbar μbar η
  have hEsub : ∀ n, E n ⊆ {ω | ∀ f,
      EntrywiseClose
        (classicalMDSMatrix (Dhat n ω f))
        (classicalMDSMatrix (D n ω f))
        (cmdsEntrywiseRate (n + 1) m
          (responseDistBound m (B n + η n)) (η n))} := by
    intro n ω hω f
    simpa [Dhat, D, augmentedSampleResponseDist] using
      cmdsEntrywise_of_responseMeanClose_of_population_norm (by omega)
        (Xbar n ω f) (μbar n ω f) (hηNonneg n) (hω f)
        (hpopulationNorm n ω f)
  exact highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds_spectralSubevents
    (Pf := Pf) (μ := μ) (hμ := hμ)
    (ψ := ψ) (hψmeas := hψmeas) (hcompact := hcompact) (hfull := hfull)
    (f_ref := f_ref) (hiid := hiid)
    (Dhat := Dhat) (D := D)
    (hsym := fun n ω f =>
      Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
        (Xbar n ω f))
    (z := centeredAugmentedPerspectiveConfig ψ f_ref)
    (hzGram := centeredAugmentedPerspectiveConfig_gram_eq ψ f_ref μbar hrealize)
    (hzRadial := centeredAugmentedPerspectiveConfig_radial ψ f_ref)
    (hα := hα) (ceiling := ceiling)
    (entryRate := fun n => cmdsEntrywiseRate (n + 1) m
      (responseDistBound m (B n + η n)) (η n))
    (Hspectral := Hspectral) (Hrate := Hrate)
    (E := E) (hEmeas := hmeanMeas) (hEsub := hEsub) (hE := hmean)
    (score := score) (Qstar := Qstar) (Qsub := Qsub)
    (γ := γ) (hlip := hlip) (hγ := hγ) (hbase := hbase)

/-- Infinite-class-compatible response capstone using measurable response
subevents rather than measurability of the universal response event.

The proof should intersect `Hmean.event` with `Hspectral.event` and use
`Hmean.subset` only after entering the event.  Once complete, this is the sole
spectral/response theorem needed by both final Perfect Quench capstones.

Implementation recipe (execute in this order):
1. Use the internal event `Hmean.event`; its measurability and high-probability
   fields are already available.
2. For `hEsub`, compose `Hmean.subset n` with the deterministic theorem that
   turns augmented response-mean closeness and `hpopulationNorm` into CMDS
   entrywise closeness at the stated `cmdsEntrywiseRate`.
3. Define `Dhat` and `D` as in the preceding response-mean theorem and obtain
   Hermitian symmetry from the response-distance helper.
4. Invoke
   `highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds_spectralSubevents`
   with `E := Hmean.event`, `hEmeas := Hmean.measurable`, and
   `hE := Hmean.highProb`.
5. Supply the centered configuration Gram/radial lemmas from the realization
   hypothesis and the supplied spectral/rate certificates.
6. Use named arguments and finish by `simpa`.  Do not try to prove measurability
   of the universal response event; `Hmean.event` exists specifically to avoid
   that obligation.
-/
theorem highProbQQueryEfficient_tieAverage_of_responseSubevents_realization_spectralSubevents
    {d m p : Nat}
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μ : Nat → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (ψ : Model Q X → Vec d) (hψmeas : Measurable ψ)
    (hcompact : IsCompact (Set.range ψ))
    (hfull : PerspectiveFullSupport Pf ψ)
    (f_ref : ∀ n, Ω → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μ f_ref)
    (Xbar μbar : ∀ n, Ω → Model Q X → Fin (n + 1) → Acharyya2024.Mat m p)
    (η B : Nat → Real)
    (hηNonneg : ∀ n, 0 ≤ η n)
    (Hmean : AugmentedResponseMeanSubevents μ hμ Xbar μbar η)
    (hpopulationNorm : ∀ n ω f i, ‖μbar n ω f i‖ ≤ B n)
    (hrealize : PerspectiveResponseRealization ψ f_ref μbar)
    {α : Real} (hα : 0 < α)
    (ceiling : Nat → Real)
    (Hspectral : GrowingSpectralSubevents μ hμ
      (fun n ω f => responseDist (μbar n ω f))
      (centeredAugmentedPerspectiveConfig ψ f_ref)
      (centeredAugmentedPerspectiveConfig_gram_eq
        ψ f_ref μbar hrealize)
      α ceiling)
    (Hrate : GrowingConfigControl (fun n => n + 1) d α ceiling
      (fun n => cmdsEntrywiseRate (n + 1) m
        (responseDistBound m (B n + η n)) (η n)))
    (score : Model Q X → Finset Q → Real)
    (Qstar Qsub : Finset Q)
    (γ : Real)
    (hlip : ∀ f f',
      |score f Qstar - score f' Qstar| ≤ γ * ‖ψ f - ψ f'‖)
    (hγ : 0 < γ)
    (hbase : 0 < MSE Pf (yFull score Qstar) (yQ score Qsub)) :
    HighProbQQueryEfficient (Q := Q) (X := X) μ hμ Pf sqLoss
      (yFull score Qstar)
      (fun n ω f => yNNTieAverage_augmentedCMDS (d := d)
        (augmentedSampleResponseDist Xbar)
        (fun n ω f =>
          Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
            (Xbar n ω f))
        f_ref score Qstar n ω f)
      (fun _ _ f => yQ score Qsub f) := by
  let Dhat : ∀ n, Ω → Model Q X → DisMat (n + 1) :=
    augmentedSampleResponseDist Xbar
  let D : ∀ n, Ω → Model Q X → DisMat (n + 1) :=
    fun n ω f => responseDist (μbar n ω f)
  have hEsub : ∀ n, Hmean.event n ⊆ {ω | ∀ f,
      EntrywiseClose
        (classicalMDSMatrix (Dhat n ω f))
        (classicalMDSMatrix (D n ω f))
        (cmdsEntrywiseRate (n + 1) m
          (responseDistBound m (B n + η n)) (η n))} := by
    intro n ω hω f
    have hmean := Hmean.subset n hω f
    simpa [Dhat, D, augmentedSampleResponseDist] using
      cmdsEntrywise_of_responseMeanClose_of_population_norm (by omega)
        (Xbar n ω f) (μbar n ω f) (hηNonneg n) hmean
        (hpopulationNorm n ω f)
  exact highProbQQueryEfficient_tieAverage_of_growing_augmented_cmds_spectralSubevents
    (Pf := Pf) (μ := μ) (hμ := hμ)
    (ψ := ψ) (hψmeas := hψmeas) (hcompact := hcompact) (hfull := hfull)
    (f_ref := f_ref) (hiid := hiid)
    (Dhat := Dhat) (D := D)
    (hsym := fun n ω f =>
      Acharyya2025.AlignedPipeline.isHermitian_disMatToMatrix_classicalMDSMatrix_responseDist
        (Xbar n ω f))
    (z := centeredAugmentedPerspectiveConfig ψ f_ref)
    (hzGram := centeredAugmentedPerspectiveConfig_gram_eq ψ f_ref μbar hrealize)
    (hzRadial := centeredAugmentedPerspectiveConfig_radial ψ f_ref)
    (hα := hα) (ceiling := ceiling)
    (entryRate := fun n => cmdsEntrywiseRate (n + 1) m
      (responseDistBound m (B n + η n)) (η n))
    (Hspectral := Hspectral) (Hrate := Hrate)
    (E := Hmean.event) (hEmeas := Hmean.measurable)
    (hEsub := hEsub) (hE := Hmean.highProb)
    (score := score) (Qstar := Qstar) (Qsub := Qsub)
    (γ := γ) (hlip := hlip) (hγ := hγ) (hbase := hbase)

end DkpsQuench.Perfect
