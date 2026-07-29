/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Spectra.QuantumMechanics.BornRule.POVMCore
import Spectra.QuantumMechanics.BornRule.Mixed
/-!
# Generalized measurements: Born rules and binary POVMs

The core POVM structure, effect calculus, discrete constructor, and the
forgetful map from projection-valued measures live in `POVMCore`.  This file
adds the pure and mixed Born rules and the two-outcome capstone.  Keeping the
core independent of mixed-state/KMS infrastructure allows joint spectral
measure constructions to import only the operator-valued-measure layer.
-/

open MeasureTheory Complex
open scoped InnerProductSpace ENNReal
open Spectra Spectra.ProjValMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [MeasurableSpace ι]
/-! ## §4  The Born rule for POVMs

Identical in form to the PVM Born rule, because that layer only ever touched `diag`. -/

open Spectra

namespace Spectra.QuantumMechanics.BornRule

/-! ### Pure states -/

/-- The **POVM Born measure of a pure state** `ψ`: the carried diagonal measure, exactly as in
the projective case.  `(bornMeasurePOVMPure M ψ) B = ⟪ψ, M(B) ψ⟫` by `inner_effect`. -/
noncomputable def bornMeasurePOVMPure (M : POVM H ι) (ψ : H) : Measure ι :=
  M.diag ψ

/-- For a unit vector this is a probability measure (mass `‖ψ‖² = 1`, by `diag_univ_toReal`). -/
theorem isProbabilityMeasure_bornMeasurePOVMPure (M : POVM H ι) {ψ : H} (hψ : ‖ψ‖ = 1) :
    IsProbabilityMeasure (bornMeasurePOVMPure M ψ) := by
  refine ⟨(ENNReal.toReal_eq_one_iff _).mp ?_⟩
  change ((M.diag ψ) Set.univ).toReal = 1
  rw [M.diag_univ_toReal, hψ, one_pow]

/-- `[done]` **The Born rule, POVM pure form.**  `Prob(B) = ⟪ψ, M(B) ψ⟫`.  Proof:
`M.inner_effect`, with `.re`/`.toReal` bookkeeping (the value is real). -/
theorem bornMeasurePOVMPure_apply (M : POVM H ι) (ψ : H)
    {B : Set ι} (hB : MeasurableSet B) :
    ((bornMeasurePOVMPure M ψ) B).toReal = (⟪ψ, M.effect B hB ψ⟫_ℂ).re := by
  rw [show (bornMeasurePOVMPure M ψ) = M.diag ψ from rfl, M.inner_effect B hB ψ,
    Complex.ofReal_re]

/-! ### Mixed states -/

/-- The **POVM Born measure of a mixed state** `ρ`: the eigenvalue-weighted mixture of the pure
POVM measures — the same `Measure.sum` construction as for PVMs.  This is the `M : POVM H ι`,
`ρ : DensityOperator H ↦ Measure ι` map of the stub. -/
noncomputable def bornMeasurePOVM (M : POVM H ι) (ρ : DensityOperator H) : Measure ι :=
  Measure.sum (fun i => ρ.weight i • M.diag (ρ.state i))

/-- `[done]` A probability measure (mass `∑ pᵢ = 1`). -/
theorem isProbabilityMeasure_bornMeasurePOVM (M : POVM H ι) (ρ : DensityOperator H) :
    IsProbabilityMeasure (bornMeasurePOVM M ρ) := by
  refine ⟨?_⟩
  rw [bornMeasurePOVM, Measure.sum_apply _ MeasurableSet.univ]
  have hone : ∀ i, (ρ.weight i • M.diag (ρ.state i)) Set.univ = ρ.weight i := fun i => by
    rw [Measure.smul_apply, smul_eq_mul]
    have h := M.diag_univ_toReal (ρ.state i)
    rw [ρ.state_unit i, one_pow] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top (M.diag (ρ.state i)) Set.univ), h,
      ENNReal.ofReal_one, mul_one]
  simp only [hone]
  exact ρ.weight_sum

/-- `[done]` **The trace form as a spectral sum**, `Tr(ρ M(B)) = ∑' i, pᵢ ⟪eᵢ, M(B) eᵢ⟫`.
Via `Measure.sum_apply _ hB` and `Measure.smul_apply`. -/
theorem bornMeasurePOVM_apply (M : POVM H ι) (ρ : DensityOperator H)
    {B : Set ι} (hB : MeasurableSet B) :
    (bornMeasurePOVM M ρ) B = ∑' i, ρ.weight i * (M.diag (ρ.state i)) B := by
  rw [bornMeasurePOVM, Measure.sum_apply _ hB]
  simp only [Measure.smul_apply, smul_eq_mul]

/-- `[done]` The pure case reduces to `bornMeasurePOVMPure`. -/
theorem bornMeasurePOVM_pure (M : POVM H ι) {ψ : H} (hψ : ‖ψ‖ = 1) :
    bornMeasurePOVM M (DensityOperator.pure hψ) = bornMeasurePOVMPure M ψ := by
  refine Measure.ext fun B hB => ?_
  rw [bornMeasurePOVM_apply M _ hB]
  simp only [DensityOperator.pure, ite_mul, one_mul, zero_mul, tsum_ite_eq, bornMeasurePOVMPure]

/-- `[done]` **`Tr(ρ M(B))`, literal**, through the `toState` bridge of `Mixed.lean`: the normal
state evaluated on the effect equals the POVM Born probability.  Proof: `toStateCLM_apply`,
`M.inner_effect` termwise, then `bornMeasurePOVM_apply` — the exact analogue of `toState_proj_eq`
with `inner_effect` in place of `inner_proj`. -/
theorem toState_effect_eq (M : POVM H ι) (ρ : DensityOperator H)
    {B : Set ι} (hB : MeasurableSet B) :
    (ρ.toStateCLM (M.effect B hB)).re = ((bornMeasurePOVM M ρ) B).toReal := by
  have hrhs : ((bornMeasurePOVM M ρ) B).toReal
      = ∑' i, (ρ.weight i).toReal * ((M.diag (ρ.state i)) B).toReal := by
    rw [bornMeasurePOVM_apply M ρ hB]
    have hfin : ∀ i, ρ.weight i * (M.diag (ρ.state i)) B ≠ ⊤ := fun i =>
      ENNReal.mul_ne_top
        (lt_of_le_of_lt (ρ.weight_sum ▸ ENNReal.le_tsum i) ENNReal.one_lt_top).ne
        (measure_ne_top _ _)
    rw [ENNReal.tsum_toReal_eq hfin]
    exact tsum_congr fun i => ENNReal.toReal_mul
  rw [hrhs, DensityOperator.toStateCLM_apply]
  have key : ∀ i, (ρ.weight i).toReal • ⟪ρ.state i, M.effect B hB (ρ.state i)⟫_ℂ
      = ((ρ.weight i).toReal * ((M.diag (ρ.state i)) B).toReal : ℝ) := fun i => by
    rw [M.inner_effect B hB (ρ.state i), Complex.real_smul, ← Complex.ofReal_mul]
  simp_rw [key]
  rw [← Complex.ofReal_tsum]
  exact Complex.ofReal_re _

/-- `[done]` **Consistency with the projective Born rule.**  For a `ProjValMeasure`, its POVM
Born measure is its PVM Born measure: `toPOVM` only forgets `proj_inter`, which the measure never
used.  Proof: both are `Measure.sum` of the same `P.diag`s (`toPOVM_diag`). -/
theorem bornMeasurePOVM_toPOVM (P : ProjValMeasure H) (ρ : DensityOperator H) :
    bornMeasurePOVM P.toPOVM ρ = bornMeasureMixed P ρ := rfl

/-! ## §5  Capstone: the two-outcome measurement

The simplest non-trivial POVM, and the one every yes/no test and state-discrimination problem
reduces to: an effect `E` with `0 ≤ E ≤ 1` is precisely a binary measurement — `E` the "yes"
effect, its complement `1 - E` the "no" effect.  `binaryPOVM` builds it on `Bool`, and it ties the
three strands of the file together:

* the **effect calculus** of §1 — `1 - E` is again an effect *exactly because* `E ≤ 1` in the
  Loewner order (`ContinuousLinearMap.le_def`, which makes `E ≤ 1` definitionally
  `(1 - E).IsPositive`);
* the **constructor** `ofEffects` of §2, applied to the two-element family `{E, 1 - E}` whose sum
  is the identity;
* the **Born rule** of §4 — the outcome probabilities are `⟪ψ, E ψ⟫` and `⟪ψ, (1 - E) ψ⟫`, which
  for a unit vector sum to one (`isProbabilityMeasure_bornMeasurePOVMPure`).

So an effect is *literally* a yes-probability operator: `binaryPOVM_bornPure_true` reads
`P(yes) = ⟪ψ, E ψ⟫`. -/

/-- The two-element effect family of a binary measurement: `true` ("yes") carries `E`, `false`
("no") its complement `1 - E`.  Shared by `binaryPOVM` and its `@[simp]` effect lemmas. -/
private abbrev binaryEffect (E : H →L[ℂ] H) : Bool → (H →L[ℂ] H) := fun b => bif b then E else 1 - E

/-- The **two-outcome POVM** of an effect `0 ≤ E ≤ 1`: outcome `true` ("yes") carries the effect
`E`, outcome `false` ("no") its complement `1 - E`. -/
noncomputable def binaryPOVM (E : H →L[ℂ] H) (hE : E.IsPositive) (hE1 : E ≤ 1) :
    POVM H Bool :=
  POVM.ofEffects (binaryEffect E)
    (fun b => by cases b with
      | true => exact hE
      | false => exact (ContinuousLinearMap.le_def E 1).mp hE1)
    (by
      rw [(hasSum_fintype (binaryEffect E)).tsum_eq, Fintype.sum_bool]
      simp)

/-- The "yes" effect of `binaryPOVM` is `E` itself. -/
@[simp] lemma binaryPOVM_effect_true (E : H →L[ℂ] H) (hE : E.IsPositive) (hE1 : E ≤ 1) :
    (binaryPOVM E hE hE1).effect {true} (measurableSet_singleton true) = E := by
  rw [binaryPOVM, POVM.ofEffects_effect,
    (hasSum_fintype (fun b : Bool => Set.indicator {true} (binaryEffect E) b)).tsum_eq,
    Fintype.sum_bool]
  simp

/-- The "no" effect of `binaryPOVM` is the complement `1 - E`. -/
@[simp] lemma binaryPOVM_effect_false (E : H →L[ℂ] H) (hE : E.IsPositive) (hE1 : E ≤ 1) :
    (binaryPOVM E hE hE1).effect {false} (measurableSet_singleton false) = 1 - E := by
  rw [binaryPOVM, POVM.ofEffects_effect,
    (hasSum_fintype (fun b : Bool => Set.indicator {false} (binaryEffect E) b)).tsum_eq,
    Fintype.sum_bool]
  simp

/-- **The yes-probability is `⟪ψ, E ψ⟫`.**  The Born probability that `binaryPOVM E` returns `true`
in state `ψ` is exactly the diagonal matrix element of the effect — an effect *is* a yes-probability
operator.  (Effect order ⟹ constructor ⟹ Born rule, in one line.) -/
theorem binaryPOVM_bornPure_true (E : H →L[ℂ] H) (hE : E.IsPositive) (hE1 : E ≤ 1) (ψ : H) :
    ((bornMeasurePOVMPure (binaryPOVM E hE hE1) ψ) {true}).toReal = (⟪ψ, E ψ⟫_ℂ).re := by
  rw [bornMeasurePOVMPure_apply (binaryPOVM E hE hE1) ψ (measurableSet_singleton true),
    binaryPOVM_effect_true]

/-- The complementary "no" probability is `⟪ψ, (1 - E) ψ⟫`. -/
theorem binaryPOVM_bornPure_false (E : H →L[ℂ] H) (hE : E.IsPositive) (hE1 : E ≤ 1) (ψ : H) :
    ((bornMeasurePOVMPure (binaryPOVM E hE hE1) ψ) {false}).toReal = (⟪ψ, (1 - E) ψ⟫_ℂ).re := by
  rw [bornMeasurePOVMPure_apply (binaryPOVM E hE hE1) ψ (measurableSet_singleton false),
    binaryPOVM_effect_false]

/-! ## §6  Flags

`[optional refactor — no new infra]`  **Factor the Born layer through `diag`.**  Every Born-rule
declaration in `Mixed.lean` and here depends only on the `diag : H → Measure ·` field and the mass
lemma — never on `proj_inter`, `effect_univ`, or the operators.  A typeclass
```
class HasDiagonalMeasure (F : Type*) (H ι) where
  diag : F → H → Measure ι
  diag_finite : …
  diag_univ : ((diag f ξ) univ).toReal = ‖ξ‖²
```
with `ProjValMeasure` and `POVM` instances would let `bornMeasure`, `bornMeasureMixed`,
`isProbabilityMeasure_*`, and `*_apply` be stated and proved **once**.  Pure refactor; recommended
only if a third carrier appears.

`[done — discrete case, in `Naimark.lean`]`  **Naimark's theorem.**  Every POVM `M` on `H` is the
compression of a PVM `P` on a larger space `K`: `M.effect B = V⋆ ∘ P.proj B ∘ V` for an isometry
`V : H → K`.  This is the structural theorem justifying "generalized measurement," and the bridge by
which POVM results reduce to projective ones.

The **discrete / countable** case is proved completely in
`QuantumMechanics/BornRule/Naimark.lean` as `naimark_dilation`: for a resolution of the identity
`E : κ → (H →L[ℂ] H)`, `∑' k, E k = 1` (i.e. an `ofEffects` POVM), with carrier
`NaimarkSpace H κ = lp (fun _ : κ => H) 2`, isometry `naimarkV : ψ ↦ (√Eₖ ψ)ₖ` (operator square
root `CFC.sqrt`), and the diagonal PVM `naimarkPVM : ProjValMeasure' (NaimarkSpace H κ) κ`.  This
covers every `ofEffects`/`binaryPOVM` measurement.  The dilating PVM lives in the general
`Spectra.ProjValMeasure'` (`ProjValMeasure/General.lean`) — a PVM over an arbitrary Hilbert space
and outcome space, i.e. `POVM` + the `proj_inter` field.

(Aside: there is **no** Stinespring/Naimark/CP-dilation existence theorem in Mathlib, and the
`Bochner.GNS` stack here is specialized to positive-definite functions `ℝ → ℂ` for Stone's theorem,
so neither shortcuts this — the discrete dilation is the bespoke ℓ²-direct-sum construction.)

`[needs infra: operator-valued-measure topology]`  The fully general σ-additive Naimark theorem,
for an *uncountable* outcome space `ι` with a non-atomic POVM, remains open: it needs a topology on
operator-valued measures that the library deliberately avoids.

`[needs InformationGeometry.StatisticalModel API]`  **The weld, quantum-estimation form.**  A POVM
`M` turns a state `ρ` into the classical model `bornMeasurePOVM M ρ`; ranging over `M` is the
*measurement-choice* in quantum estimation.  The quantum Cramér–Rao bound
(`CramerRao.Quantum`) is the optimization of the classical Fisher information of
`θ ↦ bornMeasurePOVM M ρ_θ` over all POVMs `M`, bounded by the quantum Fisher information.  The map
`(M, ρ) ↦ bornMeasurePOVM M ρ` is the object that optimization is taken over.
-/

end Spectra.QuantumMechanics.BornRule
