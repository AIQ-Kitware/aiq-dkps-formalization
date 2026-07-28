/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.ApproximationNumbers.Core
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
import DavisKahan.OperatorIdeal.ApproximationNumbers.Real
import ForTauCeti.Analysis.OperatorIdeal.Family.Basic

/-!
# Scalar-generic approximation-number endpoints and ideal families

This public module assembles the lower approximation-number foundation with
its complex and real analytic endpoints. The scalar-generic endpoint wrappers
and the downstream Ky Fan dominant ideal families live here, above both
scalar-specific implementations, avoiding the former real-proof import cycle.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
open scoped ENNReal
open Filter

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Analytic capability asserting strong-cutoff convergence for approximation
numbers over a scalar field.  This is separated from `RCLike`: the latter is
an open algebraic typeclass, while this property is currently established for
the standard real and complex scalar fields. -/
class HasApproximationNumberStrongCutoff
    (𝕜 : Type u) [RCLike 𝕜] : Prop where
  tendsto_comp_strongProjection :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι},
      (∀ i, IsOrthogonalProjectionMap (P i)) →
      StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E) →
      ∀ (n : ℕ) (K : E →L[𝕜] F),
        Tendsto
          (fun i => approximationSingularValue n (K ∘L P i))
          l (𝓝 (approximationSingularValue n K))

/-- Analytic capability asserting the finite Ky Fan triangle inequality over
a scalar field. -/
class HasKyFanApproximationGaugeTriangle
    (𝕜 : Type u) [RCLike 𝕜] : Prop where
  add_le :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (k : ℕ) (K L : E →L[𝕜] F),
      kyFanApproximationGauge k (K + L) ≤
        kyFanApproximationGauge k K + kyFanApproximationGauge k L

instance realHasApproximationNumberStrongCutoff :
    HasApproximationNumberStrongCutoff.{0, v, w} ℝ where
  tendsto_comp_strongProjection :=
    ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real

instance complexHasApproximationNumberStrongCutoff :
    HasApproximationNumberStrongCutoff.{0, v, w} ℂ where
  tendsto_comp_strongProjection :=
    approximationSingularValue_comp_strongProjection_tendsto_complex

instance realHasKyFanApproximationGaugeTriangle :
    HasKyFanApproximationGaugeTriangle.{0, v} ℝ where
  add_le := ApproximationNumbersReal.kyFanApproximationGauge_add_le_real

instance complexHasKyFanApproximationGaugeTriangle :
    HasKyFanApproximationGaugeTriangle.{0, v} ℂ where
  add_le := kyFanApproximationGauge_add_le_complex

/-- Real-Hilbert-space continuity of approximation numbers under strongly
convergent orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_real
    {ER FR : Type v}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]
    {ι : Type w} {P : ι → ER →L[ℝ] ER} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ ER))
    (n : ℕ) (K : ER →L[ℝ] FR) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real
    hPproj hP n K

/-- Real-Hilbert-space finite Ky Fan convergence under strongly convergent
orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_real
    {ER FR : Type v}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]
    {ι : Type w} {P : ι → ER →L[ℝ] ER} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ ER))
    (k : ℕ) (K : ER →L[ℝ] FR) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) :=
  ApproximationNumbersReal.kyFanApproximationGauge_comp_strongProjection_tendsto_real
    hPproj hP k K

/-- Real-Hilbert-space infinite-dimensional Ky Fan triangle inequality. -/
theorem kyFanApproximationGauge_add_le_real
    {ER FR : Type v}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [CompleteSpace ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [CompleteSpace FR]
    (k : ℕ) (K L : ER →L[ℝ] FR) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L :=
  ApproximationNumbersReal.kyFanApproximationGauge_add_le_real k K L

/-- Continuity of each approximation number under strongly convergent
orthogonal cutoffs. -/
theorem approximationSingularValue_comp_strongProjection_tendsto
    [HasApproximationNumberStrongCutoff.{u, v, w} 𝕜]
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (n : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  HasApproximationNumberStrongCutoff.tendsto_comp_strongProjection
    (𝕜 := 𝕜) hPproj hP n K

/-- Ky Fan's addition inequality for approximation numbers. -/
theorem kyFanApproximationGauge_add_le
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (k : ℕ) (K L : E →L[𝕜] F) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L :=
  HasKyFanApproximationGaugeTriangle.add_le (𝕜 := 𝕜) k K L


/-- Ky Fan gauges converge under strong orthogonal cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto
    [HasApproximationNumberStrongCutoff.{u, v, w} 𝕜]
    {ι : Type w} {P : ι → E →L[𝕜] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id 𝕜 E))
    (k : ℕ) (K : E →L[𝕜] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  simp only [kyFanApproximationGauge]
  exact tendsto_finsetSum (Finset.range k)
    (fun n hn => approximationSingularValue_comp_strongProjection_tendsto
      hPproj hP n K)

/-! ### The finite Ky Fan gauges as a canonical ideal family -/

/-- The finite Ky Fan gauge `∑_{n < k} aₙ` as a **canonical** symmetric operator
ideal family (`TauCeti.SymmetricOperatorIdealFamily`).

The gauge is `ENNReal.ofReal` of `kyFanApproximationGauge k`, so it is finite
everywhere — every bounded operator is a member
(`carrier_kyFanSymmetricIdealFamily`) — and the four ideal laws are the
real-valued ones transported along `ENNReal.ofReal`.  Only one of them,
subadditivity, is mathematics rather than bookkeeping; it arrives through the
`HasKyFanApproximationGaugeTriangle` capability class.

`hk : 0 < k` is needed for exactly one law: `enorm_le_gauge`.  At `k = 0` the
gauge is identically `0`, which satisfies the other three but is not a norm.

**Intended destination.**  This belongs beside `TauCeti.operatorNormFamily` in
`ForTauCeti/Analysis/OperatorIdeal/Family/`.  It cannot live there yet, because
both `kyFanApproximationGauge` and the capability class supplying its triangle
inequality are defined in this library; it moves when the approximation-number
layer is extracted. -/
noncomputable def kyFanSymmetricIdealFamily
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜] (k : ℕ) (hk : 0 < k) :
    TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge A := ENNReal.ofReal (kyFanApproximationGauge k A)
  gauge_add_le A B := by
    rw [← ENNReal.ofReal_add (kyFanApproximationGauge_nonneg k A)
      (kyFanApproximationGauge_nonneg k B)]
    exact ENNReal.ofReal_le_ofReal (kyFanApproximationGauge_add_le k A B)
  gauge_smul c A := by
    rw [kyFanApproximationGauge_smul, ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm]
  enorm_le_gauge A := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (opNorm_le_kyFanApproximationGauge hk A)
  gauge_comp_le L A R := by
    rw [← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg L),
      ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg L) (kyFanApproximationGauge_nonneg k A))]
    exact ENNReal.ofReal_le_ofReal (kyFanApproximationGauge_comp_le k L A R)
  gauge_adjoint A := by rw [kyFanApproximationGauge_adjoint]

@[simp]
theorem gauge_kyFanSymmetricIdealFamily
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜] (k : ℕ) (hk : 0 < k)
    (A : E →L[𝕜] F) :
    (kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).gauge A =
      ENNReal.ofReal (kyFanApproximationGauge k A) := rfl

theorem gauge_kyFanSymmetricIdealFamily_ne_top
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜] (k : ℕ) (hk : 0 < k)
    (A : E →L[𝕜] F) :
    (kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).gauge A ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Every bounded operator lies in the finite Ky Fan ideal: the gauge is a
finite sum of approximation numbers, so it never reaches `∞`. -/
@[simp]
theorem carrier_kyFanSymmetricIdealFamily
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜] (k : ℕ) (hk : 0 < k) :
    (kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).toOperatorIdealFamily.carrier
      (E := E) (F := F) = ⊤ := by
  ext A
  simp

/-- The real-valued Ky Fan gauge is recovered from the canonical one. -/
@[simp]
theorem toReal_gauge_kyFanSymmetricIdealFamily
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜] (k : ℕ) (hk : 0 < k)
    (A : E →L[𝕜] F) :
    ((kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).gauge A).toReal =
      kyFanApproximationGauge k A :=
  ENNReal.toReal_ofReal (kyFanApproximationGauge_nonneg k A)

/-- The finite Ky Fan ideal is complete.

The ideal is all of `E →L[𝕜] F` and its norm is *equivalent* to the operator
norm — `‖A‖ ≤ ∑_{n<k} aₙ(A) ≤ k‖A‖` — so completeness is inherited from the
bounded operators.  Both inequalities are needed: the first turns an ideal-norm
Cauchy sequence into an operator-norm one, the second turns the operator-norm
limit back into an ideal-norm limit. -/
instance isComplete_kyFanSymmetricIdealFamily
    [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜] (k : ℕ) (hk : 0 < k) :
    (kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).toOperatorIdealFamily.IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    have hnorm : ∀ x : (kyFanSymmetricIdealFamily (𝕜 := 𝕜) k hk).toOperatorIdealFamily.Elem E F,
        ‖x‖ = kyFanApproximationGauge k x.val :=
      fun x => ENNReal.toReal_ofReal (kyFanApproximationGauge_nonneg k _)
    refine Metric.complete_of_cauchySeq_tendsto fun a ha => ?_
    have hop : CauchySeq fun n => (a n).val := by
      rw [Metric.cauchySeq_iff] at ha ⊢
      intro ε hε
      obtain ⟨M, hM⟩ := ha ε hε
      refine ⟨M, fun m hm n hn => lt_of_le_of_lt ?_ (hM m hm n hn)⟩
      rw [dist_eq_norm, dist_eq_norm, hnorm]
      exact opNorm_le_kyFanApproximationGauge hk _
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hop
    refine ⟨TauCeti.OperatorIdealFamily.Elem.mk
      (gauge_kyFanSymmetricIdealFamily_ne_top k hk L), ?_⟩
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    rw [Metric.tendsto_atTop] at hL ⊢
    intro ε hε
    obtain ⟨M, hM⟩ := hL (ε / k) (div_pos hε hkR)
    refine ⟨M, fun n hn => ?_⟩
    rw [dist_eq_norm, hnorm]
    calc kyFanApproximationGauge k ((a n).val - L)
        ≤ (k : ℝ) * ‖(a n).val - L‖ :=
          kyFanApproximationGauge_le_nat_mul_opNorm k _
      _ < (k : ℝ) * (ε / k) := by
          refine mul_lt_mul_of_pos_left ?_ hkR
          simpa [dist_eq_norm] using hM n hn
      _ = ε := by field_simp

/-- A rectangular ideal family whose gauge is fully symmetric with respect
    to all finite Ky Fan approximation gauges. -/
structure KyFanDominantIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  toRectangularSymmetricIdealFamily :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜)
  majorization_mem_and_gauge_le :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A B : E →L[𝕜] F},
      toRectangularSymmetricIdealFamily.Mem B →
      (∀ k, kyFanApproximationGauge k A ≤
        kyFanApproximationGauge k B) →
      toRectangularSymmetricIdealFamily.Mem A ∧
        toRectangularSymmetricIdealFamily.gauge A ≤
          toRectangularSymmetricIdealFamily.gauge B

/-- Source-facing name for the infinite-dimensional unitarily invariant norm
families supported by the Davis--Kahan cutoff proof. -/
abbrev UnitaryInvariantIdealFamily
    (𝕜 : Type u) [RCLike 𝕜] :=
  KyFanDominantIdealFamily (𝕜 := 𝕜)

namespace KyFanDominantIdealFamily

/-! ### The ideal interface

`KyFanDominantIdealFamily` carries its ideal as a `RectangularSymmetricIdealFamily`
field, but no consumer should have to say so.  These two accessors are the whole
public surface the sin-Θ development uses, and everything downstream is stated
through them rather than through the field.

That indirection is deliberate and is the first half of the §13 retirement of
`RectangularSymmetricIdealFamily` (see `dev/tauceti-signature-polish-todo.md`).
The canonical replacement, `TauCeti.SymmetricOperatorIdealFamily`, carries a
single `ℝ≥0∞` gauge and no membership predicate — its laws are unconditional —
so swapping the representation changes the *type* of `gauge` and deletes
`Mem` as data.  With ~376 call sites naming the field directly that swap was a
sixty-module flag day; with them naming these accessors it is a change to this
file plus whatever proof repair the `ℝ`-valued view needs, and the `ℝ`-valued
interface below can survive as a documented convenience of the paper layer
instead of as a second competing structure. -/

variable (N : KyFanDominantIdealFamily.{u, v} 𝕜)

/-- Membership in the ideal: the operator has finite ideal gauge. -/
abbrev Mem (A : E →L[𝕜] F) : Prop :=
  N.toRectangularSymmetricIdealFamily.Mem A

/-- The ideal gauge, real-valued and meaningful only on members
(`KyFanDominantIdealFamily.Mem`). -/
abbrev gauge (A : E →L[𝕜] F) : ℝ :=
  N.toRectangularSymmetricIdealFamily.gauge A

/-! Both accessors are `abbrev`, so they are reducible and `exact` sees through
them.  `rw` does **not**: it keys on the head symbol, and
`KyFanDominantIdealFamily.gauge N A` and
`RectangularSymmetricIdealFamily.gauge N.toRectangularSymmetricIdealFamily A`
have different ones.  A proof whose goal is stated through these accessors but
whose supporting lemmas are stated over the underlying ideal — the block
lemmas in `SinTheta/**` are the usual case — needs one
`simp only [KyFanDominantIdealFamily.gauge]` before the rewrite.  Five proofs
needed exactly that when the call sites were repointed; there is no need to
avoid the accessors on account of it. -/

/-- The ordinary operator norm with its finite-Ky-Fan dominance property. -/
noncomputable def operatorNorm :
    KyFanDominantIdealFamily (𝕜 := 𝕜) where
  toRectangularSymmetricIdealFamily :=
    RectangularSymmetricIdealFamily.operatorNorm
  majorization_mem_and_gauge_le := by
    intro E F _ _ _ _ _ _ A B hB hmajor
    refine ⟨trivial, ?_⟩
    change ‖A‖ ≤ ‖B‖
    simpa using hmajor 1

/-- Completeness of a fixed positive finite Ky Fan gauge. -/
theorem kyFan_gauge_complete (k : ℕ) (hk : 0 < k)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : ℕ → E →L[𝕜] F)
    (hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
      kyFanApproximationGauge k (A m - A n) < ε) :
    ∃ L : E →L[𝕜] F, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
      kyFanApproximationGauge k (A n - L) < ε := by
  have hopCauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
      ‖A m - A n‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hCauchy ε hε
    refine ⟨N, ?_⟩
    intro m n hm hn
    exact lt_of_le_of_lt
      (opNorm_le_kyFanApproximationGauge hk (A m - A n))
      (hN m n hm hn)
  obtain ⟨L, hLmem, hL⟩ :=
    RectangularSymmetricIdealFamily.operatorNorm.gauge_complete
      A (fun n => trivial) hopCauchy
  refine ⟨L, ?_⟩
  intro ε hε
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨N, hN⟩ := hL (ε / (k : ℝ)) (div_pos hε hkR)
  refine ⟨N, ?_⟩
  intro n hn
  calc
    kyFanApproximationGauge k (A n - L)
        ≤ (k : ℝ) * ‖A n - L‖ :=
      kyFanApproximationGauge_le_nat_mul_opNorm k (A n - L)
    _ < (k : ℝ) * (ε / (k : ℝ)) :=
      mul_lt_mul_of_pos_left (hN n hn) hkR
    _ = ε := by field_simp

/-- A fixed positive finite Ky Fan gauge with its own dominance property. -/
noncomputable def kyFan [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (k : ℕ) (hk : 0 < k) :
    KyFanDominantIdealFamily (𝕜 := 𝕜) where
  toRectangularSymmetricIdealFamily := {
    Mem := fun _ => True
    gauge := kyFanApproximationGauge k
    zero_mem := trivial
    add_mem := by intros; trivial
    smul_mem := by intros; trivial
    adjoint_mem := by intros; trivial
    comp_mem := by intros; trivial
    gauge_nonneg := by
      intro E F _ _ _ _ _ _ A hA
      exact kyFanApproximationGauge_nonneg k A
    gauge_zero := by
      intro E F _ _ _ _ _ _
      exact kyFanApproximationGauge_zero_map k
    gauge_eq_zero := by
      intro E F _ _ _ _ _ _ A hA hzero
      apply norm_eq_zero.mp
      exact le_antisymm
        ((opNorm_le_kyFanApproximationGauge hk A).trans_eq hzero)
        (norm_nonneg A)
    gauge_add_le := by
      intro E F _ _ _ _ _ _ A B hA hB
      exact kyFanApproximationGauge_add_le k A B
    gauge_smul := by
      intro E F _ _ _ _ _ _ c A hA
      exact kyFanApproximationGauge_smul k c A
    gauge_adjoint := by
      intro E F _ _ _ _ _ _ A hA
      exact kyFanApproximationGauge_adjoint k A
    gauge_comp_le := by
      intro E F G H _ _ _ _ _ _ _ _ _ _ _ _ L A R hA
      exact kyFanApproximationGauge_comp_le k L A R
    opNorm_le_gauge := by
      intro E F _ _ _ _ _ _ A hA
      exact opNorm_le_kyFanApproximationGauge hk A
    gauge_complete := by
      intro E F _ _ _ _ _ _ A hmem hCauchy
      obtain ⟨L, hL⟩ := kyFan_gauge_complete k hk A hCauchy
      exact ⟨L, trivial, hL⟩
  }
  majorization_mem_and_gauge_le := by
    intro E F _ _ _ _ _ _ A B hB hmajor
    exact ⟨trivial, hmajor k⟩

/-- Every bounded operator belongs to the fixed finite Ky Fan family. -/
@[simp]
theorem kyFan_mem [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (k : ℕ) (hk : 0 < k) (K : E →L[𝕜] F) :
    (kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily.Mem K :=
  trivial

/-- The concrete gauge of the fixed finite Ky Fan family. -/
@[simp]
theorem kyFan_gauge [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (k : ℕ) (hk : 0 < k) (K : E →L[𝕜] F) :
    (kyFan (𝕜 := 𝕜) k hk).toRectangularSymmetricIdealFamily.gauge K =
      kyFanApproximationGauge k K :=
  rfl

end KyFanDominantIdealFamily

/-- Infinite-dimensional Fan dominance, exposed from the stronger family. -/
theorem mem_and_gauge_le_of_all_kyFanApproximationGauge_le
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F}
    (hB : N.toRectangularSymmetricIdealFamily.Mem B)
    (h : ∀ k, kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    N.toRectangularSymmetricIdealFamily.Mem A ∧
      N.toRectangularSymmetricIdealFamily.gauge A ≤
        N.toRectangularSymmetricIdealFamily.gauge B :=
  N.majorization_mem_and_gauge_le hB h

/-- Scaled Fan dominance in the exact form consumed by the Sylvester theorem. -/
theorem mem_and_scaled_gauge_le_of_all_scaled_kyFan_le
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    {A B : E →L[𝕜] F} {δ : ℝ}
    (hδ : 0 < δ)
    (hB : N.toRectangularSymmetricIdealFamily.Mem B)
    (h : ∀ k, δ * kyFanApproximationGauge k A ≤
      kyFanApproximationGauge k B) :
    N.toRectangularSymmetricIdealFamily.Mem A ∧
      δ * N.toRectangularSymmetricIdealFamily.gauge A ≤
        N.toRectangularSymmetricIdealFamily.gauge B := by
  let d : 𝕜 := (δ : 𝕜)
  have hd : d ≠ 0 := RCLike.ofReal_ne_zero.mpr hδ.ne'
  have hdnorm : ‖d‖ = δ := by
    simp [d, abs_of_pos hδ]
  have hscaled : ∀ k,
      kyFanApproximationGauge k (d • A) ≤
        kyFanApproximationGauge k B := by
    intro k
    rw [kyFanApproximationGauge_smul, hdnorm]
    exact h k
  obtain ⟨hdA, hgauge⟩ := N.majorization_mem_and_gauge_le hB hscaled
  have hA : N.toRectangularSymmetricIdealFamily.Mem A := by
    have hinv := N.toRectangularSymmetricIdealFamily.smul_mem d⁻¹ hdA
    rw [← mul_smul, inv_mul_cancel₀ hd, one_smul] at hinv
    exact hinv
  refine ⟨hA, ?_⟩
  have hhom := N.toRectangularSymmetricIdealFamily.gauge_smul d hA
  rw [hdnorm] at hhom
  linarith

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti