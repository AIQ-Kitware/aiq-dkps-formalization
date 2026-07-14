/-
All-proper-query-subset lifts for the finite and compact-infinite Quench theorems.
-/

import DkpsQuench2026.QueryEfficiency.Finite
import DkpsQuench2026.QueryEfficiency.Infinite

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Nat Classical Pointwise Topology
open Filter MeasureTheory ProbabilityTheory

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace DkpsQuench2026.QueryEfficiency

open Acharyya2024
open DkpsQuench2026

universe u v wr wy

variable {Q : Type u} [DecidableEq Q]
variable {X : Type v} [MeasurableSpace X]
variable {Ωref : Type wr} [MeasurableSpace Ωref]
variable {Ωresp : Type wy} [MeasurableSpace Ωresp]
/-- All-proper-subsets finite-model raw-response Quench.

Each valid subset receives its own dimensions, data, and assumptions, while the
reference law, response-noise law, and full score are shared.  The theorem is
the quantifier lift encoded by `HighProbQueryEfficient`.
-/
theorem finiteAllQueries
    [Fintype (Model Q X)]
    (d m p : Finset Q → Nat)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : ∀ Qsub, FiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) (d Qsub) (m Qsub) (p Qsub))
    (hm : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      0 < m Qsub)
    (H : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      FiniteSubsetAssumptions Pf μresp score Qstar Qsub (D Qsub)) :
    HighProbQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp hμresp)
      Pf sqLoss Qstar (yFull score Qstar)
      (fun Qsub => finiteEstimator f_ref score Qstar (D Qsub))
      (fun Qsub _ _ f => yQ score Qsub f) := by
  intro m0 hm0 Qsub hsub hcard
  have hlt : Qsub.card < Qstar.card := by
    simpa [hcard] using hm0
  simpa only using
    (finiteFixedSubset
      (Q := Q) (X := X) (Ωref := Ωref) (Ωresp := Ωresp)
      (d := d Qsub) (m := m Qsub) (p := p Qsub)
      (hm := hm Qsub hsub hlt)
      (Pf := Pf) (μref := μref) (hμref := hμref) (μresp := μresp)
      (f_ref := f_ref) (hiid := hiid) (score := score)
      (Qstar := Qstar) (Qsub := Qsub) (D := D Qsub)
      (H := H Qsub hsub hlt))

/-- All-proper-subsets compact infinite-model raw-response Quench.

As in the finite theorem, each subset may use its own embedding and response
dimensions, perspective, raw response embedding, and raw-response Lipschitz
constant.  The finite net, entropy exponent, regularity certificates, and norm
envelope are derived within the fixed-subset theorem.
-/
theorem infiniteAllQueries
    (d m p : Finset Q → Nat)
    (Pf : Measure (Model Q X)) [IsProbabilityMeasure Pf]
    (μref : Nat → Measure Ωref) (hμref : ∀ n, IsProbabilityMeasure (μref n))
    (μresp : Nat → Measure Ωresp)
    (hμresp : ∀ n, IsProbabilityMeasure (μresp n))
    (f_ref : ∀ n, Ωref → Fin n → Model Q X)
    (hiid : IIDReferenceSampler Pf μref f_ref)
    (score : Model Q X → Finset Q → Real)
    (Qstar : Finset Q)
    (D : ∀ Qsub, InfiniteSubsetData (Q := Q) (X := X)
      (Ωresp := Ωresp) (d Qsub) (m Qsub) (p Qsub))
    (hm : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      0 < m Qsub)
    (H : ∀ Qsub, Qsub ⊆ Qstar → Qsub.card < Qstar.card →
      InfiniteSubsetAssumptions Pf μresp score Qstar Qsub (D Qsub)) :
    HighProbQueryEfficient (Q := Q) (X := X)
      (jointStageMeasure μref μresp)
      (jointStageMeasure_probability μref hμref μresp hμresp)
      Pf sqLoss Qstar (yFull score Qstar)
      (fun Qsub => infiniteEstimator f_ref score Qstar (D Qsub))
      (fun Qsub _ _ f => yQ score Qsub f) := by
  intro m0 hm0 Qsub hsub hcard
  have hlt : Qsub.card < Qstar.card := by
    simpa [hcard] using hm0
  simpa only using
    (infiniteFixedSubset
      (Q := Q) (X := X) (Ωref := Ωref) (Ωresp := Ωresp)
      (d := d Qsub) (m := m Qsub) (p := p Qsub)
      (hm := hm Qsub hsub hlt)
      (Pf := Pf) (μref := μref) (hμref := hμref) (μresp := μresp)
      (f_ref := f_ref) (hiid := hiid) (score := score)
      (Qstar := Qstar) (Qsub := Qsub) (D := D Qsub)
      (H := H Qsub hsub hlt))


end DkpsQuench2026.QueryEfficiency
