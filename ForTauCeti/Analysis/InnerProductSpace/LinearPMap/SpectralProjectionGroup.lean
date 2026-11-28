/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.YosidaApproximation

/-!
# Spectral projections commute with the unitary group

`E_A(B)` commutes with `exp(itA)` for every Borel set `B` and every `t`.

This is the fact a block-diagonal argument needs: cutting a vector into spectral
pieces has to commute with the flow, or the blocks are not preserved by it.

The route is the one the Yosida construction already lays out, and no new
analysis is required at any step:

* spectral projections commute with the resolvent at every non-real point
  (`IsSelfAdjoint.commute_spectralPVM_proj_resolvent`);
* the symmetric Yosida approximant is a linear combination of two resolvents,
  so it commutes too;
* an exponential of a commuting operator commutes (`Commute.exp_right`);
* the Stone group is the strong limit of those exponentials, so commutation
  survives — a projection is continuous, and limits are unique.

## Sources

*Follows nothing in particular*: the commutation a block-diagonal argument needs between
spectral projections and the flow.

## Provenance

The DKPS argument combines spectral projection and resolvent commutation
with strong convergence of the symmetric Yosida flows.
-/

public section

open _root_.LinearPMap (
  resolvent)

open scoped InnerProductSpace
open TauCeti.Semigroups.StronglyContinuousGroup (ofBoundedExp)

open Complex Filter Topology

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B)

/-- A spectral projection commutes with the symmetric Yosida approximant, which
is a linear combination of two resolvents. -/
theorem specProjection_comm_yosidaApproxSym (n : ℕ+) :
    Commute ((A.spectralPVM hA).proj B hB) (A.symmetricYosidaApproximation (n : ℝ)) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  have hrootIn : (I * (n : ℂ)) ∈ _root_.LinearPMap.resolventSet A :=
    hA.mem_resolventSet_I_mul hn
  have hrootNegIn : (-I * (n : ℂ)) ∈ _root_.LinearPMap.resolventSet A := by
    simpa only [ofReal_neg, ofReal_natCast, mul_neg, neg_mul] using
      hA.mem_resolventSet_I_mul (neg_ne_zero.mpr hn)
  have h1 : Commute ((A.spectralPVM hA).proj B hB) (A.resolvent (I * (n : ℂ))) :=
    hA.commute_spectralPVM_proj_resolvent B hB hrootIn
  have h2 : Commute ((A.spectralPVM hA).proj B hB) (A.resolvent (-I * (n : ℂ))) :=
    hA.commute_spectralPVM_proj_resolvent B hB hrootNegIn
  rw [A.symmetricYosidaApproximation_def]
  push_cast
  exact (h1.add_right h2).smul_right (-((n : ℂ) ^ 2 / 2))

/-- A spectral projection commutes with each native bounded Yosida flow. -/
theorem specProjection_comm_yosidaFlow (n : ℕ+) (t : ℝ) (ψ : H) :
    (A.spectralPVM hA).proj B hB (ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) t ψ) =
      ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) t ((A.spectralPVM hA).proj B hB ψ) := by
  rw [Semigroups.StronglyContinuousGroup.ofBoundedExp_apply]
  have h := (((specProjection_comm_yosidaApproxSym hA B hB n).smul_right I).smul_right
    (t : ℂ)).exp_right
  exact congrArg (fun T : H →L[ℂ] H => T ψ) h.eq

/-- **Spectral projections commute with the unitary group.**  Commutation with
the bounded approximants survives the strong limit. -/
@[simp]
theorem specProjection_genToGroup_apply (t : ℝ) (ψ : H) :
    (A.spectralPVM hA).proj B hB ((genToGroup hA).val t ψ) =
      (genToGroup hA).val t ((A.spectralPVM hA).proj B hB ψ) := by
  have hstep : ∀ n : ℕ+,
      (A.spectralPVM hA).proj B hB (ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) t ψ)
        = ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) t
            ((A.spectralPVM hA).proj B hB ψ) := by
    intro n
    exact specProjection_comm_yosidaFlow hA B hB n t ψ
  have hleft : Tendsto (fun n : ℕ+ => (A.spectralPVM hA).proj B hB (ofBoundedExp
    (A.symmetricYosidaApproximation (n : ℝ)) t ψ))
      atTop (𝓝 ((A.spectralPVM hA).proj B hB ((genToGroup hA).val t ψ))) :=
    (((A.spectralPVM hA).proj B hB).continuous.tendsto _).comp
      (tendsto_yosidaFlow_genToGroup hA t ψ)
  have hright : Tendsto (fun n : ℕ+ => ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) t
    ((A.spectralPVM hA).proj B hB ψ))
      atTop (𝓝 ((genToGroup hA).val t ((A.spectralPVM hA).proj B hB ψ))) :=
    tendsto_yosidaFlow_genToGroup hA t ((A.spectralPVM hA).proj B hB ψ)
  exact tendsto_nhds_unique (by simpa only [hstep] using hleft) hright

end LinearPMap
end TauCeti
