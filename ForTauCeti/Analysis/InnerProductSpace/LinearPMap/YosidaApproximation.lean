/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
Adapted from: Spectra (https://github.com/adambornemann-glitch/Spectra),
  `Spectra/YosidaHille/Approximation/{Helpers,Defs}.lean` at commit
  `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`,
  Copyright (c) 2026 Spectra Formalization Project, `Authors: Adam Bornemann`,
  Apache 2.0. Modified to use TauCeti's Stone group and symmetric approximants
  (Apache 2.0 §4(b)); the donor's authorship and copyright are retained here (§4(c)).
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Yosida.Basic
public import TauCeti.Analysis.Semigroups.Group.Stone.Basic
public import TauCeti.Analysis.Semigroups.Group.Stone.Unbounded
public import Mathlib.Data.PNat.Basic
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Yosida.Uniform
import TauCeti.Analysis.Semigroups.TrotterKato
import TauCeti.LinearAlgebra.LinearPMap.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The Stone group as the strong limit of the symmetric Yosida flows

The group comes from TauCeti's Stone theorem. The symmetric Yosida generators
converge on the domain, so the contraction resolvent identity and Trotter–Kato
identify their exponential limit. TauCeti's compact-time Cauchy theorem
upgrades pointwise convergence to uniform convergence on bounded time sets.

The earlier construction used Spectra's imaginary resolvent approximants
and constructed the group by pointwise limits. See the preserved attribution
in the header and the extraction manifest for the original declarations.
-/

public section

open Complex Filter
open TauCeti.Semigroups
open scoped Topology Interval NNReal

namespace TauCeti.LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H}

open StronglyContinuousGroup (ofBoundedExp)

/-- Strong convergence of the generators on the target domain gives strong
convergence of their resolvents at `1`, using the common contraction bound. -/
private theorem tendsto_yosidaFlow_resolvent (hA : IsSelfAdjoint A) (U : StronglyContinuousGroup H)
    (hU : U.IsUnitary) (hG : U.complexGenerator hU = I • A) (x : H) :
    Tendsto (fun n : ℕ+ => _root_.LinearPMap.resolvent
      (ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ))).toSemigroup.generator 1 x)
      atTop (𝓝 (_root_.LinearPMap.resolvent U.toSemigroup.generator 1 x)) := by
  let S (n : ℕ+) := (ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ))).toSemigroup
  let T := U.toSemigroup
  have hb (n : ℕ+) : (S n).HasGrowthBound 0 1 :=
    (StronglyContinuousGroup.isUnitary_ofBoundedExp _
      (hA.isSelfAdjoint_symmetricYosidaApproximation _)).hasGrowthBound_zero_one.toSemigroup
  have hT : T.HasGrowthBound 0 1 := hU.hasGrowthBound_zero_one.toSemigroup
  have h01 : (0 : ℝ) < 1 := zero_lt_one
  let y := T.resolvent hT 1 h01 x
  have hy := (T.isResolventAt_generator hT h01).mem_domain x
  have hG' : T.generator = (I • A).restrictScalars ℝ := by
    change U.toSemigroup.generator = _
    rw [← U.generator_def]
    exact (U.complexGenerator_restrictScalars hU).symm.trans
      (congrArg (_root_.LinearPMap.restrictScalars ℝ) hG)
  have hyA : y ∈ A.domain := by
    change y ∈ T.generator.domain at hy
    rw [hG', _root_.LinearPMap.restrictScalars_domain, Submodule.restrictScalars_mem,
      _root_.LinearPMap.smul_domain] at hy
    exact hy
  have hx : y - I • A ⟨y, hyA⟩ = x := by
    have h := (T.isResolventAt_generator hT h01).smul_sub_apply x
    have happ : T.generator ⟨y, hy⟩ = I • A ⟨y, hyA⟩ :=
      _root_.LinearPMap.congr_fun_restrictScalars ℝ hG' hy hyA
    change 1 • y - T.generator ⟨y, hy⟩ = x at h
    rwa [one_smul, happ] at h
  have happrox := (((hA.tendsto_symmetricYosidaApproximation_apply ⟨y, hyA⟩).mono_left
    atTop_le_cocompact).comp
      (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)).const_smul I
  have herror : Tendsto (fun n : ℕ+ =>
      ‖I • A.symmetricYosidaApproximation (n : ℝ) y - I • A ⟨y, hyA⟩‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp happrox
  change Tendsto (fun n => _root_.LinearPMap.resolvent (S n).generator 1 x) atTop
    (𝓝 (_root_.LinearPMap.resolvent T.generator 1 x))
  rw [T.generator_resolvent_eq hT h01]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) herror
  have hSn : (S n).generator =
      ((I • A.symmetricYosidaApproximation (n : ℝ)).restrictScalars ℝ).toLinearMap.toPMap ⊤ := by
    change (ofBoundedExp _).toSemigroup.generator = _
    rw [← StronglyContinuousGroup.generator_def, StronglyContinuousGroup.ofBoundedExp_generator]
  let v : (S n).generator.domain := ⟨y, by rw [hSn]; exact Submodule.mem_top⟩
  have hv : (S n).generator v = I • A.symmetricYosidaApproximation (n : ℝ) y :=
    _root_.LinearPMap.congr_fun hSn v.property Submodule.mem_top
  have hbound : ‖_root_.LinearPMap.resolvent (S n).generator 1‖ ≤ 1 := by
    simpa only [sub_zero, div_one] using (S n).norm_generator_resolvent_le (hb n) h01
  calc
    _ = ‖_root_.LinearPMap.resolvent (S n).generator 1
        (I • A.symmetricYosidaApproximation (n : ℝ) y - I • A ⟨y, hyA⟩)‖ := by
      have hleft := ((S n).isResolventAt_generator (hb n) h01).apply_smul_sub v
      change (S n).resolvent (hb n) 1 h01 (1 • y - (S n).generator v) = y at hleft
      rw [one_smul, hv, ← (S n).generator_resolvent_eq (hb n) h01] at hleft
      calc
        _ = ‖_root_.LinearPMap.resolvent (S n).generator 1
            (x - (y - I • A.symmetricYosidaApproximation (n : ℝ) y))‖ := by
          rw [map_sub, hleft]
        _ = _ := by
          congr 2
          rw [← hx]
          abel
    _ ≤ _ := (ContinuousLinearMap.le_opNorm _ _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hbound (norm_nonneg _))

/-- Trotter–Kato gives convergence for nonnegative time. For negative time,
apply the inverse of the approximating group and use its unitarity. -/
private theorem tendsto_yosidaFlow_of_complexGenerator_eq (hA : IsSelfAdjoint A)
    (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (hG : U.complexGenerator hU = I • A)
    (t : ℝ) (x : H) :
    Tendsto (fun n : ℕ+ => ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) t x)
      atTop (𝓝 (U t x)) := by
  let V (n : ℕ+) := ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ))
  have hV (n : ℕ+) : (V n).IsUnitary :=
    StronglyContinuousGroup.isUnitary_ofBoundedExp _
      (hA.isSelfAdjoint_symmetricYosidaApproximation _)
  have hpos (s : ℝ) (hs : 0 ≤ s) (z : H) :
      Tendsto (fun n : ℕ+ => V n s z) atTop (𝓝 (U s z)) := by
    have h := StronglyContinuousSemigroup.tendsto_apply_of_tendsto_resolvent
      (S := fun n => (V n).toSemigroup) (T := U.toSemigroup)
      (fun n => (hV n).hasGrowthBound_zero_one.toSemigroup)
      hU.hasGrowthBound_zero_one.toSemigroup (lambda := 1) zero_lt_one
      (tendsto_yosidaFlow_resolvent hA U hU hG) ⟨s, hs⟩ z
    have hsU : U.toSemigroup (⟨s, hs⟩ : ℝ≥0) z = U s z :=
      DFunLike.congr_fun (U.toSemigroup_apply ⟨s, hs⟩) z
    rw [hsU] at h
    exact h.congr fun n => DFunLike.congr_fun ((V n).toSemigroup_apply ⟨s, hs⟩) z
  by_cases ht : 0 ≤ t
  · exact hpos t ht x
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have h := tendsto_iff_norm_sub_tendsto_zero.mp
      (hpos (-t) (neg_nonneg.mpr (le_of_not_ge ht)) (U t x))
    refine h.congr fun n => ?_
    rw [U.map_neg_apply_map_apply]
    calc
      _ = ‖V n t (V n (-t) (U t x) - x)‖ := ((hV n).norm_map t _).symm
      _ = _ := by rw [map_sub, (V n).map_apply_map_neg_apply, norm_sub_rev]


/-- The unitary group selected by TauCeti's unbounded Stone theorem. -/
noncomputable def genToGroup (hA : IsSelfAdjoint A) :
    {U : StronglyContinuousGroup H // U.IsUnitary} :=
  ⟨hA.exists_isUnitary_complexGenerator_eq_I_smul.choose,
    hA.exists_isUnitary_complexGenerator_eq_I_smul.choose_spec.choose⟩

private theorem complexGenerator_genToGroup (hA : IsSelfAdjoint A) :
    (genToGroup hA).val.complexGenerator (genToGroup hA).property = I • A :=
  hA.exists_isUnitary_complexGenerator_eq_I_smul.choose_spec.choose_spec

/-- The group selected by Stone's theorem has Stone generator `A`. -/
theorem stoneGenerator_genToGroup (hA : IsSelfAdjoint A) :
    (genToGroup hA).val.stoneGenerator (genToGroup hA).property = A := by
  rw [StronglyContinuousGroup.stoneGenerator_def, complexGenerator_genToGroup,
    smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

/-- The Yosida exponentials converge strongly to the Stone group at every real time. -/
theorem tendsto_yosidaFlow_genToGroup (hA : IsSelfAdjoint A) (t : ℝ) (x : H) :
    Tendsto (fun n : ℕ+ => ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) t x)
      atTop (𝓝 ((genToGroup hA).val t x)) :=
  tendsto_yosidaFlow_of_complexGenerator_eq hA _ _ (complexGenerator_genToGroup hA) t x

/-- Convergence to the Stone group is uniform on bounded time sets at each vector. -/
theorem tendstoUniformlyOn_yosidaFlow_genToGroup (hA : IsSelfAdjoint A) (x : H)
    {S : Set ℝ} {R : ℝ} (hS : ∀ t ∈ S, |t| ≤ R) :
    TendstoUniformlyOn
      (fun (n : ℕ+) (t : ℝ) => ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) t x)
      (fun t => (genToGroup hA).val t x) atTop S := by
  have h := hA.uniformCauchySeqOn_exp_smul_I_smul_symmetricYosidaApproximation_apply x hS
  have hcast : Tendsto (fun n : ℕ+ => (n : ℝ)) atTop (cocompact ℝ) :=
    (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop).mono_right atTop_le_cocompact
  have hc : UniformCauchySeqOn
      (fun (n : ℕ+) (t : ℝ) =>
        ofBoundedExp (A.symmetricYosidaApproximation (n : ℝ)) t x) atTop S := by
    simpa only [StronglyContinuousGroup.ofBoundedExp_apply,
      ContinuousLinearMap.coe_restrictScalars'] using
      (show UniformCauchySeqOn (fun (n : ℕ+) (t : ℝ) =>
        NormedSpace.exp ((t : ℂ) • (I • A.symmetricYosidaApproximation (n : ℝ))) x) atTop S from
        fun u hu => (hcast.prodMap hcast).eventually (h u hu))
  exact hc.tendstoUniformlyOn_of_tendsto fun t _ => tendsto_yosidaFlow_genToGroup hA t x

/-- The Stone orbit has the expected derivative for vectors in the operator domain. -/
private theorem hasDerivAt_genToGroup (hA : IsSelfAdjoint A) (x : A.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (genToGroup hA).val s x)
      (I • (genToGroup hA).val t (A x)) t := by
  let U := (genToGroup hA).val
  have hU : U.IsUnitary := (genToGroup hA).property
  have hG : U.generator = (I • A).restrictScalars ℝ :=
    (U.complexGenerator_restrictScalars hU).symm.trans
      (congrArg (_root_.LinearPMap.restrictScalars ℝ) (complexGenerator_genToGroup hA))
  have hx : (x : H) ∈ U.generator.domain := by
    rw [hG, _root_.LinearPMap.restrictScalars_domain, Submodule.restrictScalars_mem,
      _root_.LinearPMap.smul_domain]
    exact x.property
  have hxU : (x : H) ∈ U.domain := U.generator_domain ▸ hx
  have hval : U.generator ⟨x, hx⟩ = I • A x :=
    _root_.LinearPMap.congr_fun_restrictScalars ℝ hG hx x.property
  simpa only [hval, hU.map_smul] using U.hasDerivAt ⟨x, hxU⟩ t

/-- Integrating the Stone orbit derivative recovers its displacement. -/
theorem integral_genToGroup (hA : IsSelfAdjoint A) (x : A.domain) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, I • (genToGroup hA).val s (A x)) = (genToGroup hA).val t x - x := by
  have hc := ((genToGroup hA).val.continuous_orbit (A x)).const_smul I
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_genToGroup hA x s) (hc.intervalIntegrable 0 t)]
  rw [StronglyContinuousGroup.map_zero_apply]

/-- On the operator domain the Stone orbit has speed at most `‖A x‖`. -/
theorem norm_genToGroup_sub_self_le (hA : IsSelfAdjoint A) (x : A.domain) (t : ℝ) :
    ‖(genToGroup hA).val t x - x‖ ≤ |t| * ‖A x‖ := by
  rw [← integral_genToGroup hA x t]
  simpa only [sub_zero, mul_comm] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun s : ℝ => I • (genToGroup hA).val s (A x)) (a := 0) (b := t)
      (C := ‖A x‖) fun s _ => by
        rw [norm_smul, Complex.norm_I, one_mul, (genToGroup hA).property.norm_map])

end TauCeti.LinearPMap
