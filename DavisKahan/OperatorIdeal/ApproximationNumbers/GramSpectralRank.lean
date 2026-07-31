/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMaxUpper
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralFormBounds

/-!
# Spectral ranks of Gram cutoffs

This module is the rank-theoretic input for finite spectral-band selection.
For the positive Gram operator `X†X`, approximation-number thresholds control
the dimensions of the upper spectral ranges:

* if `r < a_n(X)`, the closed upper range `[r², ∞)` has rank at least `n+1`;
* if `a_n(X) < r`, the open upper range `(r², ∞)` has rank at most `n`.

The proofs are explicit min--max arguments.  No tactic search, compactness, or
singular-vector attainment is used.  The spectral measure is Tau Ceti's native
`LinearPMap.spectralPVM`; no Spectra self-adjoint wrapper or Stone group is
introduced for this bounded operator.

## Provenance

Promoted from `FinishTanTwoTheta/FinishTanTwoTheta/ApproximationNumber/GramSpectralRank.lean`
under lane `FTT-PROMOTE-5` (2026-07-30), which moved it out of a library that
is not a default build target.  The statements and proofs are unchanged; the
enclosing namespace moved from `TauCeti.FinishTanTwoTheta` to
`TauCeti.ApproximationNumber`, joining the three modules lane `FTT-PROMOTE-3`
landed beside it, and `FinishTanTwoTheta.GroundedImports` — which imports
`DavisKahan.All` and so cannot survive the move — was dropped in favour of the
`ForTauCeti` leaves the file already named.
-/

namespace TauCeti
namespace ApproximationNumber

open scoped InnerProductSpace
open Set

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]


namespace LinearPMap

open TauCeti.LinearPMap

section LocalHalfLine

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-! ## Vector-local half-line bounds

The global lemmas above assume an entire half-line projection is the zero
operator.  Min--max arguments need the sharper local form: a particular domain
vector is annihilated by the unwanted half-line projection.  The proof is the
same cutoff argument, but only along that vector and its image under `A`.
-/

/-- If the low closed half-line annihilates `x`, then the complementary high
closed half-line fixes `x`. -/
theorem specProjection_Ici_apply_eq_self_of_Iic_apply_eq_zero {c : ℝ} (x : H)
    (hz : specProjection hA (Set.Iic c) measurableSet_Iic x = 0) :
    specProjection hA (Set.Ici c) measurableSet_Ici x = x := by
  let P := spectralPVM hA
  have hIio : P.proj (Set.Iio c) measurableSet_Iio x = 0 := by
    have hset : Set.Iio c ∩ Set.Iic c = Set.Iio c := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Iic]
      constructor
      · exact fun hs => hs.1
      · intro hs
        exact ⟨hs, hs.le⟩
    calc
      P.proj (Set.Iio c) measurableSet_Iio x =
          (P.proj (Set.Iio c) measurableSet_Iio *
            P.proj (Set.Iic c) measurableSet_Iic) x := by
        rw [P.proj_inter]
        exact (congrArg (fun T : H →L[ℂ] H => T x)
          (P.proj_congr hset (measurableSet_Iio.inter measurableSet_Iic)
            measurableSet_Iio)).symm
      _ = 0 := by
        change P.proj (Set.Iio c) measurableSet_Iio
            (P.proj (Set.Iic c) measurableSet_Iic x) = 0
        change P.proj (Set.Iic c) measurableSet_Iic x = 0 at hz
        rw [hz, map_zero]
  have hcompl : (Set.Iio c)ᶜ = Set.Ici c := Set.compl_Iio
  change P.proj (Set.Ici c) measurableSet_Ici x = x
  calc
    P.proj (Set.Ici c) measurableSet_Ici x =
        P.proj (Set.Iio c)ᶜ measurableSet_Iio.compl x := by
      exact congrArg (fun T : H →L[ℂ] H => T x)
        (P.proj_congr hcompl.symm measurableSet_Ici measurableSet_Iio.compl)
    _ = (ContinuousLinearMap.id ℂ H - P.proj (Set.Iio c) measurableSet_Iio) x := by
      rw [P.proj_compl]
    _ = x := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hIio, sub_zero]

/-- If the high closed half-line annihilates `x`, then the complementary low
closed half-line fixes `x`. -/
theorem specProjection_Iic_apply_eq_self_of_Ici_apply_eq_zero {c : ℝ} (x : H)
    (hz : specProjection hA (Set.Ici c) measurableSet_Ici x = 0) :
    specProjection hA (Set.Iic c) measurableSet_Iic x = x := by
  let P := spectralPVM hA
  have hIoi : P.proj (Set.Ioi c) measurableSet_Ioi x = 0 := by
    have hset : Set.Ioi c ∩ Set.Ici c = Set.Ioi c := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · exact fun hs => hs.1
      · intro hs
        exact ⟨hs, hs.le⟩
    calc
      P.proj (Set.Ioi c) measurableSet_Ioi x =
          (P.proj (Set.Ioi c) measurableSet_Ioi *
            P.proj (Set.Ici c) measurableSet_Ici) x := by
        rw [P.proj_inter]
        exact (congrArg (fun T : H →L[ℂ] H => T x)
          (P.proj_congr hset (measurableSet_Ioi.inter measurableSet_Ici)
            measurableSet_Ioi)).symm
      _ = 0 := by
        change P.proj (Set.Ioi c) measurableSet_Ioi
            (P.proj (Set.Ici c) measurableSet_Ici x) = 0
        change P.proj (Set.Ici c) measurableSet_Ici x = 0 at hz
        rw [hz, map_zero]
  have hcompl : (Set.Ioi c)ᶜ = Set.Iic c := Set.compl_Ioi
  change P.proj (Set.Iic c) measurableSet_Iic x = x
  calc
    P.proj (Set.Iic c) measurableSet_Iic x =
        P.proj (Set.Ioi c)ᶜ measurableSet_Ioi.compl x := by
      exact congrArg (fun T : H →L[ℂ] H => T x)
        (P.proj_congr hcompl.symm measurableSet_Iic measurableSet_Ioi.compl)
    _ = (ContinuousLinearMap.id ℂ H - P.proj (Set.Ioi c) measurableSet_Ioi) x := by
      rw [P.proj_compl]
    _ = x := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, hIoi, sub_zero]

/-- **Vector-local lower energy bound.** If a domain vector has no spectral
component in `(-∞, c]`, its quadratic form is at least `c ‖x‖²`. -/
theorem le_re_inner_of_specProjection_Iic_apply_eq_zero {c : ℝ} (x : A.domain)
    (hz : specProjection hA (Set.Iic c) measurableSet_Iic (x : H) = 0) :
    c * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re := by
  have hfix : specProjection hA (Set.Ici c) measurableSet_Ici (x : H) = (x : H) :=
    specProjection_Ici_apply_eq_self_of_Iic_apply_eq_zero hA (x : H) hz
  have hzA : specProjection hA (Set.Iic c) measurableSet_Iic (A x) = 0 := by
    rw [← specProjection_apply_domain hA (Set.Iic c) measurableSet_Iic x]
    have hsub :
        (⟨specProjection hA (Set.Iic c) measurableSet_Iic (x : H),
          specProjection_mem_domain hA (Set.Iic c) measurableSet_Iic x⟩ : A.domain) = 0 :=
      Subtype.ext hz
    rw [hsub, _root_.LinearPMap.map_zero]
  have hfixA : specProjection hA (Set.Ici c) measurableSet_Ici (A x) = A x :=
    specProjection_Ici_apply_eq_self_of_Iic_apply_eq_zero hA (A x) hzA
  have hlim_of_fix : ∀ (v : H),
      specProjection hA (Set.Ici c) measurableSet_Ici v = v →
      Filter.Tendsto
        (fun τ : ℝ => specProjection hA (Set.Icc c τ) measurableSet_Icc v)
        Filter.atTop (nhds v) := by
    intro v hv
    refine (tendsto_specProjection_Icc hA v).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop |c|] with τ hτ
    obtain ⟨hτ1, hτ2⟩ := abs_le.mp hτ
    have hset : Set.Icc (-τ) τ ∩ Set.Ici c = Set.Icc c τ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
      constructor
      · rintro ⟨⟨hs1, hs2⟩, hs3⟩
        exact ⟨hs3, hs2⟩
      · rintro ⟨hs1, hs2⟩
        exact ⟨⟨by linarith, hs2⟩, hs1⟩
    let P := spectralPVM hA
    change P.proj (Set.Icc (-τ) τ) measurableSet_Icc v =
      P.proj (Set.Icc c τ) measurableSet_Icc v
    symm
    calc
      P.proj (Set.Icc c τ) measurableSet_Icc v =
          P.proj (Set.Icc (-τ) τ ∩ Set.Ici c)
            (measurableSet_Icc.inter measurableSet_Ici) v := by
        exact congrArg (fun T : H →L[ℂ] H => T v)
          (P.proj_congr hset.symm measurableSet_Icc
            (measurableSet_Icc.inter measurableSet_Ici))
      _ = (P.proj (Set.Icc (-τ) τ) measurableSet_Icc *
          P.proj (Set.Ici c) measurableSet_Ici) v := by
        rw [P.proj_inter]
      _ = P.proj (Set.Icc (-τ) τ) measurableSet_Icc v := by
        change P.proj (Set.Icc (-τ) τ) measurableSet_Icc
          (P.proj (Set.Ici c) measurableSet_Ici v) = _
        change P.proj (Set.Ici c) measurableSet_Ici v = v at hv
        rw [hv]
  have hbound : ∀ τ : ℝ,
      c * ‖specProjection hA (Set.Icc c τ) measurableSet_Icc (x : H)‖ ^ 2
        ≤ (⟪specProjection hA (Set.Icc c τ) measurableSet_Icc (A x),
            specProjection hA (Set.Icc c τ) measurableSet_Icc (x : H)⟫_ℂ).re := by
    intro τ
    set y : H := specProjection hA (Set.Icc c τ) measurableSet_Icc (x : H) with hy
    have hyK : y ∈ specRange hA (Set.Icc c τ) measurableSet_Icc := ⟨(x : H), rfl⟩
    have hymem : y ∈ A.domain :=
      specProjection_mem_domain hA (Set.Icc c τ) measurableSet_Icc x
    have hAy : A ⟨y, hymem⟩ =
        specProjection hA (Set.Icc c τ) measurableSet_Icc (A x) :=
      specProjection_apply_domain hA (Set.Icc c τ) measurableSet_Icc x
    have h := (re_inner_apply_bounds_of_subset_Icc hA (Set.Icc c τ)
      measurableSet_Icc (β := c) (α := τ) Set.Subset.rfl hyK hymem).1
    rwa [hAy] at h
  have hlx := hlim_of_fix (x : H) hfix
  have hlA := hlim_of_fix (A x) hfixA
  exact le_of_tendsto_of_tendsto'
    (((hlx.norm).pow 2).const_mul c)
    ((Complex.continuous_re.tendsto _).comp (hlA.inner hlx)) hbound

/-- **Vector-local upper energy bound.** If a domain vector has no spectral
component in `[c, ∞)`, its quadratic form is at most `c ‖x‖²`. -/
theorem re_inner_le_of_specProjection_Ici_apply_eq_zero {c : ℝ} (x : A.domain)
    (hz : specProjection hA (Set.Ici c) measurableSet_Ici (x : H) = 0) :
    (⟪A x, (x : H)⟫_ℂ).re ≤ c * ‖(x : H)‖ ^ 2 := by
  have hfix : specProjection hA (Set.Iic c) measurableSet_Iic (x : H) = (x : H) :=
    specProjection_Iic_apply_eq_self_of_Ici_apply_eq_zero hA (x : H) hz
  have hzA : specProjection hA (Set.Ici c) measurableSet_Ici (A x) = 0 := by
    rw [← specProjection_apply_domain hA (Set.Ici c) measurableSet_Ici x]
    have hsub :
        (⟨specProjection hA (Set.Ici c) measurableSet_Ici (x : H),
          specProjection_mem_domain hA (Set.Ici c) measurableSet_Ici x⟩ : A.domain) = 0 :=
      Subtype.ext hz
    rw [hsub, _root_.LinearPMap.map_zero]
  have hfixA : specProjection hA (Set.Iic c) measurableSet_Iic (A x) = A x :=
    specProjection_Iic_apply_eq_self_of_Ici_apply_eq_zero hA (A x) hzA
  have hlim_of_fix : ∀ (v : H),
      specProjection hA (Set.Iic c) measurableSet_Iic v = v →
      Filter.Tendsto
        (fun τ : ℝ => specProjection hA (Set.Icc (-τ) c) measurableSet_Icc v)
        Filter.atTop (nhds v) := by
    intro v hv
    refine (tendsto_specProjection_Icc hA v).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop |c|] with τ hτ
    obtain ⟨hτ1, hτ2⟩ := abs_le.mp hτ
    have hset : Set.Icc (-τ) τ ∩ Set.Iic c = Set.Icc (-τ) c := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨hs1, hs2⟩, hs3⟩
        exact ⟨hs1, hs3⟩
      · rintro ⟨hs1, hs2⟩
        exact ⟨⟨hs1, by linarith⟩, hs2⟩
    let P := spectralPVM hA
    change P.proj (Set.Icc (-τ) τ) measurableSet_Icc v =
      P.proj (Set.Icc (-τ) c) measurableSet_Icc v
    symm
    calc
      P.proj (Set.Icc (-τ) c) measurableSet_Icc v =
          P.proj (Set.Icc (-τ) τ ∩ Set.Iic c)
            (measurableSet_Icc.inter measurableSet_Iic) v := by
        exact congrArg (fun T : H →L[ℂ] H => T v)
          (P.proj_congr hset.symm measurableSet_Icc
            (measurableSet_Icc.inter measurableSet_Iic))
      _ = (P.proj (Set.Icc (-τ) τ) measurableSet_Icc *
          P.proj (Set.Iic c) measurableSet_Iic) v := by
        rw [P.proj_inter]
      _ = P.proj (Set.Icc (-τ) τ) measurableSet_Icc v := by
        change P.proj (Set.Icc (-τ) τ) measurableSet_Icc
          (P.proj (Set.Iic c) measurableSet_Iic v) = _
        change P.proj (Set.Iic c) measurableSet_Iic v = v at hv
        rw [hv]
  have hbound : ∀ τ : ℝ,
      (⟪specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (A x),
          specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (x : H)⟫_ℂ).re
        ≤ c * ‖specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (x : H)‖ ^ 2 := by
    intro τ
    set y : H := specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (x : H) with hy
    have hyK : y ∈ specRange hA (Set.Icc (-τ) c) measurableSet_Icc := ⟨(x : H), rfl⟩
    have hymem : y ∈ A.domain :=
      specProjection_mem_domain hA (Set.Icc (-τ) c) measurableSet_Icc x
    have hAy : A ⟨y, hymem⟩ =
        specProjection hA (Set.Icc (-τ) c) measurableSet_Icc (A x) :=
      specProjection_apply_domain hA (Set.Icc (-τ) c) measurableSet_Icc x
    have h := (re_inner_apply_bounds_of_subset_Icc hA (Set.Icc (-τ) c)
      measurableSet_Icc (β := -τ) (α := c) Set.Subset.rfl hyK hymem).2
    rwa [hAy] at h
  have hlx := hlim_of_fix (x : H) hfix
  have hlA := hlim_of_fix (A x) hfixA
  exact le_of_tendsto_of_tendsto'
    ((Complex.continuous_re.tendsto _).comp (hlA.inner hlx))
    (((hlx.norm).pow 2).const_mul c) hbound

end LocalHalfLine

end LinearPMap

/-- The bounded positive Gram operator. -/
def gramOperator (X : E0 →L[ℂ] E1) : E0 →L[ℂ] E0 :=
  X.adjoint ∘L X

/-- The Gram operator is self-adjoint. -/
theorem gramOperator_isSelfAdjoint (X : E0 →L[ℂ] E1) :
    IsSelfAdjoint (gramOperator X) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪X.adjoint (X x), y⟫_ℂ = ⟪x, X.adjoint (X y)⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- The Gram quadratic form is the squared image norm. -/
theorem re_inner_gramOperator (X : E0 →L[ℂ] E1) (x : E0) :
    RCLike.re ⟪gramOperator X x, x⟫_ℂ = ‖X x‖ ^ 2 := by
  change RCLike.re ⟪X.adjoint (X x), x⟫_ℂ = ‖X x‖ ^ 2
  rw [ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The bounded Gram operator viewed as an everywhere-defined partial map. -/
def gramLinearPMap (X : E0 →L[ℂ] E1) : E0 →ₗ.[ℂ] E0 :=
  ((gramOperator X : E0 →ₗ[ℂ] E0).toPMap ⊤)

/-- The Gram partial map is everywhere defined: it comes from a bounded operator. -/
@[simp] theorem gramLinearPMap_domain (X : E0 →L[ℂ] E1) :
    (gramLinearPMap X).domain = ⊤ := rfl

/-- On its domain the Gram partial map is the bounded Gram operator. -/
@[simp] theorem gramLinearPMap_apply (X : E0 →L[ℂ] E1)
    (x : (gramLinearPMap X).domain) :
    gramLinearPMap X x = gramOperator X (x : E0) := rfl

/-- The native Tau Ceti self-adjointness proof for the Gram partial map. -/
theorem gramLinearPMap_isSelfAdjoint (X : E0 →L[ℂ] E1) :
    IsSelfAdjoint (gramLinearPMap X) :=
  LinearPMap.isSelfAdjoint_toPMap_top (gramOperator_isSelfAdjoint X)

/-- The native Tau Ceti spectral PVM of `X†X`. -/
noncomputable def gramSpectralPVM (X : E0 →L[ℂ] E1) : ProjValMeasure E0 :=
  LinearPMap.spectralPVM (gramLinearPMap_isSelfAdjoint X)

/-- Definitional bridge between the named Gram PVM and Tau Ceti's pointwise
spectral-projection API.  Keeping this as a named equality avoids repeatedly
asking the elaborator to unfold the full spectral construction through a
`change` tactic. -/
theorem gramSpectralPVM_proj_eq_specProjection (X : E0 →L[ℂ] E1)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (gramSpectralPVM X).proj B hB =
      TauCeti.LinearPMap.specProjection (gramLinearPMap_isSelfAdjoint X) B hB := rfl

/-- A strict lower threshold for `a_n(X)` forces at least `n+1` dimensions in
`E_{X†X}([r²,∞))`. -/
theorem natCast_succ_le_rank_gramProjection_Ici_of_lt_approximationNumber
    (X : E0 →L[ℂ] E1) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < X.approximationNumber n) :
    ((n + 1 : ℕ) : Cardinal) ≤
      ((gramSpectralPVM X).proj (Set.Ici (r ^ 2)) measurableSet_Ici).rank := by
  classical
  let P : E0 →L[ℂ] E0 :=
    (gramSpectralPVM X).proj (Set.Ici (r ^ 2)) measurableSet_Ici
  obtain ⟨s, hrs, v, hv, hV⟩ :=
    X.exists_linearIndependent_lowerBound_of_lt_approximationNumber n hr0 hr
  let V : Submodule ℂ E0 := Submodule.span ℂ (Set.range v)
  let b : Module.Basis (Fin (n + 1)) ℂ V := Module.Basis.span hv
  let W : Submodule ℂ E0 := P.range
  let f : V →ₗ[ℂ] W :=
    { toFun := fun x => ⟨P x, ⟨x, rfl⟩⟩
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by intro c x; apply Subtype.ext; simp }
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    let z : E0 := (x : E0) - (y : E0)
    have hzV : z ∈ V := V.sub_mem x.property y.property
    have hPz : P z = 0 := by
      have hval := congrArg Subtype.val hxy
      change P (x : E0) = P (y : E0) at hval
      simpa [z, map_sub] using sub_eq_zero.mpr hval
    have hzDom : z ∈ (gramLinearPMap X).domain := by
      rw [gramLinearPMap_domain]
      exact Submodule.mem_top
    have henergy := LinearPMap.re_inner_le_of_specProjection_Ici_apply_eq_zero
      (gramLinearPMap_isSelfAdjoint X) (⟨z, hzDom⟩ : (gramLinearPMap X).domain) (by
        rw [← gramSpectralPVM_proj_eq_specProjection X
          (Set.Ici (r ^ 2)) measurableSet_Ici]
        simpa only [P] using hPz)
    have hupper : ‖X z‖ ^ 2 ≤ r ^ 2 * ‖z‖ ^ 2 := by
      calc
        ‖X z‖ ^ 2 = RCLike.re ⟪gramOperator X z, z⟫_ℂ := by
          symm
          exact re_inner_gramOperator X z
        _ = RCLike.re
            ⟪gramLinearPMap X (⟨z, hzDom⟩ : (gramLinearPMap X).domain), z⟫_ℂ := by
          rw [gramLinearPMap_apply]
        _ ≤ r ^ 2 * ‖z‖ ^ 2 := henergy
    have hlower : s * ‖z‖ ≤ ‖X z‖ := hV z hzV
    have hs0 : 0 ≤ s := hr0.trans hrs.le
    have hupper' : ‖X z‖ ^ 2 ≤ (r * ‖z‖) ^ 2 := by
      simpa only [mul_pow] using hupper
    have hupperLinear : ‖X z‖ ≤ r * ‖z‖ :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr0 (norm_nonneg z))).1 hupper'
    have hz0 : ‖z‖ = 0 := by
      nlinarith [hlower.trans hupperLinear, norm_nonneg z]
    have hz : (x : E0) - (y : E0) = 0 := by
      simpa only [z] using norm_eq_zero.mp hz0
    exact sub_eq_zero.mp hz
  have hfb : LinearIndependent ℂ (f ∘ fun i => b i) := by
    exact b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf_injective)
  have hrankW : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ W :=
    (Module.le_rank_iff).2 ⟨fun i => f (b i), hfb⟩
  change ((n + 1 : ℕ) : Cardinal) ≤ P.rank at hrankW
  simpa only [P] using hrankW

/-- A strict upper threshold for `a_n(X)` forces the open upper Gram range
`E_{X†X}((r²,∞))` to have rank at most `n`. -/
theorem rank_gramProjection_Ioi_le_natCast_of_approximationNumber_lt
    (X : E0 →L[ℂ] E1) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : X.approximationNumber n < r) :
    ((gramSpectralPVM X).proj (Set.Ioi (r ^ 2)) measurableSet_Ioi).rank ≤
      (n : Cardinal) := by
  classical
  let P : E0 →L[ℂ] E0 :=
    (gramSpectralPVM X).proj (Set.Ioi (r ^ 2)) measurableSet_Ioi
  by_contra hnot
  have hlt : (n : Cardinal) < P.rank := lt_of_not_ge hnot
  have hnrank : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℂ P.range := by
    change ((n + 1 : ℕ) : Cardinal) ≤ P.rank
    rw [← Cardinal.natCast_add_one_le_iff, ← Nat.cast_add_one] at hlt
    exact hlt
  obtain ⟨g, hg⟩ := (Module.le_rank_iff).1 hnrank
  let v : Fin (n + 1) → E0 := P.range.subtype ∘ g
  have hv : LinearIndependent ℂ v := by
    exact hg.map' P.range.subtype
      (LinearMap.ker_eq_bot.mpr P.range.injective_subtype)
  have hrle : r ≤ X.approximationNumber n := by
    apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent X n v hv
    intro x hxspan hxnorm
    have hspan_le : Submodule.span ℂ (Set.range v) ≤ P.range := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      exact (g i).property
    have hxP : x ∈ P.range := hspan_le hxspan
    have hPx : P x = x := by
      rcases hxP with ⟨y, rfl⟩
      change P (P y) = P y
      simpa only [mul_apply_eq_comp] using
        congrArg (fun T : E0 →L[ℂ] E0 => T y)
          ((gramSpectralPVM X).proj_idem (Set.Ioi (r ^ 2)) measurableSet_Ioi)
    have hzlow :
        (gramSpectralPVM X).proj (Set.Iic (r ^ 2)) measurableSet_Iic x = 0 := by
      let Q : E0 →L[ℂ] E0 :=
        (gramSpectralPVM X).proj (Set.Iic (r ^ 2)) measurableSet_Iic
      have hinter : Set.Iic (r ^ 2) ∩ Set.Ioi (r ^ 2) = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi,
          Set.mem_empty_iff_false, iff_false]
        exact fun ht => (not_lt_of_ge ht.1) ht.2
      have hQP_raw :
          (gramSpectralPVM X).proj (Set.Iic (r ^ 2)) measurableSet_Iic *
              (gramSpectralPVM X).proj (Set.Ioi (r ^ 2)) measurableSet_Ioi = 0 := by
        rw [(gramSpectralPVM X).proj_inter,
          (gramSpectralPVM X).proj_congr hinter
            (measurableSet_Iic.inter measurableSet_Ioi) MeasurableSet.empty,
          (gramSpectralPVM X).proj_empty]
      have hQP : Q * P = 0 := by
        simpa only [Q, P] using hQP_raw
      have hQPx := congrArg (fun T : E0 →L[ℂ] E0 => T x) hQP
      calc
        (gramSpectralPVM X).proj (Set.Iic (r ^ 2)) measurableSet_Iic x =
            (gramSpectralPVM X).proj (Set.Iic (r ^ 2)) measurableSet_Iic (P x) := by
          rw [hPx]
        _ = 0 := by
          simpa only [Q, _root_.mul_apply_eq_comp, zero_apply] using hQPx
    have hxDom : x ∈ (gramLinearPMap X).domain := by
      rw [gramLinearPMap_domain]
      exact Submodule.mem_top
    have henergy := LinearPMap.le_re_inner_of_specProjection_Iic_apply_eq_zero
      (gramLinearPMap_isSelfAdjoint X) (⟨x, hxDom⟩ : (gramLinearPMap X).domain) (by
        rw [← gramSpectralPVM_proj_eq_specProjection X
          (Set.Iic (r ^ 2)) measurableSet_Iic]
        exact hzlow)
    have hlowerSq : r ^ 2 * ‖x‖ ^ 2 ≤ ‖X x‖ ^ 2 := by
      calc
        r ^ 2 * ‖x‖ ^ 2 ≤
            RCLike.re
              ⟪gramLinearPMap X (⟨x, hxDom⟩ : (gramLinearPMap X).domain), x⟫_ℂ :=
          henergy
        _ = RCLike.re ⟪gramOperator X x, x⟫_ℂ := by
          rw [gramLinearPMap_apply]
        _ = ‖X x‖ ^ 2 := re_inner_gramOperator X x
    have hlowerSq' : (r * ‖x‖) ^ 2 ≤ ‖X x‖ ^ 2 := by
      simpa only [mul_pow] using hlowerSq
    have : r * ‖x‖ ≤ ‖X x‖ :=
      (sq_le_sq₀ (mul_nonneg hr0 (norm_nonneg x)) (norm_nonneg _)).1 hlowerSq'
    simpa only [hxnorm, mul_one] using this
  exact (not_le_of_gt hr) hrle

end

end ApproximationNumber
end TauCeti
