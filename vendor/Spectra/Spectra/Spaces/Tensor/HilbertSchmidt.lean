/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Spectra.Spaces.Tensor.Map
import Spectra.SpectralTheory.Antilinear.ConjugateSpace
import Spectra.Operator.AdjointClosure
import Spectra.QuantumMechanics.BornRule.Joint.Basic

/-!
# Rectangular Hilbert--Schmidt operators as a Hilbert tensor product

For complex Hilbert spaces `E` and `F`, the canonical Hilbert space of
rectangular Hilbert--Schmidt maps `F -> E` is

`E tensor Conj F`.

The coordinate-free evaluation map sends `z` to the bounded operator whose
value at `x` is the adjoint, applied to `z`, of the fixed-right-tensor map
`u |-> u tensor toConj x`.  Consequently a pure tensor
`u tensor toConj v` is exactly the rank-one operator `rankOne C u v`.

This file supplies the tensor/operator dictionary needed by the square-norm
Sylvester theorem.  It deliberately contains no spectral-measure machinery.
Left and right multiplication are represented by bounded tensor maps, so a
joint spectral model can be built in a higher module without choosing bases.
-/

open scoped InnerProductSpace ComplexConjugate BigOperators

namespace Spectra
namespace HilbertSchmidtTensor

noncomputable section

universe u v w

variable {E : Type u} {F : Type v} {G : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The canonical Hilbert space modelling Hilbert--Schmidt maps `F -> E`. -/
abbrev Space (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :=
  E ⊗̂[ℂ] Conj F

/-- A bounded operator transported to conjugate Hilbert spaces. -/
def Conj.map (A : E →L[ℂ] F) : Conj E →L[ℂ] Conj F :=
  LinearMap.mkContinuous
    { toFun := fun x => Conj.toConj (A (Conj.ofConj x))
      map_add' := by
        intro x y
        apply Conj.ofConj_injective
        simp
      map_smul' := by
        intro c x
        apply Conj.ofConj_injective
        simp [map_smul] }
    ‖A‖
    (by
      intro x
      change ‖A (Conj.ofConj x)‖ ≤ ‖A‖ * ‖x‖
      simpa only [Conj.norm_ofConj] using A.le_opNorm (Conj.ofConj x))

@[simp]
theorem Conj.map_apply (A : E →L[ℂ] F) (x : Conj E) :
    Conj.map A x = Conj.toConj (A (Conj.ofConj x)) :=
  rfl

@[simp]
theorem Conj.map_id :
    Conj.map (ContinuousLinearMap.id ℂ E) = ContinuousLinearMap.id ℂ (Conj E) := by
  ext x
  apply Conj.ofConj_injective
  simp

@[simp]
theorem Conj.map_comp (A : E →L[ℂ] F) (B : F →L[ℂ] G) :
    Conj.map (B ∘L A) = Conj.map B ∘L Conj.map A := by
  ext x
  apply Conj.ofConj_injective
  simp

@[simp]
theorem Conj.map_adjoint (A : E →L[ℂ] F) :
    Conj.map A.adjoint = (Conj.map A).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff
    (Conj.map A.adjoint) (Conj.map A)).2
  intro x y
  change ⟪A.adjoint (Conj.ofConj x), Conj.ofConj y⟫_ℂ =
    ⟪Conj.ofConj x, A (Conj.ofConj y)⟫_ℂ
  exact ContinuousLinearMap.adjoint_inner_left A _ _

private theorem Conj.norm_map_le (A : E →L[ℂ] F) : ‖Conj.map A‖ ≤ ‖A‖ := by
  apply (Conj.map A).opNorm_le_bound (norm_nonneg A)
  intro x
  change ‖A (Conj.ofConj x)‖ ≤ ‖A‖ * ‖x‖
  simpa only [Conj.norm_ofConj] using A.le_opNorm (Conj.ofConj x)

@[simp]
theorem Conj.norm_map (A : E →L[ℂ] F) : ‖Conj.map A‖ = ‖A‖ := by
  apply le_antisymm
  · exact Conj.norm_map_le A
  · calc
      ‖A‖ = ‖Conj.map (Conj.map A)‖ := by
        congr 1
        ext x
        rfl
      _ ≤ ‖Conj.map A‖ := Conj.norm_map_le (Conj.map A)

/-- Fixing the second factor of the pure tensor gives a bounded map in the
first factor. -/
def rightTensor (x : F) : E →L[ℂ] Space E F :=
  (ContinuousLinearMap.apply ℂ (Space E F) (Conj.toConj x)) ∘L
    HilbertTensor.tmulL ℂ E (Conj F)

@[simp]
theorem rightTensor_apply (x : F) (u : E) :
    rightTensor x u = u ⊗̂ₜ[ℂ] Conj.toConj x :=
  rfl

@[simp]
theorem rightTensor_add (x y : F) :
    rightTensor (E := E) (x + y) =
      rightTensor (E := E) x + rightTensor (E := E) y := by
  ext u
  simp [rightTensor_apply, HilbertTensor.tmul_add]

private theorem toConj_smul (c : ℂ) (x : F) :
    Conj.toConj (c • x) = starRingEnd ℂ c • Conj.toConj x := by
  apply Conj.ofConj_injective
  simp

@[simp]
theorem rightTensor_smul (c : ℂ) (x : F) :
    rightTensor (E := E) (c • x) =
      starRingEnd ℂ c • rightTensor (E := E) x := by
  ext u
  simp [rightTensor_apply, toConj_smul, HilbertTensor.tmul_smul]

/-- The fixed-right-tensor map has norm at most the norm of the fixed vector. -/
theorem norm_rightTensor_le (x : F) : ‖rightTensor (E := E) x‖ ≤ ‖x‖ := by
  apply (rightTensor x).opNorm_le_bound (norm_nonneg x)
  intro u
  simp [rightTensor_apply, HilbertTensor.norm_tmul, mul_comm]

/-- The operator represented by a Hilbert tensor. -/
def toOperatorLinear (z : Space E F) : F →ₗ[ℂ] E where
  toFun := fun x => (rightTensor x).adjoint z
  map_add' := by
    intro x y
    rw [rightTensor_add (E := E)]
    simp
  map_smul' := by
    intro c x
    rw [rightTensor_smul (E := E)]
    simp

/-- The tensor/operator map is bounded from the Hilbert tensor norm to the
ordinary operator norm. -/
def toOperator (z : Space E F) : F →L[ℂ] E :=
  LinearMap.mkContinuous (toOperatorLinear z) ‖z‖ (by
    intro x
    calc
      ‖(rightTensor x).adjoint z‖
          ≤ ‖(rightTensor x).adjoint‖ * ‖z‖ :=
        (rightTensor x).adjoint.le_opNorm z
      _ = ‖rightTensor x‖ * ‖z‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ ‖x‖ * ‖z‖ :=
        mul_le_mul_of_nonneg_right (norm_rightTensor_le (E := E) x)
          (norm_nonneg z)
      _ = ‖z‖ * ‖x‖ := mul_comm _ _)

@[simp]
theorem toOperator_apply (z : Space E F) (x : F) :
    toOperator z x = (rightTensor x).adjoint z :=
  rfl

/-- The tensor/operator map, bundled as a contraction. -/
def toOperatorL : Space E F →L[ℂ] (F →L[ℂ] E) :=
  LinearMap.mkContinuous
    { toFun := toOperator
      map_add' := by
        intro z w
        ext x
        simp [toOperator_apply]
      map_smul' := by
        intro c z
        ext x
        simp [toOperator_apply] }
    1
    (by
      intro z
      apply (toOperator z).opNorm_le_bound (norm_nonneg z)
      intro x
      exact (toOperator z).le_opNorm x)

@[simp]
theorem toOperatorL_apply (z : Space E F) :
    toOperatorL z = toOperator z :=
  rfl

/-- The represented operator has operator norm at most the tensor norm. -/
theorem norm_toOperator_le (z : Space E F) : ‖toOperator z‖ ≤ ‖z‖ := by
  apply (toOperator z).opNorm_le_bound (norm_nonneg z)
  intro x
  calc
    ‖(rightTensor x).adjoint z‖
        ≤ ‖(rightTensor x).adjoint‖ * ‖z‖ :=
      (rightTensor x).adjoint.le_opNorm z
    _ = ‖rightTensor x‖ * ‖z‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ ‖x‖ * ‖z‖ :=
      mul_le_mul_of_nonneg_right (norm_rightTensor_le (E := E) x)
        (norm_nonneg z)
    _ = ‖z‖ * ‖x‖ := mul_comm _ _

/-- Pure tensors represent the corresponding rank-one operators. -/
theorem toOperator_tmul (u : E) (v : F) :
    toOperator (u ⊗̂ₜ[ℂ] Conj.toConj v) =
      InnerProductSpace.rankOne ℂ u v := by
  ext x
  refine ext_inner_right ℂ fun w => ?_
  rw [toOperator_apply, ContinuousLinearMap.adjoint_inner_left]
  simp [rightTensor_apply, HilbertTensor.inner_tmul_tmul,
    Conj.inner_def, InnerProductSpace.rankOne_apply,
    inner_smul_left, inner_conj_symm]
  ring

private theorem inner_tmul_eq_zero_of_toOperator_eq_zero
    {z : Space E F} (hz : toOperator z = 0) (u : E) (v : F) :
    ⟪u ⊗̂ₜ[ℂ] Conj.toConj v, z⟫_ℂ = 0 := by
  have hx := congrArg (fun T : F →L[ℂ] E => T v) hz
  have hw := congrArg (fun y : E => ⟪y, u⟫_ℂ) hx
  simpa [toOperator_apply, ContinuousLinearMap.adjoint_inner_left] using hw

/-- The tensor/operator representation is faithful. -/
theorem toOperator_injective :
    Function.Injective (toOperator (E := E) (F := F)) := by
  intro z w hzw
  apply sub_eq_zero.mp
  have hzero : toOperator (z - w) = 0 := by
    simpa using sub_eq_zero.mpr hzw
  let K : Submodule ℂ (Space E F) :=
    Submodule.span ℂ (Set.range fun p : E × Conj F => p.1 ⊗̂ₜ[ℂ] p.2)
  have hzorth : z - w ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
        rcases ht with ⟨⟨u, cv⟩, rfl⟩
        rw [← Conj.toConj_ofConj cv]
        exact inner_tmul_eq_zero_of_toOperator_eq_zero hzero u (Conj.ofConj cv)
    | zero => simp
    | add x y hx hy => simp [inner_add_left, hx, hy]
    | smul c x hx => simp [inner_smul_left, hx]
  have hzclosure : z - w ∈ K.topologicalClosureᗮ := by
    rwa [orthogonal_topologicalClosure_eq]
  have hKtop : K.topologicalClosure = ⊤ :=
    HilbertTensor.span_tmul_topologicalClosure
  rw [hKtop, Submodule.top_orthogonal_eq_bot] at hzclosure
  exact hzclosure

/-- The tensor/operator map is an injective bounded linear map. -/
def toOperatorEmbedding : Space E F →L[ℂ] (F →L[ℂ] E) :=
  toOperatorL

/-- Left tensor action is left composition of represented operators. -/
theorem toOperator_mapL_left
    (A : E →L[ℂ] G) (z : Space E F) :
    toOperator (HilbertTensor.mapL A (ContinuousLinearMap.id ℂ (Conj F)) z) =
      A ∘L toOperator z := by
  apply HilbertTensor.dense_span_tmul.induction_on
  · intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
        rcases ht with ⟨⟨u, cv⟩, rfl⟩
        rw [← Conj.toConj_ofConj cv]
        simp [HilbertTensor.mapL_tmul, toOperator_tmul,
          InnerProductSpace.comp_rankOne]
    | zero => simp
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    | smul c x hx => simpa using congrArg (fun q => c • q) hx
  · exact isClosed_eq (continuous_const.sub
      ((toOperatorL.comp (HilbertTensor.mapL A
        (ContinuousLinearMap.id ℂ (Conj F)))).continuous.sub
        ((ContinuousLinearMap.compL ℂ F E G A).comp toOperatorL).continuous))
  · exact z

/-- Right tensor action by the conjugate adjoint is right composition of
represented operators. -/
theorem toOperator_mapL_right
    (B : G →L[ℂ] F) (z : Space E F) :
    toOperator (HilbertTensor.mapL (ContinuousLinearMap.id ℂ E)
      (Conj.map B.adjoint) z) =
      toOperator z ∘L B := by
  apply HilbertTensor.dense_span_tmul.induction_on
  · intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
        rcases ht with ⟨⟨u, cv⟩, rfl⟩
        rw [← Conj.toConj_ofConj cv]
        simp [HilbertTensor.mapL_tmul, toOperator_tmul,
          InnerProductSpace.rankOne_comp, Conj.inner_def]
    | zero => simp
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
    | smul c x hx => simpa using congrArg (fun q => c • q) hx
  · exact isClosed_eq (continuous_const.sub
      ((toOperatorL.comp (HilbertTensor.mapL
        (ContinuousLinearMap.id ℂ E) (Conj.map B.adjoint))).continuous.sub
        ((ContinuousLinearMap.compRightL ℂ G F E B).comp toOperatorL).continuous))
  · exact z

/-- A finite sum of pure tensors represents a finite-rank operator. -/
theorem rank_toOperator_sum_tmul_le
    {ι : Type*} (s : Finset ι) (u : ι → E) (v : ι → F) :
    (toOperator (∑ i ∈ s, u i ⊗̂ₜ[ℂ] Conj.toConj (v i))).rank ≤ s.card := by
  simp_rw [map_sum, toOperator_tmul]
  let T : F →L[ℂ] E := ∑ i ∈ s, InnerProductSpace.rankOne ℂ (u i) (v i)
  change T.rank ≤ (s.card : Cardinal)
  calc
    T.rank ≤ Module.rank ℂ (Submodule.span ℂ (u '' (s : Set ι))) := by
      exact LinearMap.rank_le_of_range_le (by
        rintro y ⟨x, rfl⟩
        change (∑ i ∈ s, InnerProductSpace.rankOne ℂ (u i) (v i)) x ∈
          Submodule.span ℂ (u '' (s : Set ι))
        simp only [Finset.sum_apply, InnerProductSpace.rankOne_apply]
        exact Submodule.sum_mem _ fun i hi =>
          Submodule.smul_mem _ _
            (Submodule.subset_span ⟨i, hi, rfl⟩))
    _ ≤ (s.card : Cardinal) := by
      simpa using Submodule.rank_span_le_card (R := ℂ) (s.image u)


/-! ## Column expansion in an arbitrary Hilbert basis -/

/-- The `i`th orthogonal column tensor of `z`. -/
def columnTensor {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) (i : ι) : Space E F :=
  toOperator z (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i)

/-- Distinct column tensors are orthogonal. -/
theorem inner_columnTensor_eq_zero {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) {i j : ι} (hij : i ≠ j) :
    ⟪columnTensor b z i, columnTensor b z j⟫_ℂ = 0 := by
  simp [columnTensor, HilbertTensor.inner_tmul_tmul, Conj.inner_def,
    b.orthonormal.inner_right hij]

/-- The column tensors resolve the identity on `E tensor Conj F`. -/
theorem hasSum_columnTensor {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) :
    HasSum (columnTensor b z) z := by
  let S : Space E F →L[ℂ] Space E F :=
    ContinuousLinearMap.id ℂ (Space E F)
  have hpure : ∀ u : E, ∀ v : F,
      HasSum (columnTensor b (u ⊗̂ₜ[ℂ] Conj.toConj v))
        (u ⊗̂ₜ[ℂ] Conj.toConj v) := by
    intro u v
    have hv := (b.hasSum_repr v)
    have hmap := (HilbertTensor.tmulL ℂ E (Conj F) u).hasSum
      ((Conj.toConjₗᵢ F).toContinuousLinearEquiv.hasSum hv)
    simpa [columnTensor, toOperator_tmul, InnerProductSpace.rankOne_apply,
      HilbertTensor.tmul_smul, Conj.inner_def, inner_conj_symm] using hmap
  have hspan : ∀ t ∈ Submodule.span ℂ
      (Set.range fun p : E × F => p.1 ⊗̂ₜ[ℂ] Conj.toConj p.2),
      HasSum (columnTensor b t) t := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
        rcases ht with ⟨⟨u, v⟩, rfl⟩
        exact hpure u v
    | zero => simpa [columnTensor]
    | add x y hx hy =>
        simpa [columnTensor, map_add, HilbertTensor.add_tmul] using hx.add hy
    | smul c x hx =>
        simpa [columnTensor, map_smul, HilbertTensor.smul_tmul] using hx.smul c
  have hclosed : IsClosed {t : Space E F | HasSum (columnTensor b t) t} := by
    rw [isClosed_iff_clusterPt]
    intro t ht
    have hpartial : ∀ s : Finset ι,
        ‖∑ i ∈ s, columnTensor b t i‖ ≤ ‖t‖ := by
      intro s
      have hproj : ∑ i ∈ s, columnTensor b t i =
          HilbertTensor.mapL (ContinuousLinearMap.id ℂ E)
            ((Submodule.span ℂ (b '' (s : Set ι))).starProjection) t := by
        apply toOperator_injective
        ext x
        simp [columnTensor, toOperator_mapL_right, HilbertBasis.sum_repr]
      rw [hproj]
      calc
        ‖HilbertTensor.mapL (ContinuousLinearMap.id ℂ E)
            ((Submodule.span ℂ (b '' (s : Set ι))).starProjection) t‖
            ≤ ‖HilbertTensor.mapL (ContinuousLinearMap.id ℂ E)
                ((Submodule.span ℂ (b '' (s : Set ι))).starProjection)‖ * ‖t‖ :=
              (HilbertTensor.mapL _ _).le_opNorm t
        _ ≤ ‖t‖ := by
          rw [HilbertTensor.norm_mapL, norm_id]
          have hp := (Submodule.span ℂ (b '' (s : Set ι))).norm_starProjection_le_one
          nlinarith [norm_nonneg t]
    exact HasSum.isClosed_of_uniformly_bounded_partialSums
      (f := columnTensor b) (C := 1) hpartial ht
  exact hclosed.mem_of_superset
    (HilbertTensor.dense_span_tmul.mono fun t ht => by
      change t ∈ Submodule.span ℂ
        (Set.range fun p : E × F => p.1 ⊗̂ₜ[ℂ] Conj.toConj p.2)
      simpa only [Set.range_comp] using ht)
    (hspan z)

/-- Parseval for the column decomposition of a tensor. -/
theorem norm_sq_eq_tsum_column_norm_sq {ι : Type*}
    (b : HilbertBasis ι ℂ F) (z : Space E F) :
    ‖z‖ ^ 2 = ∑' i, ‖toOperator z (b i)‖ ^ 2 := by
  have hsum := hasSum_columnTensor b z
  have hortho : Pairwise fun i j =>
      ⟪columnTensor b z i, columnTensor b z j⟫_ℂ = 0 := by
    intro i j hij
    exact inner_columnTensor_eq_zero b z hij
  have hpyth := hsum.norm_sq_eq_tsum_of_orthogonal hortho
  simpa [columnTensor, HilbertTensor.norm_tmul, b.norm_apply,
    mul_one, one_pow] using hpyth

/-- A basis-square-summable operator determines a tensor by its column series. -/
noncomputable def ofOperator {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) : Space E F :=
  ∑' i, A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i)

private theorem summable_columnSeries {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    Summable fun i => A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i) := by
  apply summable_of_pairwise_orthogonal_of_summable_norm_sq
  · intro i j hij
    simp [HilbertTensor.inner_tmul_tmul, Conj.inner_def,
      b.orthonormal.inner_right hij]
  · simpa [HilbertTensor.norm_tmul, b.norm_apply, mul_one, one_pow] using hA

/-- The column-series tensor represents the original operator. -/
theorem toOperator_ofOperator {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    toOperator (ofOperator b A hA) = A := by
  ext x
  have hseries := summable_columnSeries b A hA
  rw [ofOperator, ← toOperatorL_apply, map_tsum hseries]
  simp_rw [toOperator_tmul, InnerProductSpace.rankOne_apply]
  have hrepr := A.hasSum (b.hasSum_repr x)
  simpa only [map_smul, b.repr_apply_apply] using hrepr.tsum_eq

/-- The tensor reconstructed from the columns of a represented operator is the
original tensor. -/
theorem ofOperator_toOperator {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) :
    ofOperator b (toOperator z)
      ((hasSum_columnTensor b z).summable.norm_sq) = z := by
  apply toOperator_injective
  rw [toOperator_ofOperator]

/-- The Hilbert tensor norm is exactly the basis Hilbert--Schmidt norm. -/
theorem norm_ofOperator_sq {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    ‖ofOperator b A hA‖ ^ 2 = ∑' i, ‖A (b i)‖ ^ 2 := by
  rw [norm_sq_eq_tsum_column_norm_sq b]
  simp [toOperator_ofOperator b A hA]

/-- Basis-square-summability is equivalent to representability by a unique
Hilbert tensor. -/
theorem existsUnique_tensor_iff_summable_columns {ι : Type*}
    (b : HilbertBasis ι ℂ F) (A : F →L[ℂ] E) :
    (∃! z : Space E F, toOperator z = A) ↔
      Summable (fun i => ‖A (b i)‖ ^ 2) := by
  constructor
  · rintro ⟨z, rfl, _⟩
    exact (hasSum_columnTensor b z).summable.norm_sq
  · intro hA
    refine ⟨ofOperator b A hA, toOperator_ofOperator b A hA, ?_⟩
    intro z hz
    exact toOperator_injective (hz.trans (toOperator_ofOperator b A hA).symm)

end

end HilbertSchmidtTensor
end Spectra
