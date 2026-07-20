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

/- The pure-tensor notation `x ⊗̂ₜ[𝕜] y` is scoped to `Spectra.HilbertTensor`, not to
`Spectra`, so being inside `namespace Spectra` activates `⊗̂[𝕜]` but not `⊗̂ₜ[𝕜]`. -/
open scoped HilbertTensor

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
  -- The inner product on `Conj E` is the *swapped* one, `⟪x, y⟫ = ⟪ofConj y, ofConj x⟫`,
  -- so the obligation is the `adjoint_inner_right` orientation, not `adjoint_inner_left`.
  simp only [Conj.inner_def, Conj.map_apply, Conj.ofConj_toConj]
  exact ContinuousLinearMap.adjoint_inner_right A _ _

/-- The norm on `Conj E` is the norm on `E`; `toConj` is the identity on vectors. -/
@[simp]
theorem Conj.norm_toConj (x : E) : ‖Conj.toConj x‖ = ‖x‖ := rfl

private theorem Conj.norm_map_le (A : E →L[ℂ] F) : ‖Conj.map A‖ ≤ ‖A‖ := by
  apply (Conj.map A).opNorm_le_bound (norm_nonneg A)
  intro x
  change ‖A (Conj.ofConj x)‖ ≤ ‖A‖ * ‖x‖
  simpa only [Conj.norm_ofConj] using A.le_opNorm (Conj.ofConj x)

@[simp]
theorem Conj.norm_map (A : E →L[ℂ] F) : ‖Conj.map A‖ = ‖A‖ := by
  refine le_antisymm (Conj.norm_map_le A) ?_
  -- The reverse bound is proved directly.  Passing through `Conj.map (Conj.map A)` is
  -- not available: that operator has type `Conj (Conj E) →L[ℂ] Conj (Conj F)`, which is
  -- not the type of `A`, so no congruence relates their norms.
  apply A.opNorm_le_bound (norm_nonneg _)
  intro x
  simpa only [Conj.map_apply, Conj.ofConj_toConj, Conj.norm_toConj]
    using (Conj.map A).le_opNorm (Conj.toConj x)

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
  simp only [rightTensor_apply, ContinuousLinearMap.add_apply]
  -- `Conj.toConj` is the identity on vectors, so `toConj (x + y)` is already
  -- `toConj x + toConj y`; `simp` cannot see this and leaves the sum unsplit.
  exact HilbertTensor.tmul_add u (Conj.toConj x) (Conj.toConj y)

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
  rw [rightTensor_apply, HilbertTensor.norm_tmul, Conj.norm_toConj]
  exact le_of_eq (mul_comm _ _)

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
    -- `adjoint` is conjugate-linear, so the conjugated scalar comes back unconjugated.
    rw [map_smulₛₗ ContinuousLinearMap.adjoint]
    simp

/-- The defining estimate for the tensor/operator map, stated on the underlying
linear map so that both the bundled operator and its norm bound can cite it. -/
private theorem norm_toOperatorLinear_le (z : Space E F) (x : F) :
    ‖toOperatorLinear z x‖ ≤ ‖z‖ * ‖x‖ :=
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

/-- The tensor/operator map is bounded from the Hilbert tensor norm to the
ordinary operator norm. -/
def toOperator (z : Space E F) : F →L[ℂ] E :=
  LinearMap.mkContinuous (toOperatorLinear z) ‖z‖ (norm_toOperatorLinear_le z)

@[simp]
theorem toOperator_apply (z : Space E F) (x : F) :
    toOperator z x = (rightTensor x).adjoint z :=
  rfl

/-- The represented operator has operator norm at most the tensor norm. -/
theorem norm_toOperator_le (z : Space E F) : ‖toOperator z‖ ≤ ‖z‖ :=
  LinearMap.mkContinuous_norm_le (toOperatorLinear z) (norm_nonneg z)
    (norm_toOperatorLinear_le z)

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
      rw [one_mul]
      -- Bounding by `‖toOperator z‖` here would assume the conclusion; the honest
      -- bound is the `mkContinuous` constant `‖z‖`.
      exact norm_toOperator_le z)

@[simp]
theorem toOperatorL_apply (z : Space E F) :
    toOperatorL z = toOperator z :=
  rfl

/-! The tensor/operator map is linear.  These are stated separately because
`toOperator` is the unbundled map, so `map_add` and friends do not apply to it
directly; the span inductions below need them as `simp` lemmas. -/

@[simp]
theorem toOperator_zero : toOperator (0 : Space E F) = 0 := by
  simpa only [toOperatorL_apply] using map_zero (toOperatorL (E := E) (F := F))

@[simp]
theorem toOperator_add (z w : Space E F) :
    toOperator (z + w) = toOperator z + toOperator w := by
  simpa only [toOperatorL_apply] using map_add toOperatorL z w

@[simp]
theorem toOperator_smul (c : ℂ) (z : Space E F) :
    toOperator (c • z) = c • toOperator z := by
  simpa only [toOperatorL_apply] using map_smul toOperatorL c z

@[simp]
theorem toOperator_sum {ι : Type*} (s : Finset ι) (f : ι → Space E F) :
    toOperator (∑ i ∈ s, f i) = ∑ i ∈ s, toOperator (f i) := by
  simpa only [toOperatorL_apply] using map_sum toOperatorL f s

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

/-- The pure-tensor formula with the second factor left in the conjugate space.
The span inductions below produce this shape, and substituting the conjugate
variable is not stable: `Conj.toConj_ofConj` is a `simp` lemma, so any rewrite
introducing `toConj (ofConj _)` is immediately undone. -/
@[simp]
theorem toOperator_tmul' (u : E) (cv : Conj F) :
    toOperator (u ⊗̂ₜ[ℂ] cv) =
      InnerProductSpace.rankOne ℂ u (Conj.ofConj cv) :=
  toOperator_tmul u (Conj.ofConj cv)

/-- The conjugate transport commutes with taking adjoints, in the form the
span inductions need: `simp` normalises towards `(Conj.map B).adjoint`, so the
`Conj.map B.adjoint` orientation is not available to it. -/
@[simp]
theorem Conj.ofConj_adjoint_map (B : E →L[ℂ] F) (cv : Conj F) :
    Conj.ofConj ((Conj.map B).adjoint cv) = B.adjoint (Conj.ofConj cv) := by
  rw [← Conj.map_adjoint]
  rfl

private theorem inner_tmul_eq_zero_of_toOperator_eq_zero
    {z : Space E F} (hz : toOperator z = 0) (u : E) (v : F) :
    ⟪u ⊗̂ₜ[ℂ] Conj.toConj v, z⟫_ℂ = 0 := by
  have hx : toOperator z v = 0 := by rw [hz]; rfl
  calc ⟪u ⊗̂ₜ[ℂ] Conj.toConj v, z⟫_ℂ
      = ⟪rightTensor v u, z⟫_ℂ := rfl
    _ = ⟪u, (rightTensor v).adjoint z⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = ⟪u, toOperator z v⟫_ℂ := rfl
    _ = 0 := by rw [hx, inner_zero_right]

/-- The tensor/operator representation is faithful. -/
theorem toOperator_injective :
    Function.Injective (toOperator (E := E) (F := F)) := by
  intro z w hzw
  apply sub_eq_zero.mp
  have hzero : toOperator (z - w) = 0 := by
    have h : toOperatorL (z - w) = 0 := by
      rw [map_sub, toOperatorL_apply, toOperatorL_apply, hzw, sub_self]
    simpa only [toOperatorL_apply] using h
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
    -- `span_induction` binds the *membership* proofs before the induction
    -- hypotheses; naming only two binders captures the memberships and leaves
    -- the hypotheses inaccessible.
    | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
    | smul c x _ hx => simp [inner_smul_left, hx]
  have hzclosure : z - w ∈ K.topologicalClosureᗮ := by
    rwa [Submodule.orthogonal_closure]
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
  -- `Dense.induction` is `elab_as_elim`, so the motive has to be supplied explicitly;
  -- `apply` cannot abstract `z` out of the goal on its own.
  refine HilbertTensor.dense_span_tmul.induction
    (P := fun t => toOperator (HilbertTensor.mapL A
      (ContinuousLinearMap.id ℂ (Conj F)) t) = A ∘L toOperator t) ?_ ?_ z
  · intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
        rcases ht with ⟨⟨u, cv⟩, rfl⟩
        -- Substitute rather than rewrite: `Conj.toConj_ofConj` is itself a `simp`
        -- lemma, so `rw [← Conj.toConj_ofConj cv]` is undone by the `simp` below.
        simp [HilbertTensor.mapL_tmul, toOperator_tmul',
          InnerProductSpace.comp_rankOne]
    | zero => simp
    | add x y _ _ hx hy =>
        simp only [map_add, toOperator_add, hx, hy, ContinuousLinearMap.comp_add]
    | smul c x _ hx =>
        simp only [map_smul, toOperator_smul, hx, ContinuousLinearMap.comp_smul]
  · exact isClosed_eq
      (toOperatorL.comp
        (HilbertTensor.mapL A (ContinuousLinearMap.id ℂ (Conj F)))).continuous
      ((ContinuousLinearMap.compL ℂ F E G A).comp toOperatorL).continuous

/-- Right tensor action by the conjugate adjoint is right composition of
represented operators. -/
theorem toOperator_mapL_right
    (B : G →L[ℂ] F) (z : Space E F) :
    toOperator (HilbertTensor.mapL (ContinuousLinearMap.id ℂ E)
      (Conj.map B.adjoint) z) =
      toOperator z ∘L B := by
  refine HilbertTensor.dense_span_tmul.induction
    (P := fun t => toOperator (HilbertTensor.mapL (ContinuousLinearMap.id ℂ E)
      (Conj.map B.adjoint) t) = toOperator t ∘L B) ?_ ?_ z
  · intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
        rcases ht with ⟨⟨u, cv⟩, rfl⟩
        simp [HilbertTensor.mapL_tmul, toOperator_tmul',
          InnerProductSpace.rankOne_comp, Conj.inner_def]
    | zero => simp
    | add x y _ _ hx hy =>
        simp only [map_add, toOperator_add, hx, hy, ContinuousLinearMap.add_comp]
    | smul c x _ hx =>
        simp only [map_smul, toOperator_smul, hx, ContinuousLinearMap.smul_comp]
  · -- Right composition by `B` as a bounded operator: `compL` composes on the left,
    -- so the flipped form is what sends `T` to `T ∘L B`.
    exact isClosed_eq
      (toOperatorL.comp (HilbertTensor.mapL
        (ContinuousLinearMap.id ℂ E) (Conj.map B.adjoint))).continuous
      (((ContinuousLinearMap.compL ℂ G F E).flip B).comp toOperatorL).continuous

/-- A finite sum of pure tensors represents a finite-rank operator. -/
theorem rank_toOperator_sum_tmul_le
    {ι : Type*} (s : Finset ι) (u : ι → E) (v : ι → F) :
    (toOperator (∑ i ∈ s, u i ⊗̂ₜ[ℂ] Conj.toConj (v i))).rank ≤ s.card := by
  classical
  have happly : ∀ x : F,
      toOperator (∑ i ∈ s, u i ⊗̂ₜ[ℂ] Conj.toConj (v i)) x
        = ∑ i ∈ s, ⟪v i, x⟫_ℂ • u i := by
    intro x
    rw [toOperator_sum]
    simp
  have hrange :
      LinearMap.range
          (toOperator (∑ i ∈ s, u i ⊗̂ₜ[ℂ] Conj.toConj (v i))).toLinearMap ≤
        Submodule.span ℂ ((s.image u : Finset E) : Set E) := by
    rintro _ ⟨x, rfl⟩
    change toOperator (∑ i ∈ s, u i ⊗̂ₜ[ℂ] Conj.toConj (v i)) x ∈ _
    rw [happly]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem u hi)))
  calc (toOperator (∑ i ∈ s, u i ⊗̂ₜ[ℂ] Conj.toConj (v i))).rank
      ≤ Module.rank ℂ (Submodule.span ℂ ((s.image u : Finset E) : Set E)) :=
        Submodule.rank_mono hrange
    _ ≤ ((s.image u).card : Cardinal) := rank_span_finset_le _
    _ ≤ (s.card : Cardinal) := by exact_mod_cast Finset.card_image_le


/-! ## Column expansion in an arbitrary Hilbert basis -/

/-- Tensoring on the right with a fixed unit vector of the conjugate space is a
linear isometry.  Packaging the columns this way makes them an
`OrthogonalFamily`, which is the interface Mathlib offers for Pythagoras and for
square-summability. -/
private def tmulRightₗᵢ (w : Conj F) (hw : ‖w‖ = 1) : E →ₗᵢ[ℂ] Space E F where
  toFun u := u ⊗̂ₜ[ℂ] w
  map_add' u u' := HilbertTensor.add_tmul u u' w
  map_smul' c u := HilbertTensor.smul_tmul c u w
  norm_map' u := by
    -- The structure-instance field is still the raw anonymous constructor here, so
    -- the pure-tensor norm lemma has to be exposed by a definitional change first.
    change ‖u ⊗̂ₜ[ℂ] w‖ = ‖u‖
    rw [HilbertTensor.norm_tmul, hw, mul_one]

@[simp]
private theorem tmulRightₗᵢ_apply (w : Conj F) (hw : ‖w‖ = 1) (u : E) :
    tmulRightₗᵢ (E := E) w hw u = u ⊗̂ₜ[ℂ] w :=
  rfl

/-- The `i`th column embedding of a Hilbert basis: tensoring on the right with
the `i`th conjugate basis vector. -/
private def columnEmbedding {ι : Type*} (b : HilbertBasis ι ℂ F) (i : ι) :
    E →ₗᵢ[ℂ] Space E F :=
  tmulRightₗᵢ (Conj.toConj (b i)) (by rw [Conj.norm_toConj]; exact b.orthonormal.1 i)

private theorem orthogonalFamily_columnEmbedding {ι : Type*} (b : HilbertBasis ι ℂ F) :
    OrthogonalFamily ℂ (fun _ : ι => E) (columnEmbedding (E := E) b) := by
  intro i j hij x y
  -- The inner product on `Conj F` is the swapped one, so the surviving factor is
  -- `⟪b j, b i⟫`, not `⟪b i, b j⟫`.
  simp [columnEmbedding, HilbertTensor.inner_tmul_tmul, Conj.inner_def,
    b.orthonormal.inner_eq_zero hij.symm]

/-- The `i`th orthogonal column tensor of `z`. -/
def columnTensor {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) (i : ι) : Space E F :=
  toOperator z (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i)

private theorem columnTensor_eq {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) (i : ι) :
    columnTensor b z i = columnEmbedding b i (toOperator z (b i)) :=
  rfl

/-- Distinct column tensors are orthogonal. -/
theorem inner_columnTensor_eq_zero {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) {i j : ι} (hij : i ≠ j) :
    ⟪columnTensor b z i, columnTensor b z j⟫_ℂ = 0 := by
  simp [columnTensor, HilbertTensor.inner_tmul_tmul, Conj.inner_def,
    b.orthonormal.inner_eq_zero hij.symm]

/-- Pythagoras for the finite partial sums of the column expansion. -/
theorem norm_sum_columnTensor_sq {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) (s : Finset ι) :
    ‖∑ i ∈ s, columnTensor b z i‖ ^ 2 = ∑ i ∈ s, ‖toOperator z (b i)‖ ^ 2 := by
  simpa only [← columnTensor_eq] using
    (orthogonalFamily_columnEmbedding (E := E) b).norm_sum
      (fun i => toOperator z (b i)) s

/-- Pairing a pure tensor against `z` on the left evaluates the represented
operator. -/
private theorem inner_tmul_left_eq (u : E) (v : F) (z : Space E F) :
    ⟪u ⊗̂ₜ[ℂ] Conj.toConj v, z⟫_ℂ = ⟪u, toOperator z v⟫_ℂ := by
  rw [toOperator_apply]
  exact (ContinuousLinearMap.adjoint_inner_right (rightTensor v) u z).symm

/-- Bessel's inequality for the column expansion: every finite partial sum of
column norms is bounded by the tensor norm. -/
theorem sum_column_norm_sq_le {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) (s : Finset ι) :
    ∑ i ∈ s, ‖toOperator z (b i)‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have hpy := norm_sum_columnTensor_sq b z s
  have hnonneg : (0 : ℝ) ≤ ∑ i ∈ s, ‖toOperator z (b i)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- The partial sum pairs with `z` to exactly its own squared norm.
  have hinner : ⟪∑ i ∈ s, columnTensor b z i, z⟫_ℂ
      = ((∑ i ∈ s, ‖toOperator z (b i)‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [columnTensor, inner_tmul_left_eq]
    exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (toOperator z (b i))
  have hcs : ‖⟪∑ i ∈ s, columnTensor b z i, z⟫_ℂ‖
      ≤ ‖∑ i ∈ s, columnTensor b z i‖ * ‖z‖ := norm_inner_le_norm (𝕜 := ℂ) _ _
  rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hcs
  -- Cauchy--Schwarz plus Pythagoras bounds the partial sum by `‖z‖`.
  have hle : ‖∑ i ∈ s, columnTensor b z i‖ ≤ ‖z‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (∑ i ∈ s, columnTensor b z i)) with h | h
    · rw [← h]; exact norm_nonneg z
    · nlinarith [hcs, hpy, h]
  nlinarith [hpy, hle, norm_nonneg (∑ i ∈ s, columnTensor b z i), norm_nonneg z]

/-- The columns of a Hilbert tensor are square-summable. -/
theorem summable_column_norm_sq {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) : Summable fun i => ‖toOperator z (b i)‖ ^ 2 :=
  summable_of_sum_le (fun _ => sq_nonneg _) (sum_column_norm_sq_le b z)

/-- The column tensors resolve the identity on `E tensor Conj F`. -/
theorem hasSum_columnTensor {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) :
    HasSum (columnTensor b z) z := by
  have hsummable : Summable (columnTensor b z) := by
    simpa only [← columnTensor_eq] using
      ((orthogonalFamily_columnEmbedding (E := E) b).summable_iff_norm_sq_summable
        (fun i => toOperator z (b i))).2 (summable_column_norm_sq b z)
  obtain ⟨w, hw⟩ := hsummable
  -- The limit is forced to be `z` because the two represented operators agree on
  -- the basis, hence everywhere.
  have hkey : toOperator w = toOperator z := by
    ext x
    have hcol : ∀ i : ι,
        (rightTensor x).adjoint (columnTensor b z i)
          = ⟪b i, x⟫_ℂ • toOperator z (b i) := by
      intro i
      rw [columnTensor, ← toOperator_apply, toOperator_tmul,
        InnerProductSpace.rankOne_apply]
    -- The limit of the mapped net is `(rightTensor x).adjoint w`, which is the
    -- unfolded form of `toOperator w x`; naming it keeps `simp` from rewriting
    -- the summands and the limit with the same rule in different directions.
    have hval : (rightTensor x).adjoint w = toOperator w x := rfl
    have h1 : HasSum (fun i => ⟪b i, x⟫_ℂ • toOperator z (b i))
        (toOperator w x) := by
      simpa only [hcol, hval] using hw.mapL ((rightTensor x).adjoint)
    have h2 : HasSum (fun i => ⟪b i, x⟫_ℂ • toOperator z (b i))
        (toOperator z x) := by
      simpa only [map_smul, b.repr_apply_apply] using
        (b.hasSum_repr x).mapL (toOperator z)
    exact h1.unique h2
  rwa [toOperator_injective hkey] at hw

/-- Parseval for the column decomposition of a tensor. -/
theorem norm_sq_eq_tsum_column_norm_sq {ι : Type*}
    (b : HilbertBasis ι ℂ F) (z : Space E F) :
    ‖z‖ ^ 2 = ∑' i, ‖toOperator z (b i)‖ ^ 2 := by
  have hlim := ((continuous_norm.pow 2).tendsto z).comp (hasSum_columnTensor b z)
  have h : HasSum (fun i => ‖toOperator z (b i)‖ ^ 2) (‖z‖ ^ 2) :=
    hlim.congr fun s => norm_sum_columnTensor_sq b z s
  exact h.tsum_eq.symm

/-- A basis-square-summable operator determines a tensor by its column series. -/
noncomputable def ofOperator {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) : Space E F :=
  ∑' i, A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i)

private theorem summable_columnSeries {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    Summable fun i => A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i) :=
  ((orthogonalFamily_columnEmbedding (E := E) b).summable_iff_norm_sq_summable
    (fun i => A (b i))).2 hA

/-- The column-series tensor represents the original operator. -/
theorem toOperator_ofOperator {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    toOperator (ofOperator b A hA) = A := by
  have hseries := summable_columnSeries b A hA
  ext x
  have hcol : ∀ i : ι,
      (rightTensor x).adjoint (A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i))
        = ⟪b i, x⟫_ℂ • A (b i) := by
    intro i
    rw [← toOperator_apply, toOperator_tmul, InnerProductSpace.rankOne_apply]
  have hval : (rightTensor x).adjoint (∑' i, A (b i) ⊗̂ₜ[ℂ] Conj.toConj (b i))
      = toOperator (ofOperator b A hA) x := rfl
  have h1 : HasSum (fun i => ⟪b i, x⟫_ℂ • A (b i))
      (toOperator (ofOperator b A hA) x) := by
    simpa only [hcol, hval] using hseries.hasSum.mapL ((rightTensor x).adjoint)
  have h2 : HasSum (fun i => ⟪b i, x⟫_ℂ • A (b i)) (A x) := by
    simpa only [map_smul, b.repr_apply_apply] using A.hasSum (b.hasSum_repr x)
  exact h1.unique h2

/-- The tensor reconstructed from the columns of a represented operator is the
original tensor. -/
theorem ofOperator_toOperator {ι : Type*} (b : HilbertBasis ι ℂ F)
    (z : Space E F) :
    ofOperator b (toOperator z) (summable_column_norm_sq b z) = z := by
  apply toOperator_injective
  rw [toOperator_ofOperator]

/-- The Hilbert tensor norm is exactly the basis Hilbert--Schmidt norm. -/
theorem norm_ofOperator_sq {ι : Type*} (b : HilbertBasis ι ℂ F)
    (A : F →L[ℂ] E) (hA : Summable fun i => ‖A (b i)‖ ^ 2) :
    ‖ofOperator b A hA‖ ^ 2 = ∑' i, ‖A (b i)‖ ^ 2 := by
  rw [norm_sq_eq_tsum_column_norm_sq b, toOperator_ofOperator]

/-- Basis-square-summability is equivalent to representability by a unique
Hilbert tensor. -/
theorem existsUnique_tensor_iff_summable_columns {ι : Type*}
    (b : HilbertBasis ι ℂ F) (A : F →L[ℂ] E) :
    (∃! z : Space E F, toOperator z = A) ↔
      Summable (fun i => ‖A (b i)‖ ^ 2) := by
  constructor
  · rintro ⟨z, rfl, _⟩
    exact summable_column_norm_sq b z
  · intro hA
    refine ⟨ofOperator b A hA, toOperator_ofOperator b A hA, ?_⟩
    intro z hz
    exact toOperator_injective (hz.trans (toOperator_ofOperator b A hA).symm)

end

end HilbertSchmidtTensor
end Spectra
