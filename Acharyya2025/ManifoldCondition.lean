/-
Proposition 1 of Acharyya et al. (2025): the compact-Riemannian-manifold sufficient condition.

The proposition asserts that Assumptions 1 and 2 hold as soon as every generative model is
associated with a vector on a `d`-dimensional compact Riemannian manifold in an ambient `R^q`,
whose pairwise geodesic distances are the population dissimilarities.

That hypothesis constrains the ambient space and says nothing about how the models are placed
inside it, and the conclusion is a statement about the placement: Assumption 1 asks the
population matrix to have rank `d`, and Assumption 2 asks its `d`-th eigenvalue to stay above a
positive constant.  A degenerate selection satisfies the hypothesis and violates both.

This file records that, with the degenerate selection made explicit and machine-checked.  The
source states Proposition 1 without proof.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
import Acharyya2024.Common
import Acharyya2025.Deterministic
import Acharyya2025.MathlibBridge
import ForTauCeti.Analysis.Matrix.SpectralFunctionMeasurable
import ForTauCeti.Analysis.Matrix.Spectrum
import Acharyya2025.GramRealization

open scoped BigOperators Matrix
open Acharyya2024 Acharyya2025.Deterministic Acharyya2025.MathlibBridge

namespace Acharyya2025.ManifoldCondition

/-- A constant model selection has vanishing population dissimilarities, hence a vanishing
doubly centred population matrix. -/
theorem classicalMDSMatrix_const_eq_zero {n q : Nat} (p : Rvec q) :
    classicalMDSMatrix (fun _ _ : Fin n => ‖p - p‖) = fun _ _ => 0 := by
  funext i j
  simp only [sub_self, norm_zero]
  simp [classicalMDSMatrix, doubleCenter, rowMean, colMean, grandMean]

/-- The matrix form of the same fact. -/
theorem disMatToMatrix_classicalMDSMatrix_const_eq_zero {n q : Nat} (p : Rvec q) :
    disMatToMatrix (classicalMDSMatrix (fun _ _ : Fin n => ‖p - p‖)) = 0 := by
  funext i j
  rw [disMatToMatrix, classicalMDSMatrix_const_eq_zero]
  rfl

/-- A Hermitian matrix that vanishes has vanishing eigenvalues. -/
theorem eigenvalues₀_eq_zero_of_eq_zero {n : Nat} {B : Matrix (Fin n) (Fin n) Real}
    (hB : B.IsHermitian) (h0 : B = 0) (k : Fin (Fintype.card (Fin n))) :
    hB.eigenvalues₀ k = 0 := by
  have hbound : ∀ i j, |B i j| ≤ (0 : Real) := by simp [h0]
  have h := TauCeti.Matrix.abs_eigenvalues₀_le_of_entry_le hB hbound k
  rw [mul_zero] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/--
**Every eigenvalue of the population matrix of a constant selection is zero.**

Associate every model with one and the same point `p`.  The pairwise population dissimilarities
are then all zero.  They are also, literally, the pairwise geodesic distances of any compact
geodesically convex set containing `p` -- a closed ball of the ambient `R^q`, for instance --
so the hypothesis of Proposition 1 is met.  The doubly centred population matrix nevertheless
vanishes identically.
-/
theorem eigenvalues₀_classicalMDSMatrix_const_eq_zero {n q : Nat} (p : Rvec q)
    (hB : (disMatToMatrix (classicalMDSMatrix (fun _ _ : Fin n => ‖p - p‖))).IsHermitian)
    (k : Fin (Fintype.card (Fin n))) :
    hB.eigenvalues₀ k = 0 :=
  eigenvalues₀_eq_zero_of_eq_zero hB (disMatToMatrix_classicalMDSMatrix_const_eq_zero p) k

/--
**Assumption 2 fails for the constant selection**: no positive constant bounds the eigenvalues
of its population matrix from below, at any stage.
-/
theorem no_eigenvalue_floor_for_const_selection {q : Nat} (p : Rvec q) :
    ¬ ∃ C₁ : Real, 0 < C₁ ∧ ∀ (n : Nat)
      (hB : (disMatToMatrix (classicalMDSMatrix (fun _ _ : Fin n => ‖p - p‖))).IsHermitian)
      (k : Fin (Fintype.card (Fin n))), C₁ ≤ hB.eigenvalues₀ k := by
  rintro ⟨C₁, hC₁, h⟩
  have hzero := disMatToMatrix_classicalMDSMatrix_const_eq_zero (n := 1) p
  have hB : (disMatToMatrix (classicalMDSMatrix (fun _ _ : Fin 1 => ‖p - p‖))).IsHermitian := by
    rw [hzero]; exact Matrix.isHermitian_zero
  have hk : Fin (Fintype.card (Fin 1)) := ⟨0, by simp⟩
  have := h 1 hB hk
  rw [eigenvalues₀_classicalMDSMatrix_const_eq_zero p hB hk] at this
  linarith

/--
**Assumption 1 fails for the constant selection**: the population matrix has rank `0`, not `d`,
for any positive embedding dimension `d`.
-/
theorem rank_classicalMDSMatrix_const_eq_zero {n q : Nat} (p : Rvec q) :
    (disMatToMatrix (classicalMDSMatrix (fun _ _ : Fin n => ‖p - p‖))).rank = 0 := by
  rw [disMatToMatrix_classicalMDSMatrix_const_eq_zero]
  exact Matrix.rank_zero

/-! ## The repair: a spread condition on the placement

Proposition 1's hypothesis constrains the ambient space and says nothing about how the models
are placed inside it, which is what the counterexample above exploits.  The repair is to add
the missing placement hypothesis, and the honest form of it is geometric: the latent points,
recentred at their centroid, must have variance bounded below in *every* direction.  A constant
selection has variance zero in every direction, so the repair excludes exactly the
configurations that refute the printed proposition.

The first step is the classical-MDS identity itself, which the tree did not have: for a
Euclidean placement, the doubly centred matrix of the pairwise distances is the Gram matrix of
the recentred configuration.  Everything else follows from it. -/

/-- The centroid of a finite configuration. -/
noncomputable def centroid {n d : Nat} (ψ : Config n d) : Rvec d :=
  ((n : Real)⁻¹) • ∑ i : Fin n, ψ i

/-- The configuration recentred at its centroid: the paper's `H ψ`. -/
noncomputable def centeredConfig {n d : Nat} (ψ : Config n d) (i : Fin n) : Rvec d :=
  ψ i - centroid ψ

/-- The inner product of a configuration point with the centroid is the row mean of the
Gram matrix. -/
theorem inner_centroid_right {n d : Nat} (ψ : Config n d) (i : Fin n) :
    inner ℝ (ψ i) (centroid ψ) = ((n : Real)⁻¹) * ∑ k : Fin n, inner ℝ (ψ i) (ψ k) := by
  rw [centroid, inner_smul_right, inner_sum]

/-- The inner product of the centroid with a configuration point is the column mean of the
Gram matrix. -/
theorem inner_centroid_left {n d : Nat} (ψ : Config n d) (j : Fin n) :
    inner ℝ (centroid ψ) (ψ j) = ((n : Real)⁻¹) * ∑ k : Fin n, inner ℝ (ψ k) (ψ j) := by
  rw [centroid, real_inner_smul_left, sum_inner]

/-- The squared norm of the centroid is the grand mean of the Gram matrix. -/
theorem inner_centroid_self {n d : Nat} (ψ : Config n d) :
    inner ℝ (centroid ψ) (centroid ψ)
      = ((n : Real)⁻¹) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, inner ℝ (ψ a) (ψ b) := by
  rw [centroid, real_inner_smul_left, real_inner_smul_right, sum_inner]
  simp only [inner_sum]
  ring

/-- **The classical-MDS identity.**  For a Euclidean placement `ψ`, the doubly centred matrix
of the pairwise distances is the Gram matrix of the configuration recentred at its centroid:
`-½ H ∆∘² H = (Hψ)(Hψ)ᵀ`.

This is the fact classical multidimensional scaling rests on, and the repair below is its
consequence: the population matrix of a Euclidean placement *is* a Gram matrix, so its rank and
its eigenvalue floor are properties of the placement -- exactly what the printed Proposition 1
declines to constrain. -/
theorem classicalMDSMatrix_dist_eq_inner_centered {n d : Nat} (ψ : Config n d) (i j : Fin n) :
    classicalMDSMatrix (fun a b => ‖ψ a - ψ b‖) i j
      = inner ℝ (centeredConfig ψ i) (centeredConfig ψ j) := by
  have hn : (0 : Nat) < n := i.pos
  have hnR : ((n : Real)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set S : Fin n → Fin n → Real := fun a b => inner ℝ (ψ a) (ψ b) with hS
  have hsq : ∀ a b : Fin n, ‖ψ a - ψ b‖ ^ 2 = S a a - 2 * S a b + S b b := by
    intro a b
    rw [← real_inner_self_eq_norm_sq]
    simp only [hS, inner_sub_left, inner_sub_right]
    rw [real_inner_comm (ψ b) (ψ a)]
    ring
  -- the three centred means of the squared-distance matrix
  have hrow : ∀ a : Fin n, (∑ b : Fin n, ‖ψ a - ψ b‖ ^ 2)
      = (n : Real) * S a a - 2 * (∑ b : Fin n, S a b) + ∑ b : Fin n, S b b := by
    intro a
    simp only [hsq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum]
    simp
  have hcol : ∀ b : Fin n, (∑ a : Fin n, ‖ψ a - ψ b‖ ^ 2)
      = (∑ a : Fin n, S a a) - 2 * (∑ a : Fin n, S a b) + (n : Real) * S b b := by
    intro b
    simp only [hsq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum]
    simp
  have hgrand : (∑ a : Fin n, ∑ b : Fin n, ‖ψ a - ψ b‖ ^ 2)
      = 2 * (n : Real) * (∑ a : Fin n, S a a) - 2 * ∑ a : Fin n, ∑ b : Fin n, S a b := by
    have : ∀ a : Fin n, (∑ b : Fin n, ‖ψ a - ψ b‖ ^ 2)
        = (n : Real) * S a a - 2 * (∑ b : Fin n, S a b) + ∑ b : Fin n, S b b := hrow
    simp only [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_const]
    simp [Finset.card_univ]
    ring
  simp only [classicalMDSMatrix, doubleCenter, rowMean, colMean, grandMean]
  rw [hsq i j, hrow i, hcol j, hgrand]
  rw [centeredConfig, centeredConfig, inner_sub_left, inner_sub_right, inner_sub_right,
    inner_centroid_right ψ i, inner_centroid_left ψ j, inner_centroid_self ψ]
  simp only [hS]
  field_simp
  ring

/-- The Gram identity in the entrywise-sum form the realization API consumes. -/
theorem sum_centered_eq_classicalMDSMatrix_dist {n d : Nat} (ψ : Config n d) (i j : Fin n) :
    (∑ k : Fin d, centeredConfig ψ i k * centeredConfig ψ j k)
      = disMatToMatrix (classicalMDSMatrix (fun a b => ‖ψ a - ψ b‖)) i j := by
  rw [disMatToMatrix, classicalMDSMatrix_dist_eq_inner_centered ψ i j]
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- **The population matrix of a Euclidean placement is positive semidefinite of rank at most
the ambient dimension.**

This is the half of Assumption 1 that follows from the placement being `d`-dimensional at all,
with no spread hypothesis: it is a *Gram* matrix, by the classical-MDS identity. -/
theorem posSemidef_and_rank_le_classicalMDSMatrix_dist {n d : Nat} (ψ : Config n d) :
    (disMatToMatrix (classicalMDSMatrix (fun a b => ‖ψ a - ψ b‖))).PosSemidef ∧
      (disMatToMatrix (classicalMDSMatrix (fun a b => ‖ψ a - ψ b‖))).rank ≤ d :=
  Acharyya2025.GramRealization.posSemidef_and_rank_le_of_config_gram_eq _ (centeredConfig ψ)
    (sum_centered_eq_classicalMDSMatrix_dist ψ)

/-- **Assumption 1 for a Euclidean placement**, in the encoded form the perturbation theory
consumes: the sorted eigenvalues of the population matrix vanish from index `d` on.

The hypothesis is that the models are placed in a `d`-dimensional Euclidean space and the
population dissimilarities are their distances.  No spread condition is needed for this half --
the rank bound is a consequence of the placement being `d`-dimensional, and the counterexample
above satisfies it too, with every eigenvalue zero. -/
theorem eigenvalues₀_classicalMDSMatrix_dist_eq_zero_of_le {n d : Nat} (ψ : Config n d)
    {i : Fin (Fintype.card (Fin n))} (hi : d ≤ (i : Nat)) :
    (posSemidef_and_rank_le_classicalMDSMatrix_dist ψ).1.isHermitian.eigenvalues₀ i = 0 :=
  TauCeti.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le
    (posSemidef_and_rank_le_classicalMDSMatrix_dist ψ).1
    (posSemidef_and_rank_le_classicalMDSMatrix_dist ψ).2 hi

/-- The quadratic form of the population matrix of a Euclidean placement is the squared norm
of the corresponding combination of recentred points. -/
theorem dotProduct_mulVec_classicalMDSMatrix_dist {n d : Nat} (ψ : Config n d)
    (v : Fin n → Real) :
    v ⬝ᵥ (disMatToMatrix (classicalMDSMatrix (fun a b => ‖ψ a - ψ b‖)) *ᵥ v)
      = ‖∑ i : Fin n, v i • centeredConfig ψ i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [dotProduct, Matrix.mulVec, disMatToMatrix,
    classicalMDSMatrix_dist_eq_inner_centered ψ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-! ### The spread condition

The printed Proposition 1 constrains the ambient space.  What it does not constrain, and what
its conclusion is about, is the *placement*: `SpreadPlacement ψ α` below is the missing
hypothesis in its most elementary sufficient form.  It asks that among the `n` models there be
`d` whose recentred positions are mutually orthogonal, each at squared distance at least `α`
from the centroid.

It is a sufficient condition, not a necessary one -- any placement whose recentred
configuration has `d`-th singular value at least `√α` would do -- and it is stated this way
because it is checkable, because it is elementary enough to be verified against a picture, and
because it fails for exactly the reason the counterexample above works: a constant selection
has every recentred position at distance `0`. -/

/-- **A spread placement**: `d` of the models have mutually orthogonal recentred positions,
each at squared distance at least `α` from the centroid. -/
def SpreadPlacement {n d : Nat} (ψ : Config n d) (α : Real) : Prop :=
  ∃ idx : Fin d → Fin n, Function.Injective idx ∧
    (∀ k l : Fin d, k ≠ l →
      inner ℝ (centeredConfig ψ (idx k)) (centeredConfig ψ (idx l)) = 0) ∧
    (∀ k : Fin d, α ≤ ‖centeredConfig ψ (idx k)‖ ^ 2)

/-- **Assumption 2, upper half, for a Euclidean placement.**

The quadratic form of the population matrix is bounded by the total recentred energy
`∑ᵢ ‖ψᵢ − ψ̄‖²`, which is the placement's diameter-type constant.  This is Cauchy--Schwarz and
needs no spread hypothesis. -/
theorem dotProduct_mulVec_classicalMDSMatrix_dist_le {n d : Nat} (ψ : Config n d)
    (v : Fin n → Real) :
    v ⬝ᵥ (disMatToMatrix (classicalMDSMatrix (fun a b => ‖ψ a - ψ b‖)) *ᵥ v)
      ≤ (∑ i : Fin n, ‖centeredConfig ψ i‖ ^ 2) * ∑ i : Fin n, v i ^ 2 := by
  rw [dotProduct_mulVec_classicalMDSMatrix_dist ψ v]
  have htri : ‖∑ i : Fin n, v i • centeredConfig ψ i‖
      ≤ ∑ i : Fin n, |v i| * ‖centeredConfig ψ i‖ := by
    refine (norm_sum_le _ _).trans_eq ?_
    exact Finset.sum_congr rfl fun i _ => by rw [norm_smul, Real.norm_eq_abs]
  have hcs : (∑ i : Fin n, |v i| * ‖centeredConfig ψ i‖) ^ 2
      ≤ (∑ i : Fin n, v i ^ 2) * ∑ i : Fin n, ‖centeredConfig ψ i‖ ^ 2 := by
    calc (∑ i : Fin n, |v i| * ‖centeredConfig ψ i‖) ^ 2
        ≤ (∑ i : Fin n, |v i| ^ 2) * ∑ i : Fin n, ‖centeredConfig ψ i‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ i : Fin n, v i ^ 2) * ∑ i : Fin n, ‖centeredConfig ψ i‖ ^ 2 := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => sq_abs (v i)
  calc ‖∑ i : Fin n, v i • centeredConfig ψ i‖ ^ 2
      ≤ (∑ i : Fin n, |v i| * ‖centeredConfig ψ i‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ (∑ i : Fin n, v i ^ 2) * ∑ i : Fin n, ‖centeredConfig ψ i‖ ^ 2 := hcs
    _ = (∑ i : Fin n, ‖centeredConfig ψ i‖ ^ 2) * ∑ i : Fin n, v i ^ 2 := by ring

/-- Pythagoras for a finite pairwise-orthogonal family. -/
private theorem norm_sq_sum_of_pairwise_orthogonal {ι : Type*} {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace Real F]
    (t : Finset ι) (y : ι → F)
    (h : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → inner ℝ (y i) (y j) = 0) :
    ‖∑ i ∈ t, y i‖ ^ 2 = ∑ i ∈ t, ‖y i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq (y i)
  · exact fun j hj hne => h i hi j hj (Ne.symm hne)
  · exact fun hni => absurd hi hni

/-- **Assumption 2, lower half, from the spread condition.**

Under `SpreadPlacement ψ α` the first `d` sorted eigenvalues of the population matrix are at
least `α`.  This is the clause the printed Proposition 1 cannot supply: the counterexample above
is a Euclidean placement in every ambient sense the proposition asks for, and its population
matrix is zero.

The proof is Courant--Fischer applied to the coordinate subspace cut out by the `k + 1` spread
indices, on which the quadratic form is bounded below by `α` by orthogonality. -/
theorem le_eigenvalues₀_classicalMDSMatrix_dist_of_spread {n d : Nat} (ψ : Config n d)
    {α : Real} (hspread : SpreadPlacement ψ α)
    {k : Fin (Fintype.card (Fin n))} (hk : (k : Nat) < d) :
    α ≤ (posSemidef_and_rank_le_classicalMDSMatrix_dist ψ).1.isHermitian.eigenvalues₀ k := by
  classical
  obtain ⟨idx, hinj, horth, hnorm⟩ := hspread
  set hpsd := (posSemidef_and_rank_le_classicalMDSMatrix_dist ψ).1 with hpsd_def
  set s : Finset (Fin n) := (Finset.Iic (⟨(k : Nat), hk⟩ : Fin d)).image idx with hs
  have hcard : s.card = (k : Nat) + 1 := by
    rw [hs, Finset.card_image_of_injective _ hinj, Fin.card_Iic]
  set b : OrthonormalBasis (Fin n) Real (EuclideanSpace Real (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) Real with hb
  have hVdim : Module.finrank Real (b.spanIndices (↑s : Set (Fin n)))
      = ((Fin.cast (Fintype.card_fin n) k : Fin n) : Nat) + 1 := by
    rw [b.finrank_spanIndices, hcard]
    rfl
  obtain ⟨x, hxV, hx1, hxle⟩ :=
    (TauCeti.Matrix.opSym hpsd.isHermitian).exists_unit_vector_re_inner_le_eigenvalue
      finrank_euclideanSpace_fin (Fin.cast (Fintype.card_fin n) k) _ hVdim
  refine le_trans ?_ (hxle.trans_eq ?_)
  · -- the quadratic form is at least `α` on the spread coordinate subspace
    have hzero : ∀ i, i ∉ s → WithLp.ofLp x i = 0 := by
      intro i hi
      have := b.repr_eq_zero_of_mem_spanIndices hxV (s := (↑s : Set (Fin n)))
        (by simpa using hi)
      simpa [hb] using this
    have hform : RCLike.re (inner ℝ ((Matrix.toEuclideanLin
        (disMatToMatrix (classicalMDSMatrix (fun a b => ‖ψ a - ψ b‖)))) x) x)
        = ‖∑ i : Fin n, (WithLp.ofLp x) i • centeredConfig ψ i‖ ^ 2 := by
      rw [← dotProduct_mulVec_classicalMDSMatrix_dist ψ (WithLp.ofLp x),
        EuclideanSpace.inner_eq_star_dotProduct]
      simp
    rw [hform]
    -- restrict the sum to the spread indices, then use orthogonality
    have hsum : (∑ i : Fin n, (WithLp.ofLp x) i • centeredConfig ψ i)
        = ∑ i ∈ s, (WithLp.ofLp x) i • centeredConfig ψ i := by
      refine (Finset.sum_subset (Finset.subset_univ s) ?_).symm
      intro i _ hi
      rw [hzero i hi, zero_smul]
    rw [hsum, norm_sq_sum_of_pairwise_orthogonal s _ ?_]
    · have hlb : ∀ i ∈ s, α * (WithLp.ofLp x i) ^ 2
          ≤ ‖(WithLp.ofLp x) i • centeredConfig ψ i‖ ^ 2 := by
        intro i hi
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        exact (mul_le_mul_of_nonneg_right (hnorm j) (sq_nonneg _)).trans_eq (by ring)
      calc α = α * ∑ i ∈ s, (WithLp.ofLp x i) ^ 2 := by
              rw [show (∑ i ∈ s, (WithLp.ofLp x i) ^ 2) = 1 from ?_, mul_one]
              have hxs : ∑ i : Fin n, (WithLp.ofLp x i) ^ 2 = 1 := by
                have := congrArg (· ^ 2) hx1
                simp only [EuclideanSpace.norm_eq, one_pow] at this
                rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at this
                simpa [Real.norm_eq_abs, sq_abs] using this
              rw [← hxs]
              refine Finset.sum_subset (Finset.subset_univ s) ?_
              intro i _ hi
              rw [hzero i hi]; ring
        _ = ∑ i ∈ s, α * (WithLp.ofLp x i) ^ 2 := by rw [Finset.mul_sum]
        _ ≤ ∑ i ∈ s, ‖(WithLp.ofLp x) i • centeredConfig ψ i‖ ^ 2 :=
              Finset.sum_le_sum hlb
    · intro i hi j hj hne
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hj
      rw [real_inner_smul_left, real_inner_smul_right,
        horth a c (fun e => hne (by rw [e])), mul_zero, mul_zero]
  · rw [TauCeti.Matrix.eigenvalues_toEuclideanLin_eq_eigenvalues₀ hpsd.isHermitian]
    congr 1

/-- **Assumption 2, upper half, in eigenvalue form.**

Every sorted eigenvalue of the population matrix is at most the placement's total recentred
energy.  No spread hypothesis is needed. -/
theorem eigenvalues₀_classicalMDSMatrix_dist_le {n d : Nat} (ψ : Config n d)
    (k : Fin (Fintype.card (Fin n))) :
    (posSemidef_and_rank_le_classicalMDSMatrix_dist ψ).1.isHermitian.eigenvalues₀ k
      ≤ ∑ i : Fin n, ‖centeredConfig ψ i‖ ^ 2 := by
  classical
  set hpsd := (posSemidef_and_rank_le_classicalMDSMatrix_dist ψ).1 with hpsd_def
  obtain ⟨V, hVdim, hVlow⟩ :=
    (TauCeti.Matrix.opSym hpsd.isHermitian).exists_submodule_forall_unit_eigenvalue_le_re_inner
      finrank_euclideanSpace_fin (Fin.cast (Fintype.card_fin n) k)
  have hVpos : 0 < Module.finrank Real V := by rw [hVdim]; omega
  obtain ⟨y₀, hy₀⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hVpos
  have hyV : (y₀ : EuclideanSpace Real (Fin n)) ∈ V := y₀.2
  have hy0 : (y₀ : EuclideanSpace Real (Fin n)) ≠ 0 := by
    simpa using (Submodule.coe_eq_zero (p := V)).not.mpr hy₀
  set y : EuclideanSpace Real (Fin n) := (y₀ : EuclideanSpace Real (Fin n)) with hy
  set x : EuclideanSpace Real (Fin n) := ‖y‖⁻¹ • y with hx
  have hx1 : ‖x‖ = 1 := by
    rw [hx, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]
  have hxV : x ∈ V := V.smul_mem _ hyV
  have hlow := hVlow x hxV hx1
  rw [TauCeti.Matrix.eigenvalues_toEuclideanLin_eq_eigenvalues₀ hpsd.isHermitian] at hlow
  have hform : RCLike.re (inner ℝ ((Matrix.toEuclideanLin
      (disMatToMatrix (classicalMDSMatrix (fun a b => ‖ψ a - ψ b‖)))) x) x)
      = (WithLp.ofLp x) ⬝ᵥ (disMatToMatrix (classicalMDSMatrix (fun a b => ‖ψ a - ψ b‖))
          *ᵥ WithLp.ofLp x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]; simp
  rw [hform] at hlow
  have hxs : ∑ i : Fin n, (WithLp.ofLp x i) ^ 2 = 1 := by
    have := congrArg (· ^ 2) hx1
    simp only [EuclideanSpace.norm_eq, one_pow] at this
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at this
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hup := dotProduct_mulVec_classicalMDSMatrix_dist_le ψ (WithLp.ofLp x)
  rw [hxs, mul_one] at hup
  have hcast : (Fin.cast (Fintype.card_fin n).symm (Fin.cast (Fintype.card_fin n) k)) = k :=
    Fin.ext rfl
  rw [hcast] at hlow
  exact hlow.trans hup

/-- **The repair of Proposition 1.**

This is *not* the printed proposition, which is refuted above: it replaces the printed
ambient-manifold condition by an explicit spread condition on the *placement*, and derives from
it exactly the two assumptions the downstream perturbation theory consumes.

* Assumption 1 (`rank`): the sorted eigenvalues of the population matrix vanish from index `d`.
* Assumption 2 (`floor`, `ceil`): the leading `d` eigenvalues lie in `[α, Λ]`, with
  `Λ = ∑ᵢ ‖ψᵢ − ψ̄‖²` the placement's recentred energy.

The printed proposition constrains the ambient space and concludes the same thing; the
counterexample `constantSelection_classicalMDSMatrix_eq_zero` shows that no constraint on the
ambient space alone can do so, because a constant placement satisfies every such constraint and
has population matrix `0`. -/
theorem proposition1_repair_of_spreadPlacement {n d : Nat} (ψ : Config n d) {α : Real}
    (hspread : SpreadPlacement ψ α) :
    (∀ i : Fin (Fintype.card (Fin n)), d ≤ (i : Nat) →
        (posSemidef_and_rank_le_classicalMDSMatrix_dist ψ).1.isHermitian.eigenvalues₀ i = 0) ∧
      (∀ i : Fin (Fintype.card (Fin n)), (i : Nat) < d →
        α ≤ (posSemidef_and_rank_le_classicalMDSMatrix_dist ψ).1.isHermitian.eigenvalues₀ i) ∧
      (∀ i : Fin (Fintype.card (Fin n)),
        (posSemidef_and_rank_le_classicalMDSMatrix_dist ψ).1.isHermitian.eigenvalues₀ i
          ≤ ∑ j : Fin n, ‖centeredConfig ψ j‖ ^ 2) :=
  ⟨fun _ hi => eigenvalues₀_classicalMDSMatrix_dist_eq_zero_of_le ψ hi,
    fun _ hi => le_eigenvalues₀_classicalMDSMatrix_dist_of_spread ψ hspread hi,
    eigenvalues₀_classicalMDSMatrix_dist_le ψ⟩

end Acharyya2025.ManifoldCondition
