/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import ForTauCeti.Analysis.Normed.FiniteLpGauge
import ForTauCeti.Analysis.OperatorIdeal.Family.KyFan
import ForTauCeti.Analysis.OperatorIdeal.Family.TraceClass
import ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidtEnergy
import ForTauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
import ForTauCeti.Topology.ENNRealLiminf
import ForTauCeti.Analysis.InnerProductSpace.SingularSystem
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional

/-!
# The Schatten-`p` operator ideals

The **Schatten `p`-norm** of a bounded operator is the `ℓᵖ` norm of its approximation-number
sequence,

```
T.schattenENorm p = (∑' n, ‖aₙ(T)‖ₑ ^ p) ^ p⁻¹,
```

valued in `ℝ≥0∞` and therefore defined for every bounded operator, being `∞` exactly off the
ideal.  At `p = 1` it is the nuclear norm and at `p = 2` the Hilbert--Schmidt norm; those two
have their own modules, and this one is the family in between.

## Why the triangle inequality is the whole file

Every other ideal law is a pointwise statement about approximation numbers and transports
term by term.  Subadditivity is not: `aₙ(S + T) ≤ aₙ(S) + aₙ(T)` is **false** in general, and
what is true is the weaker *prefix* statement, the Ky Fan inequality
`∑_{n<k} aₙ(S+T) ≤ ∑_{n<k} aₙ(S) + ∑_{n<k} aₙ(T)`.  Getting from prefix sums to `ℓᵖ` norms is
exactly weak majorization.

`ForTauCeti/Analysis/Convex/Majorization.lean` has that theory, but for `Fin n`, and there is
no sequence version anywhere in the library.  **None is needed.**  The `Fin k` theory is
applied to the truncation at each `k`, which bounds every partial sum of the left side by the
*whole* right side; the supremum over `k` is then the left side's own `tsum`.  The finite
layer is the tool here, not the obstacle.

## Main definitions and results

* `ContinuousLinearMap.schattenENorm`: the Schatten `p`-norm, valued in `ℝ≥0∞`;
* `ContinuousLinearMap.schattenENorm_add_le`: the triangle inequality;
* `ContinuousLinearMap.schattenENorm_smul`, `_adjoint`, `_comp_le`: the remaining ideal laws;
* `ContinuousLinearMap.IsSchattenClass`: the membership predicate;
* `TauCeti.schattenIdealFamily`: the resulting symmetric operator ideal family;
* `ContinuousLinearMap.schattenENorm_one` and
  `TauCeti.schattenIdealFamily_one_eq_traceClassIdealFamily`: at `p = 1` this *is* the
  trace-class ideal.  The `p = 2` counterpart is deliberately absent — see below.

## The `p = 2` bridge

`hilbertSchmidtENorm` is built from the Hilbert--Schmidt energy through a Hilbert basis and
never mentions approximation numbers, so unlike its `p = 1` twin the agreement with the
Schatten gauge is a theorem rather than arithmetic.  It is proved here, as
`tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy_of_hilbertBasis`.

**Neither of the two routes one expects is the one taken.**  Not the singular-value
decomposition of a compact operator: Mathlib's eigenvector basis is finite-dimensional only,
and pinned Mathlib has no orthonormal eigenbasis for a compact self-adjoint operator.  Not an
`ε`-argument either.  Instead both inequalities go through the *same* finite truncations of
the basis — forward by reading the finite case exactly, reverse by Fatou along
`Finset.atTop`.

What is *not* here is the resulting equality of families,
`schattenIdealFamily 𝕜 2 = hilbertSchmidtIdealFamily 𝕜`: the gauges are `hilbertSchmidtENorm`
and `schattenENorm 2`, which are the square roots of the two sides above, so it is a matter of
transporting the identity through `^ (2 : ℝ)⁻¹` and the two families' definitions.  Completeness
of the family is likewise open, as it is for the trace-class family.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: none.
-/

open scoped ENNReal NNReal InnerProductSpace

public section

namespace ContinuousLinearMap

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
-- Both spaces share a universe because `HasMinMaxLowerBoundEverywhere` quantifies over one:
-- an ideal family fixes a single universe for every pair it acts on.
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

section Truncation

/-- The prefix sums of a truncated sequence are the sequence's own partial sums, capped at the
truncation length.  This is the only bridge the file needs between
`TauCeti.FiniteVector.prefixSum` on `Fin k` and `Finset.range`. -/
theorem _root_.TauCeti.FiniteVector.prefixSum_comp_val {k : ℕ} (f : ℕ → ℝ) (j : ℕ) :
    TauCeti.FiniteVector.prefixSum j (fun i : Fin k => f i) =
      ∑ n ∈ Finset.range (min j k), f n := by
  classical
  rw [TauCeti.FiniteVector.prefixSum, Finset.sum_filter, Fin.sum_univ_eq_sum_range
    (fun m => if m < j then f m else 0) k, ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_min]
  exact and_comm

end Truncation

section Finite

variable [HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]

/-- **The Schatten triangle inequality on a truncation.**  Every partial `ℓᵖ` sum of the
approximation numbers of `S + T` is bounded by the *full* partial sums of `S` and of `T` at
the same length.

The proof is the whole point of the module: the truncated sequences are weakly majorized —
antitone and nonnegative because approximation numbers are, and prefix-comparable because
that comparison *is* `kyFanGauge_add_le` — so `TauCeti.FiniteVector.lpGauge_mono_weaklyMajorized`
applies, and finite Minkowski splits the right-hand side. -/
theorem lpGauge_approximationNumber_add_le {p : ℝ} (hp : 1 ≤ p) (S T : E →L[𝕜] F) (k : ℕ) :
    TauCeti.FiniteVector.lpGauge p (fun i : Fin k => (S + T).approximationNumber i) ≤
      TauCeti.FiniteVector.lpGauge p (fun i : Fin k => S.approximationNumber i) +
        TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i) := by
  classical
  have hmaj : TauCeti.FiniteVector.WeaklyMajorized
      (fun i : Fin k => (S + T).approximationNumber i)
      (fun i : Fin k => S.approximationNumber i + T.approximationNumber i) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact fun i j hij => (S + T).approximationNumber_antitone (by exact_mod_cast hij)
    · exact fun i j hij =>
        add_le_add (S.approximationNumber_antitone (by exact_mod_cast hij))
          (T.approximationNumber_antitone (by exact_mod_cast hij))
    · exact fun i => (S + T).approximationNumber_nonneg i
    · exact fun i =>
        add_nonneg (S.approximationNumber_nonneg i) (T.approximationNumber_nonneg i)
    · intro j
      rw [TauCeti.FiniteVector.prefixSum_comp_val (fun n => (S + T).approximationNumber n) j,
        show (fun i : Fin k => S.approximationNumber i + T.approximationNumber i)
          = (fun i : Fin k => (fun n => S.approximationNumber n + T.approximationNumber n) i)
          from rfl,
        TauCeti.FiniteVector.prefixSum_comp_val
          (fun n => S.approximationNumber n + T.approximationNumber n) j,
        Finset.sum_add_distrib]
      exact kyFanGauge_add_le_of_hasMinMaxLowerBound
        HasMinMaxLowerBoundEverywhere.out S T (min j k)
  calc TauCeti.FiniteVector.lpGauge p (fun i : Fin k => (S + T).approximationNumber i)
      ≤ TauCeti.FiniteVector.lpGauge p
          (fun i : Fin k => S.approximationNumber i + T.approximationNumber i) :=
        TauCeti.FiniteVector.lpGauge_mono_weaklyMajorized hp hmaj
    _ ≤ _ := TauCeti.FiniteVector.lpGauge_add_le hp _ _

end Finite

section Corestriction

variable {𝕜' : Type u} [RCLike 𝕜']
variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace 𝕜' H₀]

/-- **An operator of finite rank has the approximation numbers of its corestriction to its
own range.**

Both directions are one application of `approximationNumber_comp_le_mul_norm`: the
orthogonal projection onto the range and the inclusion of the range are both of norm at most
one, and composing with either recovers the other operator.  This is what lets the
finite-source identity — which needs a finite-dimensional *target* — be applied to an
operator whose target is an arbitrary Hilbert space. -/
theorem approximationNumber_orthogonalProjectionOnto_range_comp {G₀ : Type*}
    [NormedAddCommGroup G₀] [InnerProductSpace 𝕜' G₀] [FiniteDimensional 𝕜' G₀]
    (A : G₀ →L[𝕜'] H₀) (n : ℕ) :
    ((LinearMap.range (A : G₀ →ₗ[𝕜'] H₀)).orthogonalProjectionOnto ∘L A).approximationNumber n
      = A.approximationNumber n := by
  set W := LinearMap.range (A : G₀ →ₗ[𝕜'] H₀) with hW
  have hval : ∀ x, ((W.orthogonalProjectionOnto (A x) : W) : H₀) = A x := fun x =>
    congrArg Subtype.val
      (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨A x, ⟨x, rfl⟩⟩ : W))
  have hfactor : W.subtypeL ∘L (W.orthogonalProjectionOnto ∘L A) = A := by
    ext x
    exact hval x
  refine le_antisymm ?_ ?_
  · refine (approximationNumber_comp_le_norm_mul _ _ n).trans ?_
    exact mul_le_of_le_one_left (A.approximationNumber_nonneg n)
      (Submodule.orthogonalProjectionOnto_norm_le W)
  · conv_lhs => rw [← hfactor]
    refine (approximationNumber_comp_le_norm_mul _ _ n).trans ?_
    exact mul_le_of_le_one_left
      ((W.orthogonalProjectionOnto ∘L A).approximationNumber_nonneg n)
      W.norm_subtypeL_le



/-- **Approximation numbers of an operator out of a finite-dimensional space vanish beyond
that dimension**, because the operator is its own approximant of that rank.

The rank bound goes through `LinearMap.finrank_range_le` rather than
`LinearMap.rank_le_domain`: the latter fixes both spaces in one universe, and the consumer
here has a Euclidean source in the scalar field's universe and an arbitrary target. -/
theorem approximationNumber_eq_zero_of_finrank_le {G₀ : Type*} [NormedAddCommGroup G₀]
    [InnerProductSpace 𝕜' G₀] [FiniteDimensional 𝕜' G₀] (A : G₀ →L[𝕜'] H₀) {n : ℕ}
    (hn : Module.finrank 𝕜' G₀ ≤ n) : A.approximationNumber n = 0 := by
  refine le_antisymm ?_ (A.approximationNumber_nonneg n)
  have hrank : (A : G₀ →ₗ[𝕜'] H₀).rank ≤ (n : Cardinal) := by
    have h := LinearMap.finrank_range_le (A : G₀ →ₗ[𝕜'] H₀)
    rw [LinearMap.rank, ← Module.finrank_eq_rank]
    exact_mod_cast h.trans hn
  simpa using A.approximationNumber_le_norm_sub (R := A) hrank


end Corestriction

section FiniteSource

-- The source universe is left free rather than fixed to `v`: the consumer below applies this
-- at `EuclideanSpace 𝕜' (Fin n)`, which lives in the scalar field's universe.
variable {𝕜' : Type u} [RCLike 𝕜']
variable {G H : Type*}
  [NormedAddCommGroup G] [InnerProductSpace 𝕜' G] [CompleteSpace G] [FiniteDimensional 𝕜' G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜' H] [CompleteSpace H] [FiniteDimensional 𝕜' H]

/-- **The Hilbert--Schmidt energy is the sum of squared approximation numbers**, for an
operator out of a finite-dimensional space.

This is the `p = 2` identity between the two gauges, in the one case where it is not a limit:
evaluate the energy in the right singular basis, where `‖A vᵢ‖ = σᵢ` by
`TauCeti.norm_apply_rightSingularBasis`, and read the singular values as approximation
numbers by `approximationNumber_eq_singularValues`.

**The target's finite-dimensionality is an artefact of the singular system** and is removed
immediately below; it is needed only because `TauCeti.rightSingularBasis` is built from a
finite-dimensional adjoint. -/
private theorem hilbertSchmidtEnergy_eq_sum_approximationNumber_sq_of_finiteDimensional
    {ι : Type*} (A : G →L[𝕜'] H) (b : HilbertBasis ι 𝕜' G) :
    A.hilbertSchmidtEnergy b =
      ∑ i : Fin (Module.finrank 𝕜' G),
        ENNReal.ofReal (A.approximationNumber i) ^ 2 := by
  classical
  set v := (TauCeti.rightSingularBasis (A : G →ₗ[𝕜'] H)).toHilbertBasis with hv
  rw [A.hilbertSchmidtEnergy_indep b v, hilbertSchmidtEnergy, tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hvi : v i = TauCeti.rightSingularBasis (A : G →ₗ[𝕜'] H) i := by
    simp [hv, OrthonormalBasis.coe_toHilbertBasis]
  rw [hvi]
  have hnorm : ‖A (TauCeti.rightSingularBasis (A : G →ₗ[𝕜'] H) i)‖
      = (A : G →ₗ[𝕜'] H).singularValues i :=
    TauCeti.norm_apply_rightSingularBasis _ i
  rw [← ofReal_norm, hnorm, A.approximationNumber_eq_singularValues (i : ℕ)]
  rfl

/-- **The Hilbert--Schmidt energy is the sum of squared approximation numbers**, for an
operator out of a finite-dimensional space and into *any* Hilbert space.

The singular system needs a finite-dimensional target, so the proof corestricts `A` to its
own range — finite-dimensional because the source is — where
`approximationNumber_orthogonalProjectionOnto_range_comp` says the approximation numbers are
unchanged and the corestriction is norm-preserving, so the energy is unchanged term by term.

**The infinite-dimensional-source case is not this plus bookkeeping.** Both sides are then
suprema — the energy over finite subsets of a Hilbert basis, the Schatten gauge over
`Finset ℕ` — and that those two directed families agree is a separate statement. -/
theorem hilbertSchmidtEnergy_eq_sum_approximationNumber_sq {G₀ : Type*}
    [NormedAddCommGroup G₀] [InnerProductSpace 𝕜' G₀] [CompleteSpace G₀]
    [FiniteDimensional 𝕜' G₀] {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace 𝕜' H₀]
    {ι : Type*} (A : G₀ →L[𝕜'] H₀) (b : HilbertBasis ι 𝕜' G₀) :
    A.hilbertSchmidtEnergy b =
      ∑ i : Fin (Module.finrank 𝕜' G₀), ENNReal.ofReal (A.approximationNumber i) ^ 2 := by
  classical
  set W := LinearMap.range ((A : G₀ →L[𝕜'] H₀) : G₀ →ₗ[𝕜'] H₀) with hW
  set S := W.orthogonalProjectionOnto ∘L A with hS
  have hSval : ∀ x, (S x : H₀) = A x := fun x =>
    congrArg Subtype.val
      (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨A x, ⟨x, rfl⟩⟩ : W))
  have henergy : A.hilbertSchmidtEnergy b = S.hilbertSchmidtEnergy b := by
    rw [hilbertSchmidtEnergy, hilbertSchmidtEnergy]
    exact tsum_congr fun i => by rw [← hSval (b i)]; rfl
  rw [henergy, S.hilbertSchmidtEnergy_eq_sum_approximationNumber_sq_of_finiteDimensional b]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun r : ℝ => ENNReal.ofReal r ^ 2)
      (approximationNumber_orthogonalProjectionOnto_range_comp A (i : ℕ))

omit [CompleteSpace H] [FiniteDimensional 𝕜' H] in
/-- **The `p = 2` identity for a finite-dimensional source, as a `tsum` over `ℕ`.**

The sum over `Fin (finrank G₀)` is the whole `tsum`, because
`approximationNumber_eq_zero_of_finrank_le` kills every later term.  This is the form the
infinite-dimensional argument consumes, since there the Schatten gauge is a `tsum` over `ℕ`
on both sides. -/
theorem tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy_of_finiteDimensional
    {G₀ : Type*}
    [NormedAddCommGroup G₀] [InnerProductSpace 𝕜' G₀] [CompleteSpace G₀]
    [FiniteDimensional 𝕜' G₀] {ι : Type*} (A : G₀ →L[𝕜'] H) (b : HilbertBasis ι 𝕜' G₀) :
    ∑' n : ℕ, ENNReal.ofReal (A.approximationNumber n) ^ 2 = A.hilbertSchmidtEnergy b := by
  classical
  rw [A.hilbertSchmidtEnergy_eq_sum_approximationNumber_sq b,
    Fin.sum_univ_eq_sum_range (fun n => ENNReal.ofReal (A.approximationNumber n) ^ 2)
      (Module.finrank 𝕜' G₀)]
  refine tsum_eq_sum fun n hn => ?_
  rw [approximationNumber_eq_zero_of_finrank_le A
    (le_of_not_gt fun h => hn (Finset.mem_range.mpr h))]
  simp


end FiniteSource

section Comparison

variable {𝕜' : Type u} [RCLike 𝕜']
variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace 𝕜' G] [CompleteSpace G]

/-- The isometry of a finite slice of a Hilbert basis: `Euclidean` coordinates in, the
corresponding finite combination of basis vectors out.

It exists so that a *finite* partial sum of a Hilbert--Schmidt energy can be read as the
energy of an operator with finite-dimensional source, where
`hilbertSchmidtEnergy_eq_sum_approximationNumber_sq` applies. -/
noncomputable def finiteBasisInclusion {ι : Type*} (b : HilbertBasis ι 𝕜' G) {n : ℕ}
    (f : Fin n → ι) : EuclideanSpace 𝕜' (Fin n) →L[𝕜'] G :=
  ∑ j, (EuclideanSpace.proj j).smulRight (b (f j))

omit [CompleteSpace G] in
/-- The inclusion in coordinates: a Euclidean vector becomes the corresponding finite
combination of the selected basis vectors. -/
@[simp] theorem finiteBasisInclusion_apply {ι : Type*} (b : HilbertBasis ι 𝕜' G) {n : ℕ}
    (f : Fin n → ι) (x : EuclideanSpace 𝕜' (Fin n)) :
    finiteBasisInclusion b f x = ∑ j, x j • b (f j) := by
  simp [finiteBasisInclusion]

-- Completeness of `G` is what makes `HilbertBasis` available at all, but the identity is a
-- finite Parseval computation and does not use it again.
omit [CompleteSpace G] in
/-- The inclusion is an isometry, by Parseval on a finite orthonormal family. -/
theorem norm_finiteBasisInclusion_apply {ι : Type*} (b : HilbertBasis ι 𝕜' G) {n : ℕ}
    {f : Fin n → ι} (hf : Function.Injective f) (x : EuclideanSpace 𝕜' (Fin n)) :
    ‖finiteBasisInclusion b f x‖ = ‖x‖ := by
  have hon : Orthonormal 𝕜' fun j : Fin n => b (f j) := b.orthonormal.comp f hf
  have hsq : ‖finiteBasisInclusion b f x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [finiteBasisInclusion_apply, @norm_sq_eq_re_inner 𝕜', hon.inner_sum x x Finset.univ,
      EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity),
      map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [RCLike.conj_mul]
      simp
  have h1 : 0 ≤ ‖finiteBasisInclusion b f x‖ := norm_nonneg _
  have h2 : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

/-- The orthogonal projection onto the span of a finite slice of a Hilbert basis, written as
a finite sum so that continuity is free. -/
noncomputable def basisTruncation {ι : Type*} (b : HilbertBasis ι 𝕜' G) (s : Finset ι) :
    G →L[𝕜'] G :=
  ∑ i ∈ s, (innerSL 𝕜' (b i)).smulRight (b i)

omit [CompleteSpace G] in
/-- The truncation in coordinates. -/
theorem basisTruncation_apply {ι : Type*} (b : HilbertBasis ι 𝕜' G) (s : Finset ι) (x : G) :
    basisTruncation b s x = ∑ i ∈ s, ⟪b i, x⟫_𝕜' • b i := by
  simp [basisTruncation]

omit [CompleteSpace G] in
/-- The truncation fixes the selected basis vectors and kills the rest — so its complement
`1 - basisTruncation b s` does the opposite, which is what makes the tail estimate below a
statement about the *unselected* part of the energy. -/
theorem basisTruncation_apply_basis {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι 𝕜' G)
    (s : Finset ι) (j : ι) :
    basisTruncation b s (b j) = if j ∈ s then b j else 0 := by
  classical
  rw [basisTruncation_apply]
  by_cases hj : j ∈ s
  · rw [if_pos hj, Finset.sum_eq_single j]
    · rw [orthonormal_iff_ite.mp b.orthonormal, if_pos rfl, one_smul]
    · intro i _ hij
      rw [orthonormal_iff_ite.mp b.orthonormal, if_neg hij, zero_smul]
    · intro h; exact absurd hj h
  · rw [if_neg hj, Finset.sum_eq_zero]
    intro i hi
    rw [orthonormal_iff_ite.mp b.orthonormal, if_neg (by rintro rfl; exact hj hi), zero_smul]


variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜' H] [CompleteSpace H]

omit [CompleteSpace G] [CompleteSpace H] in
/-- **The energy of the truncation error is the unselected part of the energy.**

`1 - basisTruncation b s` kills the selected basis vectors and fixes the rest, so composing
`T` with it leaves exactly the terms outside `s`. -/
theorem hilbertSchmidtEnergy_comp_one_sub_basisTruncation {ι : Type*} [DecidableEq ι]
    (T : G →L[𝕜'] H) (b : HilbertBasis ι 𝕜' G) (s : Finset ι) :
    (T ∘L (1 - basisTruncation b s)).hilbertSchmidtEnergy b =
      ∑' i, if i ∈ s then 0 else ‖T (b i)‖ₑ ^ 2 := by
  rw [hilbertSchmidtEnergy]
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.comp_apply, sub_apply, one_apply_eq_self,
    basisTruncation_apply_basis]
  by_cases hi : i ∈ s <;> simp [hi]

/-- **The truncation error is bounded by the tail of the energy.**

The operator norm of any operator is at most its Hilbert--Schmidt norm, and the
Hilbert--Schmidt norm of the truncation error is the tail computed above.  This is the one
estimate the reverse inequality needs that the forward one does not. -/
theorem enorm_comp_one_sub_basisTruncation_sq_le {ι : Type*} [DecidableEq ι]
    (T : G →L[𝕜'] H) (b : HilbertBasis ι 𝕜' G) (s : Finset ι) :
    ‖T ∘L (1 - basisTruncation b s)‖ₑ ^ 2 ≤
      ∑' i, if i ∈ s then 0 else ‖T (b i)‖ₑ ^ 2 := by
  calc ‖T ∘L (1 - basisTruncation b s)‖ₑ ^ 2
      ≤ (T ∘L (1 - basisTruncation b s)).hilbertSchmidtENorm ^ 2 :=
        pow_le_pow_left' (enorm_le_hilbertSchmidtENorm _) 2
    _ = (T ∘L (1 - basisTruncation b s)).hilbertSchmidtEnergy b :=
        hilbertSchmidtENorm_sq _ b
    _ = _ := hilbertSchmidtEnergy_comp_one_sub_basisTruncation T b s


/-- The coordinate map dual to `finiteBasisInclusion`: a vector goes to its coefficients
against the selected basis vectors.

Written as a finite sum rather than as `finiteBasisInclusion b f |>.adjoint` so that nothing
here depends on the adjoint API — the only fact needed about it is that its norm is at most
one, and that is Bessel's inequality. -/
noncomputable def finiteBasisCoords {ι : Type*} (b : HilbertBasis ι 𝕜' G) {n : ℕ}
    (f : Fin n → ι) : G →L[𝕜'] EuclideanSpace 𝕜' (Fin n) :=
  ∑ j, (innerSL 𝕜' (b (f j))).smulRight (EuclideanSpace.single j 1)

omit [CompleteSpace G] in
/-- The coordinate map in coordinates. -/
@[simp] theorem finiteBasisCoords_apply {ι : Type*} (b : HilbertBasis ι 𝕜' G) {n : ℕ}
    (f : Fin n → ι) (x : G) (j : Fin n) :
    finiteBasisCoords b f x j = ⟪b (f j), x⟫_𝕜' := by
  classical
  simp [finiteBasisCoords, Pi.single_apply, mul_ite, mul_one, mul_zero]

omit [CompleteSpace G] in
/-- **The coordinate map is a contraction**, which is Bessel's inequality and nothing more. -/
theorem norm_finiteBasisCoords_le {ι : Type*} (b : HilbertBasis ι 𝕜' G) {n : ℕ}
    {f : Fin n → ι} (hf : Function.Injective f) : ‖finiteBasisCoords b f‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  have hon : Orthonormal 𝕜' fun j : Fin n => b (f j) := b.orthonormal.comp f hf
  rw [one_mul, EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ j : Fin n, ‖finiteBasisCoords b f x j‖ ^ 2)
      = Real.sqrt (∑ j : Fin n, ‖⟪b (f j), x⟫_𝕜'‖ ^ 2) := by
        simp only [finiteBasisCoords_apply]
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt (hon.sum_inner_products_le x)
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg x)

omit [CompleteSpace G] in
/-- **The inclusion after the coordinates is the truncation.**

`finiteBasisInclusion ∘L finiteBasisCoords` and `basisTruncation` are both `x ↦ ∑ⱼ ⟪bⱼ, x⟫ • bⱼ`
over the selected indices; this records that, and it is what lets a truncated operator be
factored through a finite-dimensional space without ever mentioning an adjoint. -/
theorem finiteBasisInclusion_comp_finiteBasisCoords {ι : Type*} [DecidableEq ι]
    (b : HilbertBasis ι 𝕜' G) {n : ℕ} {f : Fin n → ι} (hf : Function.Injective f) :
    finiteBasisInclusion b f ∘L finiteBasisCoords b f
      = basisTruncation b (Finset.univ.image f) := by
  ext x
  rw [ContinuousLinearMap.comp_apply, finiteBasisInclusion_apply, basisTruncation_apply,
    Finset.sum_image fun i _ j _ h => hf h]
  exact Finset.sum_congr rfl fun j _ => by rw [finiteBasisCoords_apply]


omit [CompleteSpace G] in
/-- **The energy of `T` restricted to a finite basis slice is that slice of the energy.**

Extracted from the forward inequality's proof, where it was inline, because the reverse
inequality needs the same computation. -/
theorem hilbertSchmidtEnergy_comp_finiteBasisInclusion {ι : Type*} (T : G →L[𝕜'] H)
    (b : HilbertBasis ι 𝕜' G) {n : ℕ} {f : Fin n → ι}
    (c : HilbertBasis (Fin n) 𝕜' (EuclideanSpace 𝕜' (Fin n))) :
    (T ∘L finiteBasisInclusion b f).hilbertSchmidtEnergy c
      = ∑ j : Fin n, ‖T (b (f j))‖ₑ ^ 2 := by
  classical
  set d := (EuclideanSpace.basisFun (Fin n) 𝕜').toHilbertBasis with hd
  rw [(T ∘L finiteBasisInclusion b f).hilbertSchmidtEnergy_indep c d,
    hilbertSchmidtEnergy, tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hdj : d j = EuclideanSpace.single j (1 : 𝕜') := by
    simp [hd, OrthonormalBasis.coe_toHilbertBasis, EuclideanSpace.basisFun_apply]
  rw [ContinuousLinearMap.comp_apply, hdj, finiteBasisInclusion_apply]
  congr 2
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · intro h; exact absurd (Finset.mem_univ j) h


omit [CompleteSpace G] in
/-- **The reverse inequality, for a truncated operator.**

`T ∘L basisTruncation b s` factors as `(T ∘L finiteBasisInclusion) ∘L finiteBasisCoords`, so
its approximation numbers are dominated by those of the finite-source operator, whose squared
sum *is* the corresponding slice of the energy.  No limit is involved — this is the reverse
inequality at every finite stage. -/
theorem tsum_approximationNumber_comp_basisTruncation_sq_le {ι : Type v}
    (T : G →L[𝕜'] H) (b : HilbertBasis ι 𝕜' G) (s : Finset ι) :
    ∑' n : ℕ, ENNReal.ofReal ((T ∘L basisTruncation b s).approximationNumber n) ^ 2
      ≤ T.hilbertSchmidtEnergy b := by
  classical
  set e := s.equivFin with he
  set f : Fin s.card → ι := fun j => (e.symm j : ι) with hfdef
  have hf : Function.Injective f := by
    intro j k hjk
    have hsub : e.symm j = e.symm k := Subtype.ext hjk
    simpa using congrArg e hsub
  have himage : Finset.univ.image f = s := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hfdef]
    exact ⟨by rintro ⟨j, rfl⟩; exact (e.symm j).2, fun hi => ⟨e ⟨i, hi⟩, by simp⟩⟩
  set V := finiteBasisInclusion b f with hV
  set Q := finiteBasisCoords b f with hQ
  have hfactor : T ∘L basisTruncation b s = (T ∘L V) ∘L Q := by
    rw [hV, hQ, ContinuousLinearMap.comp_assoc,
      finiteBasisInclusion_comp_finiteBasisCoords b hf, himage]
  set c := (EuclideanSpace.basisFun (Fin s.card) 𝕜').toHilbertBasis with hc
  calc ∑' n : ℕ, ENNReal.ofReal ((T ∘L basisTruncation b s).approximationNumber n) ^ 2
      ≤ ∑' n : ℕ, ENNReal.ofReal ((T ∘L V).approximationNumber n) ^ 2 := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) 2
        rw [hfactor]
        refine (approximationNumber_comp_le_mul_norm (T ∘L V) Q n).trans ?_
        exact mul_le_of_le_one_right ((T ∘L V).approximationNumber_nonneg n)
          (norm_finiteBasisCoords_le b hf)
    _ = (T ∘L V).hilbertSchmidtEnergy c :=
        tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy_of_finiteDimensional _ c
    _ = ∑ j : Fin s.card, ‖T (b (f j))‖ₑ ^ 2 :=
        hilbertSchmidtEnergy_comp_finiteBasisInclusion T b c
    _ = ∑ i ∈ s, ‖T (b i)‖ₑ ^ 2 := by
        conv_rhs => rw [← himage]
        rw [Finset.sum_image fun i _ j _ h => hf h]
    _ ≤ T.hilbertSchmidtEnergy b := by
        rw [hilbertSchmidtEnergy]
        exact ENNReal.sum_le_tsum s


/-- **The truncation error vanishes along the finite subsets**, when the energy is finite.

This is the only place finiteness of the energy is used: it is what makes the tail of a
convergent sum small, and hence the truncated operator a genuine approximation. -/
theorem tendsto_enorm_comp_one_sub_basisTruncation {ι : Type v}
    (T : G →L[𝕜'] H) (b : HilbertBasis ι 𝕜' G) (h : T.hilbertSchmidtEnergy b ≠ ⊤) :
    Filter.Tendsto (fun s : Finset ι => ‖T ∘L (1 - basisTruncation b s)‖ₑ ^ 2)
      Filter.atTop (nhds 0) := by
  classical
  have hEq : ∀ s : Finset ι,
      (∑' i, if i ∈ s then (0 : ℝ≥0∞) else ‖T (b i)‖ₑ ^ 2)
        = ∑' x : ↑{x : ι | x ∉ s}, ‖T (b (x : ι))‖ₑ ^ 2 := by
    intro s
    rw [tsum_subtype {x : ι | x ∉ s} fun i => ‖T (b i)‖ₑ ^ 2]
    exact tsum_congr fun i => by
      by_cases hi : i ∈ s <;> simp [hi]
  have hcompl := ENNReal.tendsto_tsum_compl_atTop_zero
    (f := fun i => ‖T (b i)‖ₑ ^ 2) (by rwa [← hilbertSchmidtEnergy])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcompl
    (Filter.Eventually.of_forall fun _ => by simp)
    (Filter.Eventually.of_forall fun s => ?_)
  exact (enorm_comp_one_sub_basisTruncation_sq_le T b s).trans (hEq s).le

/-- **The reverse inequality: the Schatten-2 gauge is at most the Hilbert--Schmidt energy.**

With the truncated case in hand, no `ε` is needed and no singular-value decomposition of a
compact operator is needed either — the two routes one would expect.  Instead:
`approximationNumber` is `1`-Lipschitz in the operator norm, the truncation error vanishes
along `Finset.atTop`, so each approximation number of `T` is the limit of those of its
truncations; `ENNReal.tsum_le_liminf_tsum` is Fatou for that limit, and every truncation is
already bounded by the energy.

**Fatou over an arbitrary filter is what makes this work.**  Restricting it to `ℕ` would force
a sequence of finite subsets to be extracted from `Finset.atTop`, which needs choice and buys
nothing. -/
theorem tsum_approximationNumber_sq_le_hilbertSchmidtEnergy {ι : Type v}
    (T : G →L[𝕜'] H) (b : HilbertBasis ι 𝕜' G) :
    ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ 2 ≤ T.hilbertSchmidtEnergy b := by
  classical
  rcases eq_or_ne (T.hilbertSchmidtEnergy b) ⊤ with hE | hE
  · rw [hE]; exact le_top
  have herr := tendsto_enorm_comp_one_sub_basisTruncation T b hE
  -- each approximation number is the limit of those of the truncations
  have hpt : ∀ n : ℕ, Filter.Tendsto
      (fun s : Finset ι =>
        ENNReal.ofReal ((T ∘L basisTruncation b s).approximationNumber n) ^ 2)
      Filter.atTop (nhds (ENNReal.ofReal (T.approximationNumber n) ^ 2)) := by
    intro n
    refine (ENNReal.continuous_pow 2).tendsto _ |>.comp ?_
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    rw [tendsto_iff_dist_tendsto_zero]
    have hnorm : Filter.Tendsto (fun s : Finset ι => ‖T ∘L (1 - basisTruncation b s)‖)
        Filter.atTop (nhds 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε ^ 2 / 2) :=
        ENNReal.ofReal_pos.mpr (by positivity)
      filter_upwards [ENNReal.tendsto_nhds_zero.mp herr _ hpos] with s hs
      have hsq : ‖T ∘L (1 - basisTruncation b s)‖ ^ 2 ≤ ε ^ 2 / 2 := by
        have hrw : ‖T ∘L (1 - basisTruncation b s)‖ₑ ^ 2
            = ENNReal.ofReal (‖T ∘L (1 - basisTruncation b s)‖ ^ 2) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        rw [hrw] at hs
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hs
      have hnn := norm_nonneg (T ∘L (1 - basisTruncation b s))
      have hlt : ‖T ∘L (1 - basisTruncation b s)‖ < ε := by nlinarith
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hlt
    refine squeeze_zero (fun _ => dist_nonneg) (fun s => ?_) hnorm
    rw [Real.dist_eq]
    have hsub : T - T ∘L basisTruncation b s = T ∘L (1 - basisTruncation b s) := by
      ext x; simp
    calc |(T ∘L basisTruncation b s).approximationNumber n - T.approximationNumber n|
        = |T.approximationNumber n - (T ∘L basisTruncation b s).approximationNumber n| :=
          abs_sub_comm _ _
      _ ≤ ‖T - T ∘L basisTruncation b s‖ :=
          abs_approximationNumber_sub_approximationNumber_le _ _ n
      _ = _ := by rw [hsub]
  refine (ENNReal.tsum_le_liminf_tsum hpt).trans ?_
  refine Filter.liminf_le_of_le (by isBoundedDefault) ?_
  intro x hx
  obtain ⟨s, hs⟩ := hx.exists
  exact le_trans hs (tsum_approximationNumber_comp_basisTruncation_sq_le T b s)


-- `G`'s completeness is carried by the `HilbertBasis` argument rather than used again, and
-- the target's is not needed at all: the range factored through is finite-dimensional, so its
-- orthogonal projection exists without completing `H`.
omit [CompleteSpace G] [CompleteSpace H] in
/-- **The Hilbert--Schmidt energy is at most the sum of squared approximation numbers.**

Half of the `p = 2` identity.  A finite partial sum of the energy is the *whole* energy of
`T ∘L finiteBasisInclusion b f`, whose source is finite-dimensional; there
`hilbertSchmidtEnergy_eq_sum_approximationNumber_sq` turns it into squared approximation
numbers, and composing with a norm-one map can only decrease them.  Taking the supremum over
finite subsets gives the energy itself.

Note that `Module.finrank` is never evaluated: the sum over `Fin (finrank _)` is bounded by
the `tsum` over `ℕ` whatever that rank is, so the dimension of the auxiliary Euclidean space
never has to be computed.

**The target needs no hypotheses at all**, not even completeness.  The finite-source identity
this rests on wants a finite-dimensional target, because the singular system is built from a
finite-dimensional adjoint — but `T ∘L finiteBasisInclusion b f` has finite rank, so it
factors through its own range: `S = W.orthogonalProjectionOnto ∘L T ∘L V` has both spaces
finite-dimensional, agrees with `T ∘L V` because the range is exactly `W`, and has norm at
most `‖T‖`.

**The reverse inequality is not proved here**, and is what stands between this and
`TauCeti.schattenIdealFamily 𝕜 2 = TauCeti.hilbertSchmidtIdealFamily 𝕜`.  It does *not* need
an infinite-dimensional spectral theorem, which is worth saying because the obvious route
through one is closed — Mathlib's eigenvector basis is finite-dimensional only.  Bounding
`∑_{n < N} aₙ(T) ^ 2` for **fixed** `N` against a finite-rank truncation, and only then
letting the truncation improve, avoids listing the singular values at all. -/
theorem hilbertSchmidtEnergy_le_tsum_approximationNumber_sq {ι : Type v}
    (T : G →L[𝕜'] H) (b : HilbertBasis ι 𝕜' G) :
    T.hilbertSchmidtEnergy b ≤ ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ 2 := by
  classical
  rw [T.hilbertSchmidtEnergy_eq_iSup_sum b]
  refine iSup_le fun s => ?_
  -- Enumerate `s` without needing an order on `ι`.
  set e := s.equivFin with he
  set f : Fin s.card → ι := fun j => (e.symm j : ι) with hfdef
  have hf : Function.Injective f := by
    intro j k hjk
    have hsub : e.symm j = e.symm k := Subtype.ext hjk
    simpa using congrArg e hsub
  set V := finiteBasisInclusion b f with hV
  have hVnorm : ‖V‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [norm_finiteBasisInclusion_apply b hf x, one_mul]
  set c : HilbertBasis (Fin s.card) 𝕜' (EuclideanSpace 𝕜' (Fin s.card)) :=
    (EuclideanSpace.basisFun (Fin s.card) 𝕜').toHilbertBasis with hc
  have hcapply : ∀ j, V (c j) = b (f j) := by
    intro j
    rw [hc, hV, finiteBasisInclusion_apply]
    simp [OrthonormalBasis.coe_toHilbertBasis, EuclideanSpace.basisFun_apply]
  -- The partial sum is the whole energy of `T ∘L V`.
  have hsum : ∑ i ∈ s, ‖T (b i)‖ₑ ^ 2 = (T ∘L V).hilbertSchmidtEnergy c := by
    rw [hilbertSchmidtEnergy, tsum_fintype,
      ← Finset.sum_attach s fun i => ‖T (b i)‖ₑ ^ 2]
    refine Fintype.sum_equiv e (fun i : {x // x ∈ s} => ‖T (b (i : ι))‖ₑ ^ 2)
      (fun j : Fin s.card => ‖(T ∘L V) (c j)‖ₑ ^ 2) fun i => ?_
    rw [ContinuousLinearMap.comp_apply, hcapply, hfdef]
    simp
  -- `T ∘L V` has finite rank, so it factors through its own range, where the target is
  -- finite-dimensional and the singular system is available.  The factor is isometric, so
  -- the energy is unchanged term by term.
  set W := LinearMap.range ((T ∘L V : EuclideanSpace 𝕜' (Fin s.card) →L[𝕜'] H) :
    EuclideanSpace 𝕜' (Fin s.card) →ₗ[𝕜'] H) with hW
  set P := (W.orthogonalProjectionOnto : H →L[𝕜'] W) with hP
  set S := P ∘L (T ∘L V) with hS
  have hSval : ∀ x, (S x : H) = (T ∘L V) x := by
    intro x
    have hmem : (T ∘L V) x ∈ W := ⟨x, rfl⟩
    rw [hS, ContinuousLinearMap.comp_apply, hP]
    exact congrArg Subtype.val
      (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨(T ∘L V) x, hmem⟩ : W))
  have henergy : (T ∘L V).hilbertSchmidtEnergy c = S.hilbertSchmidtEnergy c := by
    rw [hilbertSchmidtEnergy, hilbertSchmidtEnergy]
    refine tsum_congr fun j => ?_
    rw [← hSval (c j)]
    rfl
  rw [hsum, henergy, S.hilbertSchmidtEnergy_eq_sum_approximationNumber_sq c]
  calc ∑ i : Fin (Module.finrank 𝕜' (EuclideanSpace 𝕜' (Fin s.card))),
        ENNReal.ofReal (S.approximationNumber i) ^ 2
      ≤ ∑ i : Fin (Module.finrank 𝕜' (EuclideanSpace 𝕜' (Fin s.card))),
          ENNReal.ofReal (T.approximationNumber i) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) 2
        refine (approximationNumber_comp_comp_le P T V i).trans ?_
        have hPnorm : ‖P‖ ≤ 1 := by
          rw [hP]; exact Submodule.orthogonalProjectionOnto_norm_le W
        have hnn := T.approximationNumber_nonneg i
        have hPa : ‖P‖ * T.approximationNumber i ≤ T.approximationNumber i :=
          mul_le_of_le_one_left hnn hPnorm
        exact le_trans
          (mul_le_of_le_one_right (mul_nonneg (norm_nonneg P) hnn) hVnorm) hPa
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun n => ENNReal.ofReal (T.approximationNumber n) ^ 2)]
        exact ENNReal.sum_le_tsum _

/-- **The `p = 2` identity: the Schatten-2 gauge is the Hilbert--Schmidt energy.**

Both inequalities are proved above — the forward one by truncating the basis and reading the
finite case exactly, the reverse by Fatou against the same truncations. -/
theorem tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy_of_hilbertBasis {ι : Type v}
    (T : G →L[𝕜'] H) (b : HilbertBasis ι 𝕜' G) :
    ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ 2 = T.hilbertSchmidtEnergy b :=
  le_antisymm (tsum_approximationNumber_sq_le_hilbertSchmidtEnergy T b)
    (hilbertSchmidtEnergy_le_tsum_approximationNumber_sq T b)


end Comparison

section Gauge

/-- The **Schatten `p`-norm**, valued in `ℝ≥0∞` and therefore defined for every bounded
operator: it is `∞` exactly when `T` is not Schatten-`p`. -/
noncomputable def schattenENorm (p : ℝ) (T : E →L[𝕜] F) : ℝ≥0∞ :=
  (∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ p) ^ p⁻¹

-- Reading the finite gauge in `ℝ≥0∞` is arithmetic; neither space needs to be complete.
omit [CompleteSpace E] [CompleteSpace F] in
/-- The truncated `ℓᵖ` gauge, read in `ℝ≥0∞`.  This is the bridge between the real finite
theory, where the majorization argument lives, and the `ℝ≥0∞` gauge, where the ideal laws
are stated unconditionally. -/
theorem ofReal_lpGauge_approximationNumber {p : ℝ} (hp0 : 0 < p) (T : E →L[𝕜] F) (k : ℕ) :
    ENNReal.ofReal
        (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i)) =
      (∑ n ∈ Finset.range k, ENNReal.ofReal (T.approximationNumber n) ^ p) ^ p⁻¹ := by
  have hsum : ∀ i : Fin k, |T.approximationNumber i| ^ p = T.approximationNumber i ^ p :=
    fun i => by rw [abs_of_nonneg (T.approximationNumber_nonneg i)]
  rw [TauCeti.FiniteVector.lpGauge, one_div]
  rw [← ENNReal.ofReal_rpow_of_nonneg
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) (by positivity)]
  congr 1
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _,
    Fin.sum_univ_eq_sum_range
      (fun m => ENNReal.ofReal (|T.approximationNumber m| ^ p)) k]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [abs_of_nonneg (T.approximationNumber_nonneg m),
    ENNReal.ofReal_rpow_of_nonneg (T.approximationNumber_nonneg m) hp0.le]

-- A partial sum is at most its `tsum`; again no completeness is used.
omit [CompleteSpace E] [CompleteSpace F] in
/-- Every truncated `ℓᵖ` gauge is dominated by the whole Schatten norm. -/
theorem ofReal_lpGauge_le_schattenENorm {p : ℝ} (hp0 : 0 < p) (T : E →L[𝕜] F) (k : ℕ) :
    ENNReal.ofReal
        (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i)) ≤
      T.schattenENorm p := by
  rw [ofReal_lpGauge_approximationNumber hp0 T k, schattenENorm]
  exact ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum _) (by positivity)

section Triangle

variable [HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]

/-- **The Schatten triangle inequality.**

Each truncation is handled by `lpGauge_approximationNumber_add_le`, whose right-hand side is
already bounded by the two whole gauges; the `tsum` on the left is the supremum of those
truncations, so the bound passes to the limit with nothing further to prove. -/
theorem schattenENorm_add_le {p : ℝ} (hp : 1 ≤ p) (S T : E →L[𝕜] F) :
    (S + T).schattenENorm p ≤ S.schattenENorm p + T.schattenENorm p := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  set R := S.schattenENorm p + T.schattenENorm p with hR
  have hstep : ∀ k : ℕ,
      (∑ n ∈ Finset.range k, ENNReal.ofReal ((S + T).approximationNumber n) ^ p) ^ p⁻¹ ≤ R := by
    intro k
    rw [← ofReal_lpGauge_approximationNumber hp0 (S + T) k]
    calc ENNReal.ofReal
          (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => (S + T).approximationNumber i))
        ≤ ENNReal.ofReal
            (TauCeti.FiniteVector.lpGauge p (fun i : Fin k => S.approximationNumber i) +
              TauCeti.FiniteVector.lpGauge p (fun i : Fin k => T.approximationNumber i)) :=
          ENNReal.ofReal_le_ofReal (lpGauge_approximationNumber_add_le hp S T k)
      _ = _ := ENNReal.ofReal_add (TauCeti.FiniteVector.lpGauge_nonneg _ _)
          (TauCeti.FiniteVector.lpGauge_nonneg _ _)
      _ ≤ R := add_le_add (ofReal_lpGauge_le_schattenENorm hp0 S k)
          (ofReal_lpGauge_le_schattenENorm hp0 T k)
  -- The partial sums are bounded by `R ^ p`, and `∑'` is their supremum.
  have hpow : ∀ k : ℕ,
      ∑ n ∈ Finset.range k, ENNReal.ofReal ((S + T).approximationNumber n) ^ p ≤ R ^ p := by
    intro k
    have h := ENNReal.rpow_le_rpow (hstep k) hp0.le
    rwa [← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at h
  have htsum : ∑' n : ℕ, ENNReal.ofReal ((S + T).approximationNumber n) ^ p ≤ R ^ p :=
    ENNReal.tsum_eq_iSup_nat.trans_le (iSup_le hpow)
  have := ENNReal.rpow_le_rpow htsum (by positivity : (0 : ℝ) ≤ p⁻¹)
  rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one] at this

end Triangle

-- Scaling scales every approximation number, so it scales the whole sum; completeness is
-- not used.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **Absolute homogeneity.** -/
theorem schattenENorm_smul {p : ℝ} (hp0 : 0 < p) (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).schattenENorm p = ‖c‖ₑ * T.schattenENorm p := by
  have hterm : ∀ n : ℕ, ENNReal.ofReal ((c • T).approximationNumber n) ^ p =
      ‖c‖ₑ ^ p * ENNReal.ofReal (T.approximationNumber n) ^ p := by
    intro n
    rw [approximationNumber_smul, ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  rw [schattenENorm, schattenENorm]
  simp only [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ p⁻¹),
    ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one]

-- The zeroth term alone gives the bound, so no completeness is needed.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Schatten norm dominates the operator norm**, being its zeroth term. -/
theorem enorm_le_schattenENorm {p : ℝ} (hp0 : 0 < p) (T : E →L[𝕜] F) :
    ‖T‖ₑ ≤ T.schattenENorm p := by
  have hz : ‖T‖ₑ ^ p ≤ ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ p := by
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum 0)
    rw [← ofReal_norm, ← T.approximationNumber_index_zero]
  have := ENNReal.rpow_le_rpow hz (by positivity : (0 : ℝ) ≤ p⁻¹)
  rwa [← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one] at this

/-- **Adjoint invariance**, immediate from invariance of the approximation numbers.  This is
what makes the Schatten family *symmetric*. -/
theorem schattenENorm_adjoint (p : ℝ) (T : E →L[𝕜] F) :
    T.adjoint.schattenENorm p = T.schattenENorm p := by
  simp only [schattenENorm, approximationNumber_adjoint]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The two-sided ideal bound.** -/
theorem schattenENorm_comp_le {p : ℝ} (hp0 : 0 < p) {G H : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E) :
    (L ∘L T ∘L R).schattenENorm p ≤ ‖L‖ₑ * T.schattenENorm p * ‖R‖ₑ := by
  have hterm : ∀ n : ℕ, ENNReal.ofReal ((L ∘L T ∘L R).approximationNumber n) ^ p ≤
      (‖L‖ₑ * ‖R‖ₑ) ^ p * ENNReal.ofReal (T.approximationNumber n) ^ p := by
    intro n
    have h := ENNReal.ofReal_le_ofReal (approximationNumber_comp_comp_le L T R n)
    refine le_trans (ENNReal.rpow_le_rpow h hp0.le) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (mul_nonneg (norm_nonneg L) (T.approximationNumber_nonneg n)),
      ENNReal.ofReal_mul (norm_nonneg L), ofReal_norm, ofReal_norm,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    ring
  calc (L ∘L T ∘L R).schattenENorm p
      ≤ ((‖L‖ₑ * ‖R‖ₑ) ^ p * ∑' n : ℕ, ENNReal.ofReal (T.approximationNumber n) ^ p) ^ p⁻¹ := by
        refine ENNReal.rpow_le_rpow ?_ (by positivity)
        rw [← ENNReal.tsum_mul_left]
        exact ENNReal.tsum_le_tsum hterm
    _ = ‖L‖ₑ * T.schattenENorm p * ‖R‖ₑ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ p⁻¹),
          ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0.ne', ENNReal.rpow_one, schattenENorm]
        ring

-- Lower semicontinuity is about the approximation-number sequence; no completeness is used.
omit [CompleteSpace E] [CompleteSpace F] in
/-- **The Schatten norm is lower semicontinuous along operator-norm convergence**, stated at
the `p`-th power.

Same shape as `nuclearENorm_le_liminf`: the summands are continuous images of the
approximation numbers and `ENNReal.tsum_le_liminf_tsum` handles the sum.

**Stated at the `p`-th power deliberately**, which is also why the Hilbert--Schmidt twin is
stated at the square.  Pulling `^ p⁻¹` out of a `liminf` needs that map to commute with
`liminf`, which is true but is a separate lemma about `ℝ≥0∞`; at the `p`-th power the sum is
literally the `liminf`'s subject and nothing has to commute.  Consumers undo it with
`ENNReal.rpow_le_rpow_iff`. -/
theorem schattenENorm_rpow_le_liminf {p : ℝ} (hp0 : 0 < p) {u : Filter ℕ} [u.NeBot]
    {T : ℕ → E →L[𝕜] F} {L : E →L[𝕜] F}
    (hop : Filter.Tendsto (fun n => ‖T n - L‖) u (nhds 0)) :
    L.schattenENorm p ^ p ≤ Filter.liminf (fun n => (T n).schattenENorm p ^ p) u := by
  have hpow : ∀ S : E →L[𝕜] F, S.schattenENorm p ^ p
      = ∑' i : ℕ, ENNReal.ofReal (S.approximationNumber i) ^ p := by
    intro S
    rw [schattenENorm, ← ENNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  simp only [hpow]
  refine ENNReal.tsum_le_liminf_tsum fun i => ?_
  refine (ENNReal.continuous_rpow_const.tendsto _).comp ?_
  refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hop
  rw [Real.dist_eq]
  exact abs_approximationNumber_sub_approximationNumber_le (T n) L i

omit [CompleteSpace E] [CompleteSpace F] in
/-- The Schatten norm is unchanged by negation, term by term. -/
@[simp] theorem schattenENorm_neg (p : ℝ) (T : E →L[𝕜] F) :
    (-T).schattenENorm p = T.schattenENorm p := by
  simp only [schattenENorm, approximationNumber_neg]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `T` is **Schatten-`p`** when its Schatten norm is finite. -/
def IsSchattenClass (p : ℝ) (T : E →L[𝕜] F) : Prop := T.schattenENorm p ≠ ∞

section AgreementAtOne

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- **At `p = 1` the Schatten norm is the nuclear norm.**  Both are `tsum`s of the same
sequence and the exponents are `1` and `1⁻¹`, so this is arithmetic in `ℝ≥0∞` rather than a
theorem about operators.

The `p = 2` counterpart is *not* arithmetic and is not proved here: `hilbertSchmidtENorm` is
built from the Hilbert--Schmidt energy through a basis and never mentions approximation
numbers, so relating the two needs Parseval together with the singular-value decomposition —
a statement this library does not contain. -/
theorem schattenENorm_one (T : E →L[𝕜] F) : T.schattenENorm 1 = T.nuclearENorm := by
  simp [schattenENorm, nuclearENorm]

end AgreementAtOne

end Gauge

end ContinuousLinearMap

namespace TauCeti

universe u v

open ContinuousLinearMap

/-- **The Schatten-`p` operator ideal**, for `1 ≤ p`.

At `p = 1` its gauge is the nuclear norm and at `p = 2` the Hilbert--Schmidt norm; those two
families are built separately in this directory from their own arguments, and agreeing with
them is not asserted here. -/
noncomputable def schattenIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] {p : ℝ} (hp : 1 ≤ p) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge A := A.schattenENorm p
  gauge_add_le A B := schattenENorm_add_le hp A B
  gauge_smul c A := schattenENorm_smul (lt_of_lt_of_le zero_lt_one hp) c A
  enorm_le_gauge A := enorm_le_schattenENorm (lt_of_lt_of_le zero_lt_one hp) A
  gauge_comp_le L A R := schattenENorm_comp_le (lt_of_lt_of_le zero_lt_one hp) L A R
  gauge_adjoint A := schattenENorm_adjoint p A

/-- **The Schatten ideal is complete**, for the same reason the trace-class ideal is: the
gauge dominates the operator norm, so a gauge-Cauchy sequence has an operator-norm limit,
and `schattenENorm_rpow_le_liminf` then puts that limit in the ideal and gives convergence
in the gauge. -/
instance isComplete_schattenIdealFamily {𝕜 : Type u} [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] {p : ℝ} (hp : 1 ≤ p) :
    (schattenIdealFamily.{u, v} 𝕜 hp).toOperatorIdealFamily.IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
    refine Metric.complete_of_cauchySeq_tendsto fun a ha => ?_
    have hop : CauchySeq fun n => (a n).val := by
      rw [Metric.cauchySeq_iff] at ha ⊢
      intro ε hε
      obtain ⟨M, hM⟩ := ha ε hε
      refine ⟨M, fun m hm n hn => lt_of_le_of_lt ?_ (hM m hm n hn)⟩
      rw [dist_eq_norm, dist_eq_norm]
      exact TauCeti.OperatorIdealFamily.Elem.norm_val_le (a m - a n)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hop
    have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        (L - (a n).val).schattenENorm p ≤ ENNReal.ofReal ε := by
      intro ε hε
      rw [Metric.cauchySeq_iff] at ha
      obtain ⟨N, hN⟩ := ha ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hfatou : (L - (a n).val).schattenENorm p ^ p ≤
          Filter.liminf (fun m => ((a m).val - (a n).val).schattenENorm p ^ p)
            Filter.atTop := by
        refine ContinuousLinearMap.schattenENorm_rpow_le_liminf hp0 ?_
        have hd : Filter.Tendsto (fun m => dist ((a m).val) L) Filter.atTop (nhds 0) :=
          tendsto_iff_dist_tendsto_zero.mp hL
        simpa [dist_eq_norm] using hd
      have hev : ∀ᶠ m in Filter.atTop,
          ((a m).val - (a n).val).schattenENorm p ^ p ≤ ENNReal.ofReal ε ^ p := by
        filter_upwards [Filter.eventually_ge_atTop N] with m hm
        have hd : ‖a m - a n‖ < ε := by simpa [dist_eq_norm] using hN m hm n hn
        have hgauge : ((a m).val - (a n).val).schattenENorm p ≤ ENNReal.ofReal ε := by
          have heq : (schattenIdealFamily.{u, v} 𝕜 hp).gauge (a m - a n).val
              = ((a m).val - (a n).val).schattenENorm p := rfl
          rw [← heq, ← TauCeti.OperatorIdealFamily.Elem.enorm_eq_gauge, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hd.le
        exact ENNReal.rpow_le_rpow hgauge hp0.le
      have hle : Filter.liminf
          (fun m => ((a m).val - (a n).val).schattenENorm p ^ p) Filter.atTop
          ≤ ENNReal.ofReal ε ^ p := by
        calc Filter.liminf
              (fun m => ((a m).val - (a n).val).schattenENorm p ^ p) Filter.atTop
            ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal ε ^ p) Filter.atTop :=
              Filter.liminf_le_liminf hev
          _ = ENNReal.ofReal ε ^ p := Filter.liminf_const _
      exact (ENNReal.rpow_le_rpow_iff hp0).mp (hfatou.trans hle)
    obtain ⟨N₁, hN₁⟩ := hcauchy 1 one_pos
    have hmemL : L ∈ (schattenIdealFamily.{u, v} 𝕜 hp).toOperatorIdealFamily.carrier := by
      have hsplit : L = (L - (a N₁).val) + (a N₁).val := by abel
      rw [TauCeti.OperatorIdealFamily.mem_carrier_iff, hsplit]
      refine ne_top_of_le_ne_top ?_
        ((schattenIdealFamily.{u, v} 𝕜 hp).toOperatorIdealFamily.gauge_add_le _ _)
      refine ENNReal.add_ne_top.mpr ⟨?_, (a N₁).gauge_val_ne_top⟩
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hN₁ N₁ le_rfl)
    refine ⟨TauCeti.OperatorIdealFamily.Elem.mk hmemL, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hgauge : ((a n).val - L).schattenENorm p ≤ ENNReal.ofReal (ε / 2) := by
      have hneg : ((a n).val - L) = -(L - (a n).val) := by abel
      rw [hneg, ContinuousLinearMap.schattenENorm_neg]
      exact hN n hn
    have hle : ‖a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL‖ ≤ ε / 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgauge
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    calc dist (a n) (TauCeti.OperatorIdealFamily.Elem.mk hmemL)
        = ‖a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL‖ := dist_eq_norm _ _
      _ ≤ ε / 2 := hle
      _ < ε := by linarith

variable {𝕜 : Type u} [RCLike 𝕜]
  [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The gauge of the Schatten family *is* the Schatten norm, definitionally. -/
@[simp] theorem gauge_schattenIdealFamily {p : ℝ} (hp : 1 ≤ p) (A : E →L[𝕜] F) :
    (schattenIdealFamily.{u, v} 𝕜 hp).gauge A = A.schattenENorm p := (rfl)

/-- Membership in the Schatten ideal is exactly `IsSchattenClass`. -/
theorem mem_schattenIdealFamily_carrier_iff {p : ℝ} (hp : 1 ≤ p) (A : E →L[𝕜] F) :
    A ∈ (schattenIdealFamily.{u, v} 𝕜 hp).toOperatorIdealFamily.carrier ↔
      A.IsSchattenClass p := (Iff.rfl)

/-- **The Schatten ideal at `p = 1` is the trace-class ideal**, as families and not merely as
gauges.  `OperatorIdealFamily.ext` is what makes the upgrade available: a family in this
presentation is determined by its gauge, including off the ideal, so the two structures agree
once their gauges do. -/
theorem schattenIdealFamily_one_eq_traceClassIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜] :
    schattenIdealFamily.{u, v} 𝕜 (le_refl (1 : ℝ)) = traceClassIdealFamily.{u, v} 𝕜 := by
  exact SymmetricOperatorIdealFamily.ext fun {_E _F} _ _ _ _ _ _ A => A.schattenENorm_one

end TauCeti
