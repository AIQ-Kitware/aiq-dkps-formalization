# 145000 — From rotation counterexample to real transport matching

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `034000–038000`, `042000–051000`, `130000–135000`. **Next:** `146000`.

<!-- BEGIN SPOKEN LECTURE -->

# From rotation counterexample to real transport matching

Earlier we saw that the canonical direct rotation is not always the best orthogonal transporter when the cost is an unsquared, whole-space Schatten norm. The real four-dimensional counterexample was enough to disprove the general printed optimality claim. A counterexample, however, does not solve the minimization problem. Today we will build a more complete model: transport costs can be organized into independent principal-angle labels, with the freedom to couple certain labels in pairs.

## What are we optimizing?

Take two subspaces K and L of equal finite dimension inside a real Euclidean space. Consider every orthogonal operator U that maps K onto L. Measure its displacement from the identity using a Schatten p norm. Concretely, take every singular value of the difference between U and the identity, raise it to power p, add, and then take the pth root.

For p equal two, this is the Frobenius norm. For p equal one, it is the nuclear or trace norm. When p lies strictly between one and two, the contribution of a set of singular values differs from its squared-energy contribution. That is precisely where the direct rotation can lose optimality.

Why do we require equal dimensions? An invertible orthogonal map preserves dimension. If K and L have different dimensions, no such U maps one onto the other, regardless of how close their projections might be. We would first need a different admissible notion of transport.

## The single principal-angle block

Begin with a single principal angle theta between two lines. In their common real two-dimensional principal plane, an orthogonal rotation through theta maps the first line to the second. Its displacement operator has two equal singular values, each equal to twice sine of theta over two. Therefore its pth power Schatten cost is two times the quantity twice sine theta over two, raised to power p.

There is a choice of the sign of the rotation, but its singular values are the same. Reflections can also map one line to the other. Their displacement costs may differ, so the full optimization must allow all orthogonal transports, not just orientation-preserving rotations.

With two or more principal angles, a naive strategy would minimize the cost in each principal plane independently and sum. That works for some objectives, but our four-dimensional counterexample demonstrated a failure of unrestricted independent-plane optimality.

The missing degree of freedom is a coupling between two principal-angle blocks. A four-dimensional orthogonal operator can mix their coordinates while still mapping the entire source subspace onto the target. It might produce a more favorable distribution of displacement singular values under the chosen exponent.

## Why a matching appears

The real transport formalization turns that freedom into a finite combinatorial problem. Label the positive principal angles. Each label can remain a singleton, carrying the best permitted one-angle cost, or it can be paired with another label, carrying the best two-angle cost from a four-dimensional block.

A matching is a collection of disjoint pairs together with unmatched singletons. In Lean it is encoded by an involutive permutation: a fixed point means a singleton, and a two-cycle means a paired block. No angle label can belong to two different pairs.

The cost of a matching is the sum of singleton weights and complete pair weights. If we sum over all labels rather than over edges, each pair contributes half its full weight at each endpoint, so it is counted exactly once. The minimum over all matchings exists because the set of involutive permutations of finitely many labels is finite.

This is a substantial simplification. Instead of optimizing over a continuum of orthogonal matrices all at once, we can evaluate finitely many candidate matchings, where the difficult continuous optimization has been absorbed into the one-angle and two-angle weights.

## An exact two-angle test

Suppose the positive principal angles are theta and psi. There are two combinatorial candidates. One leaves both labels unmatched. Its cost is the sum of the two singleton costs. The other pairs them, and its cost is a single optimized four-dimensional value.

The global minimum is the smaller of those two numbers. For p equal two, the squared Frobenius objective is tied directly to the sum of squared displacements, and the canonical direct rotation satisfies the established squared-objective theorem. For exponents strictly between one and two, the paired option can be better.

You must not replace the optimized pair cost with the direct rotation's pair cost. Doing so would rebuild the false optimality claim into the supposed solution. The pair cost is obtained by minimizing over both relevant four-dimensional determinant classes; the source formalization treats that minimization explicitly.

For three positive angles, the finite choices are: three singletons, or one pair and one singleton. For four, we also have two disjoint pairs. In general, the number of matchings grows, but the mathematical structure stays finite and explicit.

## The two directions of an optimality proof

A formula for the minimum needs two distinct inequalities. First, every admissible real orthogonal transporter must have a displacement cost at least the matching minimum. Second, every candidate matching, or at least an optimal matching, must be realizable by a genuine orthogonal transporter with exactly the assigned cost.

The first direction is an extraction theorem. It analyzes an ambient optimizer and shows that its cost is represented by suitable singleton and paired blocks, preserving the original principal-angle labels. The second direction is a realization theorem. It assembles orthogonal blocks into an ambient transporter with the required action on the source subspace.

Neither direction can be replaced merely by noting that the minimum of finitely many numbers exists. A combinatorial optimizer might describe no actual geometric operator unless realization is proved. Conversely, a construction of candidate transports does not rule out a more exotic, lower-cost orthogonal matrix.

The repository contains both ingredients for a stated regime: finite-dimensional real subspaces of equal dimension and Schatten exponent p strictly between one and two. It proves the existence of an ambient minimizing orthogonal transporter whose pth power cost equals the matching minimum. It also keeps track of repeated angles and zero angles rather than discarding their coordinate labels by an informal generic-position assumption.

## Why the exponent matters

The nuclear norm is the sum of singular values, and the Frobenius norm comes from their squared sum. A cost that is additive in squared singular values rewards a different distribution than a cost that is additive in singular values themselves. Between powers one and two, changing the singular-value distribution by mixing principal planes can be advantageous.

This is why one must name the exponent in an optimality theorem. The best operator for one Schatten norm need not minimize another. The direct rotation's optimality for a squared objective does not imply its optimality for an unsquared objective, even though the underlying pair of subspaces is identical.

There are also delicate endpoint questions. A theorem proved for exponents strictly between one and two should not be quoted as automatically covering p equal one or p equal two. Continuity of an optimized value can help study endpoint costs, but a complete endpoint statement may need its own realization and attainment arguments.

## What the Lean result actually says

The main named theorem in the present source asserts existence of a minimizing real Schatten transport matching in the regime just stated. It represents the cost using the minimum of positive-angle matching weights and proves that its transporter beats every admissible orthogonal competitor.

The assumptions include finite dimension, a real inner product, equal source and target dimension, and p strictly between one and two. The conclusion concerns the pth power of the Schatten norm of identity minus the transporter; taking the pth root preserves comparisons because p is positive. The theorem does not state a universal result for arbitrary symmetric gauges or every exponent.

To reconstruct the argument, begin with principal planes, calculate the two equal singular values of a planar rotation, state the optimized one- and two-angle costs, and prove that any matching can be assembled by orthogonal direct sum. Then identify the genuinely difficult converse: ruling out an ambient transport more efficient than every matching. That converse is why this is a mathematical theorem rather than a convenient search heuristic.

The counterexample from Section four has led us to a positive classification of one important optimization problem. Next we leave square self-adjoint matrices and ask how to control singular subspaces of genuinely rectangular maps.

<!-- END SPOKEN LECTURE -->

---

## Display-only mathematical and Lean correspondence

The matching program lives in `DavisKahan/FiniteDimensional/DirectRotation/SchattenRealMatching.lean`, `.../SchattenRealMatchingWeights.lean`, and `.../RealMatchingAttainment.lean`. For a planar rotation by `θ`, the two displacement singular values equal `2 sin(θ/2)`; the direct-rotation **candidate** p-cost is therefore `2(2 sin(θ/2))^p`. The singleton and paired weights in the matching theorem refer to their own optimized class-specific definitions, not to this candidate formula by default.

The source theorem `exists_minimizing_real_schatten_transport_matching` proves the unrestricted ambient minimum for real finite-dimensional equally ranked subspaces and `1<p<2`. Do not extend the result to other exponents merely from this declaration.

## Exact Lean declaration excerpts

**`realSchattenMatchingCost`** — The combinatorial cost sums fixed-point singleton weights and half a paired weight at each endpoint of a two-cycle. The paired weight comes from the optimized four-dimensional model.

Source: `DavisKahan/FiniteDimensional/DirectRotation/SchattenRealMatching.lean`; exact declaration header (proof body omitted).

```lean
def realSchattenMatchingCost {ι : Type*} [Fintype ι]
    (p : ℝ) (theta : ι → ℝ) (s : Equiv.Perm ι) : ℝ := by
```

**`exists_attains_realSchattenMatchingMinimum`** — This theorem only attains the FINITE COMBINATORIAL minimum. It does not by itself construct an ambient orthogonal transporter.

Source: `DavisKahan/FiniteDimensional/DirectRotation/SchattenRealMatching.lean`; exact declaration header (proof body omitted).

```lean
theorem exists_attains_realSchattenMatchingMinimum {ι : Type*} [Fintype ι]
    (p : ℝ) (theta : ι → ℝ) :
    ∃ s : Equiv.Perm ι, Function.Involutive s ∧
      realSchattenMatchingCost p theta s = realSchattenMatchingMinimum p theta := by
```

**`exists_minimizing_real_schatten_transport_matching`** — This theorem supplies the missing geometric attainment and global comparison for equal-dimensional REAL subspaces with Schatten exponent strictly between one and two.

Source: `DavisKahan/FiniteDimensional/DirectRotation/RealMatchingAttainment.lean`; exact declaration header (proof body omitted).

```lean
theorem exists_minimizing_real_schatten_transport_matching
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℝ E) (hKL : Module.finrank ℝ K = Module.finrank ℝ L) :
    ∃ U : E ≃ₗᵢ[ℝ] E, K.map U.toLinearMap = L ∧
      UnitarilyInvariantSeminorm.schatten ℝ E E p
          (LinearMap.id - U.toLinearMap) ^ p.toReal =
        realPositiveSchattenMatchingMinimum p.toReal
          (fun j : {j : Fin (Module.finrank ℝ K) // 0 < K.principalAngles L j} =>
            K.principalAngles L j.val) ∧
      ∀ T : E ≃ₗᵢ[ℝ] E, K.map T.toLinearMap = L →
        UnitarilyInvariantSeminorm.schatten ℝ E E p
            (LinearMap.id - U.toLinearMap) ^ p.toReal ≤
          UnitarilyInvariantSeminorm.schatten ℝ E E p
            (LinearMap.id - T.toLinearMap) ^ p.toReal := by
```

