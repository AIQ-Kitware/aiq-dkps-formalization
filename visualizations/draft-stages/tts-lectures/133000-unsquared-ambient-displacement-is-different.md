# 133000 — Unsquared ambient displacement is different

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `130000–132000`. **Next:** `134000`.

<!-- BEGIN SPOKEN LECTURE -->

# Unsquared ambient displacement is different

Davis and Kahan's Section Four contains three valid optimization mechanisms and one printed claim that does not follow from them. We have just proved the restricted displacement theorem and the squared full-displacement theorem. Now we will examine the fourth claim on its own terms: does the direct rotation minimize every unitarily invariant norm of the **unsquared full displacement** when all principal angles are small?

The proposition as printed proposes a threshold of sixty degrees in the real case. Our task is to understand why that threshold looks plausible, why the available proofs cannot establish it, and which piece of the optimization problem changes in higher dimension.

## Define the ambient transport problem

Take a real Euclidean space and two subspaces U and V of the same dimension. A competitor is an orthogonal matrix W satisfying W U equals V. For a chosen unitarily invariant norm N, measure its cost by N of identity minus W, acting on the entire ambient space.

The canonical direct rotation D is one feasible competitor. On each principal plane it turns the source direction into the target direction through the prescribed principal angle, while choosing a compatible action on the perpendicular direction. It therefore has easily computed displacement singular values.

The optimization is not over the principal angles. The subspaces and their principal angles are fixed. We are varying W among **all** orthogonal matrices carrying U onto V. Such a W can rotate vectors inside the target subspace, and can act independently on the complement before the canonical transport. Those freedoms can mix principal planes, which changes the spectrum of identity minus W.

For two-dimensional lines in the plane, there is little freedom. In four dimensions, there is substantially more.

## Why sixty degrees arises in the plane

Let U and V be real lines meeting at a principal angle theta between zero and ninety degrees. An orthogonal transporter of the plane taking U onto V belongs to an orientation-preserving or orientation-reversing component. Each component has two sign choices for the image of a unit source vector, but the least costly representative has a simple form.

The least-displacing orientation-preserving choice is the direct rotation through theta. Its displacement singular values are both a, where a equals two sine of theta over two.

The orientation-reversing choices are reflections that send the source line onto the target line. Its displacement singular values are two and zero.

A unitarily invariant norm is a symmetric gauge of these singular values. The direct rotation is no worse than the reflection for **every** such gauge exactly when the sorted list a,a is weakly majorized by the list two,zero. The largest-entry condition says a is at most two, always true. The two-entry condition says twice a is at most two, or a is at most one.

Since a equals two sine of theta over two, this becomes theta at most sixty degrees. Thus the threshold is not arbitrary. It follows from an exact two-dimensional singular-value comparison.

However, nothing in this argument says that an arbitrary higher-dimensional competitor can be decomposed into independent rotations or reflections on the original principal planes. That would be an extra structural assertion, and it is false.

## The hidden assumption in the generalization

Imagine two independent principal planes, both with the same small angle theta. The canonical direct rotation acts as a theta rotation on each of them. We might be tempted to say that any competing transporter must incur at least the same cost plane by plane.

But the constraint on W is only that it maps the whole source subspace onto the whole target subspace. It does not require W to match each source principal vector with its canonical target partner. If the two angles coincide, the source and target carry internal rotational freedoms that can be coupled.

Those freedoms allow an orthogonal W whose rotation is concentrated into a single different plane, while its action on another two-plane is the identity. The two subspaces still have the prescribed principal angles. The eigenphases of W, and therefore the singular values of identity minus W, can be very different from those of D.

The trace norm is especially sensitive to this redistribution because it adds displacement singular values linearly. Rotating two planes a little and rotating one plane more can have different trace costs, even if both transformations carry the same subspace to its target.

## Compare with Proposition four point three

Why does the squared theorem not prohibit this? Consider two lists. The direct rotation may have four equal displacement singular values a. A competing orthogonal map may have two larger singular values b and two zeros.

For the positive squares, the lists are four copies of a squared versus two copies of b squared and two zeros. It is possible that every cumulative sum for the squared direct list is no larger than the corresponding cumulative sum for the squared competitor list, while the total **unsquared** direct sum four a is larger than the competitor's two b.

There is no contradiction. A majorization relation between squared lists does not automatically imply the same relation between the unsquared lists. The square-root function is concave, and it reacts differently to concentrations and spreading.

A numerical toy example makes the logical point. Compare four values each equal to point seven five with the list one point five, one point five, zero, zero. Both unsquared totals equal three, while the sum of squares is larger for the concentrated list. Shift the common small value slightly upward and the unsquared ordering reverses while the squared prefix ordering can still hold. The actual four-dimensional construction makes this exact using trigonometric values.

## A universal lower bound that remains true

There is, nevertheless, a lower bound on every full transport. Let P and Q be the source and target orthogonal projections. If W transports U to V, then Q equals W P W adjoint.

Introduce the reflections J-P equal two P minus identity and J-Q equal two Q minus identity. Their difference is two times P minus Q. The conjugacy condition says J-Q W equals W J-P.

Rearrange this identity. The difference of the two reflections, multiplied by W, is a commutator involving identity minus W and a reflection. By the triangle inequality and unitary invariance, the norm of that commutator is at most twice the norm of identity minus W.

Since the reflection difference is twice the projection difference, we conclude N of P minus Q is at most N of identity minus W for every unitarily invariant norm N.

This lower bound survives without a small-angle assumption. It applies over real and complex scalars and to every admissible transporter. It does **not** say that the canonical direct rotation attains the lower bound. Indeed, in the forthcoming example a noncanonical competitor does attain it in trace norm, while the direct rotation does not.

## How to test the printed claim

A universal minimizing statement must survive one explicit admissible competitor and one valid unitarily invariant norm. We can therefore choose trace norm, which is the sum of singular values.

The simplest potential counterexample should have enough dimensions to mix at least two principal planes. Four real dimensions suffice. We will take two equal acute principal angles. Then we will write a concrete orthogonal competitor, compute its action on the source plane, verify the resulting principal angles, and compute both displacement singular-value lists.

This is stronger than merely observing that the old proof has a gap. It produces a direct numerical contradiction to the stated inequality and can be expressed as a formal theorem asserting the negation of the printed proposition.

## Close

The sixty-degree threshold is correct for the standard two-dimensional real comparison. Proposition four point one remains valid for restricted displacement, and Proposition four point three remains valid for positive squared displacement. Neither theorem authorizes the universal unsquared ambient conclusion in higher dimension.

The source of the failure is extra freedom in the full orthogonal transport fiber, especially the freedom to mix repeated principal-angle directions. Our next lecture will calculate the four-dimensional witness completely, with no reliance on a drawing or a numerical optimizer.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

The printed real claim is a universal inequality for \(N(I-D)\) over every unitarily invariant norm and every orthogonal \(W\) mapping \(U\) to \(V\) when \(\theta_{\max}\le\pi/3\). The repository represents it as a proposition-valued definition and proves its negation. The planar candidates have singular values \((2\sin(\theta/2),2\sin(\theta/2))\) and \((2,0)\). Their all-gauge weak-majorization threshold is \(\theta\le\pi/3\), but this planar classification does not extend to arbitrary four-dimensional transporters.

For all admissible \(W\), \(N(P_U-P_V)\le N(I-W)\). This is a general lower bound, not an optimality assertion for \(D\).

## Exact Lean declaration excerpts

**`example4_1_directRotation_uiNorm_minimal_of_le_pi_div_three`.** This is the **two-dimensional Example 4.1 model**, with a Boolean choice between direct and reflecting transporter. It does not assert arbitrary-dimensional minimality.

`DavisKahan/Sources/DavisKahan1970/Section4LowDimensional.lean` — `example4_1_directRotation_uiNorm_minimal_of_le_pi_div_three` (exact declaration header; proof body omitted):

```lean
theorem example4_1_directRotation_uiNorm_minimal_of_le_pi_div_three
    {theta : ℝ} (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2)
    (hθ : theta ≤ Real.pi / 3)
    (flip : Bool)
    (N : UnitarilyInvariantSeminorm ℝ RealPlane RealPlane) :
    N (LinearMap.id - example41DirectRotation theta) ≤
      N (LinearMap.id - example4_1_competitor theta flip) :=
```

**`DavisKahanProposition4_4_Finite`.** This is the proposition-valued **false** printed assertion. It universally quantifies over real finite-dimensional spaces, acute pairs below `π/3`, transporters, and unitarily invariant seminorms.

`DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean` — `DavisKahanProposition4_4_Finite` (exact declaration header; proof body omitted):

```lean
def DavisKahanProposition4_4_Finite : Prop :=
```

**`projectionDifference_uiNorm_le_displacement`.** For every admissible transporter and invariant seminorm, projection difference is a lower bound for **full** displacement with no small-angle assumption.

`DavisKahan/FiniteDimensional/DirectRotation/ProjectionDisplacement.lean` — `projectionDifference_uiNorm_le_displacement` (exact declaration header; proof body omitted):

```lean
theorem projectionDifference_uiNorm_le_displacement
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N (U.starProjection.toLinearMap - V.starProjection.toLinearMap) ≤ N (LinearMap.id -
        W.toLinearMap) :=
```

