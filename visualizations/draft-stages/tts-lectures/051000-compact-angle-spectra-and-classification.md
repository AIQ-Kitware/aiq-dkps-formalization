# 051000 — Compact angle spectra and classification

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `026000` finite spectral theorem; `035000` operator modulus; `036000` singular-value decomposition; `042000` principal angles; `045000` Halmos decomposition; `046000` positive cosine operators; `050000` defect matching. **Next:** min–max principles for singular values.

<!-- BEGIN SPOKEN LECTURE -->

# Can a list of angles classify two subspaces?

When we studied two finite-dimensional subspaces, principal angles gave a remarkably efficient description of how they meet. Find their cross-Gram matrix, take its singular values, and turn each singular value into an angle. Record the dimensions of the common directions and the perpendicular pieces, and we can reconstruct the relative geometry in orthogonal blocks.

But we are working toward results about Hilbert spaces that may be infinite-dimensional. A bounded self-adjoint operator on an infinite-dimensional space need not have an eigenvector basis. So we should not assume that every pair of subspaces comes with a complete list of principal angles.

Today's question is precise: under what hypotheses does a numerical angle list give a complete classification? And what mathematical information is missing when the spectrum is continuous?

## What exactly are we classifying?

Imagine two ordered pairs of closed subspaces. One pair lives in a Hilbert space H, and the other pair lives in a possibly different Hilbert space G.

We will call the pairs equivalent if there is a linear isometric equivalence from H onto G that carries the first source subspace onto the second source subspace and, simultaneously, carries the first target onto the second target.

The word simultaneously is essential. It would be easy to match the source spaces separately and the target spaces separately. The challenge is to find one ambient unitary that respects both choices at once.

Any such unitary preserves inner products, orthogonality, and projections. In particular it preserves the four elementary Halmos pieces: the common part, the source defect, the target defect, and the exterior part.

Therefore the Hilbert-space dimensions of those four pieces are invariants. If they differ, the pairs cannot be equivalent, even if many principal angles happen to agree.

The remaining information lives in the generic part, where neither pair has a common, perpendicular, or exterior direction.

## The generic cosine block

Focus on the part of the generic space that lies in the source subspace U. On that space consider the operator obtained by projecting into V and then back into U.

This is the compression of P U times P V times P U. Call it A. Its quadratic form at a source vector x is the squared length of the projection of x onto V. Therefore A is positive, and it cannot exceed the identity.

In finite dimensions, A has eigenvalues cosine squared theta, one for each generic principal angle theta. The common part would give eigenvalue one, and the source defect would give eigenvalue zero, but we have already separated those pieces. The generic block contains neither kind of exact endpoint vector.

We can also regard the source generic part as one half of the familiar cosine–sine construction. On it, the operator A and the associated sine operator determine the two projection matrices on the full generic space.

This is the key structural fact: after the four elementary pieces are removed, the unitary-equivalence class of A determines the generic relative geometry. Two pairs with isometrically matching four pieces and unitarily equivalent generic cosine operators can be reconstructed as equivalent pairs.

But an operator is more information than a list of eigenvalues. We need compactness to justify replacing that operator by numerical spectral data.

## Why compactness supplies eigenvectors

Recall what compactness means for a bounded operator: it sends every bounded sequence to a sequence with a convergent subsequence of images.

For a positive compact operator A, suppose A is nonzero. Its operator norm equals the maximum possible Rayleigh quotient. Choose unit vectors whose Rayleigh quotients approach that norm.

The unit ball of a Hilbert space is weakly sequentially compact. We can choose a weakly convergent subsequence. Compactness upgrades the images under A to strong convergence. This is enough to show that the maximum is attained by a unit vector. The stationary-point argument from our Rayleigh quotient lecture makes that vector an eigenvector, with eigenvalue equal to the norm.

Take its orthogonal complement. Self-adjointness makes that complement invariant, so we may repeat. We obtain orthogonal eigenvectors with nonnegative eigenvalues arranged in decreasing order.

Why must those eigenvalues tend to zero if infinitely many appear? If they stayed above a fixed positive number, the images of the orthonormal eigenvectors would stay a fixed distance apart. That contradicts compactness, because the original orthonormal sequence is bounded.

The only possible accumulation point of distinct nonzero eigenvalues is therefore zero. Each nonzero eigenspace is finite-dimensional for the same reason.

Finally, if a nonzero positive operator remained after removing all those eigenspaces, we could find yet another positive eigenvalue. That contradicts the construction. So the eigenvectors account for all of the nonzero action of A.

This is the compact positive spectral theorem. It is the reason numerical eigenvalue data can be complete here.

## The angle list and its multiplicities

Assume the generic cosine operator is compact. Its positive eigenvalues are numbers between zero and one. They represent cosine squared of the generic principal angles.

Suppose the same eigenvalue occurs on a three-dimensional eigenspace. That is one angle with multiplicity three. We must record that multiplicity, because three independent principal planes carry more geometric information than one.

It is often convenient to record a function: for each possible eigenvalue, give the dimension of its eigenspace. Equivalently, arrange the positive eigenvalues in decreasing order and repeat each according to its multiplicity.

The two representations carry the same data for a compact positive operator with zero kernel. In this generic setting the kernel is indeed zero; exact right-angle directions were removed as source and target defects.

There is an important subtlety. Zero may still belong to the spectrum as an accumulation point, without being an eigenvalue. A sequence of angles can approach ninety degrees even though there is no actual right-angle vector. We must distinguish that limiting spectral behavior from the finite or infinite dimension of an exact defect space.

## A diagonal infinite-dimensional example

Take a Hilbert space of square-summable sequences, with orthonormal basis indexed by the nonnegative integers. Define a cosine operator C that multiplies the coordinate with index n by one over n plus two.

Its eigenvalues are one half, one third, one fourth, and so on. The operator is compact, because its finite-coordinate truncations converge to it in operator norm.

Now define a sine operator S by taking the positive square root of identity minus C squared. Since C and S are diagonal, they commute, and their squares add to the identity.

On a doubled sequence space, take U to be the first coordinate copy. Construct V as the image of the isometric map sending x to the pair C x, S x. Each coordinate gives a principal plane. The angle in coordinate n has cosine one over n plus two.

All these angles are less than ninety degrees, but they approach ninety degrees. There is no exact crossed defect. The generic cosine-square operator has eigenvalues one quarter, one ninth, one sixteenth, and so on.

We can recover the pair's generic geometry from that sequence, including multiplicities. The accumulation at zero represents a limiting right angle, not an additional eigenvector.

Notice also that the projection gap is one in this example, although neither crossed defect contains a nonzero vector. This recovers our earlier distinction between intersection-based acuteness and a uniform gap.

## A continuous-spectrum example

Now replace the sequence space by the space of square-integrable functions on the interval from zero to one.

Let C multiply a function by its input coordinate t. Let S multiply by the square root of one minus t squared. Again, C squared plus S squared is the identity, and both operators are positive and commute.

Construct U and V in the doubled function space exactly as before: U is the first copy, and V consists of pairs C f, S f.

What are the eigenvectors of C? An eigenvector with eigenvalue lambda would be a nonzero square-integrable function supported where t equals lambda. But a single point has measure zero. So that function must be zero.

C has no eigenvectors at all. Neither does its square. Yet the geometry is nontrivial and varies continuously across the interval. The spectrum of C is the full interval from zero to one.

A list of eigenvalue multiplicities sees none of this. It would report zero eigenspace dimension for every lambda. So it cannot possibly classify the generic geometry.

The proper invariant in this noncompact setting is the unitary-equivalence class of the positive cosine operator, including its continuous spectral behavior. Full spectral-measure language belongs to later functional analysis, but we can already see why finite-style angle lists fail.

## The compact classification statement

We can now state a useful version of the classification theorem.

Consider two ordered pairs of closed subspaces. Suppose, for each pair, the ambient operator P U P V P U is compact. Then the associated generic cosine block is compact as well.

The pairs are unitarily equivalent as ordered pairs if and only if their four elementary Halmos summands are isometrically equivalent, and the generic cosine-square eigenvalues have matching multiplicities at every eigenvalue.

To see necessity, let an ambient unitary carry one pair to the other. It carries all four elementary pieces, and it intertwines the two cosine-square operators. Intertwining preserves eigenspaces and their dimensions.

For sufficiency, match the four elementary pieces using their given isometries. On the generic source halves, the compact spectral theorem lets us match orthonormal eigenbases eigenvalue by eigenvalue. That gives a unitary intertwining the generic cosine operators. The cosine–sine reconstruction then extends it to the other generic halves. Assemble the orthogonal pieces to obtain one ambient unitary carrying both subspaces together.

Compactness is the condition that makes the second half possible using just numbers.

## Reconstruction

First, explain why an ambient equivalence must preserve each of the four elementary Halmos parts.

Second, derive positivity of the generic compression of P U P V P U, and interpret each of its eigenvalues as cosine squared of a principal angle.

Third, reproduce the compactness argument showing that nonzero eigenvalues have finite multiplicity and can accumulate only at zero.

Finally, compare the diagonal sequence example with the multiplication-by-t example. Which one admits a complete numerical list, and why does the other not?

We have completed the classification foundations for two subspaces. Next we will return to singular values, starting with their own min–max characterization. That machinery will later let us measure perturbation and rotation using norms more refined than the operator norm.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For closed subspaces \(U,V\subseteq H\), the four Halmos elementary summands are
\[
U\cap V,\quad U\cap V^\perp,\quad U^\perp\cap V,\quad U^\perp\cap V^\perp.
\]
On the \(U\)-half of the orthogonal generic remainder, the positive contraction \(A\) is the compression of \(P_UP_VP_U\). Its nonzero eigenvalues are \(\cos^2\theta\), with each eigenspace dimension recording angle multiplicity. A compact positive \(A\) has an orthonormal eigenbasis for the closure of its range, with nonzero eigenvalues of finite multiplicity tending to zero if infinite. The generic block has \(\ker A=\{0\}\), but zero may still lie in its spectrum as a limit.

**Compact pair classification:** if each ambient \(P_UP_VP_U\) is compact, two ordered pairs are unitarily equivalent exactly when (i) their four elementary summands match isometrically and (ii) the dimensions of the generic cosine-square eigenspaces match for each eigenvalue. Without compactness, the numerical point spectrum need not determine the operator; a continuous spectral component must be retained through the operator-equivalence invariant.

**Lean bridge (source excerpts).** `DavisKahan/Geometry/Halmos/CompactClassification.lean` defines a compact angle eigenvalue list via singular values:

```lean
@[expose]
noncomputable def compactAngleEigenvalueList
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [CompleteSpace K] (A : K →L[𝕜] K) : ℕ → ℝ :=
  fun n => (A.singularValue n : ℝ)
```

For a positive compact operator, singular values equal its nonnegative eigenvalues with multiplicity. The key classification theorem in the same module uses a dimension function instead, and requires compactness of the **ambient** triple projection for both pairs:

```lean
theorem pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData
    (hc₁ : IsCompactOperator (U₁.starProjection ∘L V₁.starProjection ∘L U₁.starProjection))
    (hc₂ : IsCompactOperator (U₂.starProjection ∘L V₂.starProjection ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameCompactAngleData U₁ V₁ U₂ V₂ := by
```

The proposition `SameCompactAngleData` contains fields for `common`, `sourceDefect`, `targetDefect`, and `exterior`, each asserting a nonempty isometric equivalence, and an `angleMultiplicity` field asserting equal `finrank` of eigenspaces of `genericCosineBlock`. `DavisKahan/Geometry/Halmos/GenericReconstruction.lean` provides the generic cosine reconstruction; `DavisKahan/Geometry/Halmos/Classification.lean` establishes the necessity of the operator-based invariant.

In the diagonal example \(C e_n=(n+2)^{-1}e_n\), \(A=C^2\) is compact with eigenvalues \((n+2)^{-2}\). In the multiplication example on \(L^2(0,1)\), \((Cf)(t)=tf(t)\) has no eigenvectors, while its spectrum is \([0,1]\); a discrete eigenvalue list cannot recover this geometry.

**Reconstruction exercise:** prove \(\ker(C^2)=\{0\}\) for each example and show that the first cosine square is compact while the second is not. Explain why the first pair has no exact right-angle defect even though its principal angles approach \(\pi/2\).
