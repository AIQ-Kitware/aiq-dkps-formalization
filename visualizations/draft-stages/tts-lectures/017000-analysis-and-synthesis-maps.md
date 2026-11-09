# Analysis and synthesis maps

<!-- BEGIN SPOKEN LECTURE -->

A Hilbert space can be decomposed into perpendicular subspaces, but another way to describe geometry is to choose a family of vectors. Such a family produces maps between coefficient lists and the underlying space. The central question is what those maps preserve and what their compositions reveal.

We can build new vectors from it. We can measure other vectors against it. And we can compare what those two operations do when performed one after the other.

The names for the first two constructions are *synthesis* and *analysis*. They are simple enough to calculate by hand, but they become important machinery for principal angles, Rayleigh–Ritz methods, singular-value theory, and the Davis–Kahan perturbation theory.

## A collection of vectors as a machine

Start in the ordinary plane. Take two vectors: the first points one unit to the right, and the second points one unit right and one unit up. We will call them v one and v two.

If you give me two coefficients, say a and b, I can build the vector a times v one plus b times v two. With our chosen vectors, that output has first coordinate a plus b, and second coordinate b.

You have supplied numbers; I have assembled a vector. This is *synthesis*.

The synthesis map takes a coefficient list and produces a vector in the ambient space. Its definition is always the same: multiply each selected vector by its coefficient, then add the results.

For a list of three vectors, there are three coefficients. For a list of a hundred vectors, there are a hundred. The coefficient space is a space of lists of numbers. We do not need the selected vectors to be perpendicular, independent, or normalized in order to define synthesis.

Notice that synthesis is linear. If we add two coefficient lists before synthesizing, the result is the sum of the two synthesized vectors. And scaling the coefficient list scales the output by the same amount.

This is one reason mathematicians prefer a map rather than a sequence of informal coordinate rules. Once we know synthesis is a linear operator, we can investigate its kernel, image, adjoint, and norm.

## The kernel tells us about redundancy

What happens if the selected vectors contain redundant information?

Take two copies of the same unit vector pointing to the right. Synthesis with coefficients a and b gives the horizontal vector with length determined by a plus b. The coefficients one and negative one synthesize to zero.

The coefficient list is not zero, but its synthesized vector is zero. That means synthesis has a nontrivial kernel.

So linear dependence among our selected vectors is exactly the possibility of synthesizing zero from a nonzero coefficient list.

When a family is linearly independent, synthesis is one-to-one: different coefficient lists make different vectors. When the family spans the whole ambient space, synthesis is onto. When both properties hold, we have a basis and synthesis is a linear isomorphism between the coefficient space and the ambient space.

But a useful family need not be a basis. We may deliberately use more vectors than the dimension of the space. Then coefficients are redundant, but the collection can still be useful for measurement and reconstruction.

## Turn the arrows around: analysis

Now imagine that instead of coefficients, you are given an ambient vector x. For each selected vector v, you can measure the inner product of v with x. Collect those measurements into a list.

That list is the output of *analysis*.

For our two vectors in the plane, let x have coordinates p and q. The inner product with v one is p. The inner product with v two is p plus q. So analysis returns the coefficient-like list p, p plus q.

I said *coefficient-like* for a reason. Analysis outputs measurements. They are not always the actual coefficients that synthesize x.

Try x equal to the vector pointing one unit right. Analysis gives one, one. If you now synthesize those numbers using v one and v two, you obtain two units right and one unit up. You do not recover x.

This is an easy mistake to make if your only experience is with orthonormal bases. For an orthonormal basis, inner products really are the reconstruction coefficients. For a nonorthogonal family, analysis and synthesis still make sense, but one does not automatically undo the other.

## Why analysis is the adjoint of synthesis

There is a deeper relationship between these maps. Let S denote synthesis and A denote analysis. We can show that A is the adjoint of S.

Here is the calculation in words. Take a coefficient list c and an ambient vector x. First synthesize c, and take its inner product with x. Because synthesis makes a sum of coefficient-weighted vectors, linearity of the inner product lets us expand the result into a sum of coefficient times inner-product measurements.

But that sum is exactly the inner product of the coefficient list c with the list of measurements produced by A of x. So measuring the synthesized vector against x is equivalent to measuring the coefficient list against the analyzed vector.

That is the defining adjoint identity. Therefore synthesis star equals analysis, and analysis star equals synthesis.

In the real case the analysis map uses ordinary transposition. Over complex scalars, the conjugates and the linear argument of the inner product must be placed consistently: taking the inner product of v with x is linear in x under our convention, and the synthesis and analysis maps are adjoints.

Think of this as a reversible change in the *direction of measurement*, not necessarily a reversible reconstruction. Adjoint does not mean inverse.

## A special case: an orthonormal family

Now suppose the selected vectors are mutually perpendicular and each has length one. Such a family is called orthonormal.

If we synthesize a coefficient list, its squared length is the sum of the squared magnitudes of the coefficients. Why? When we expand the squared length of the sum, all cross terms vanish because distinct selected vectors are perpendicular. Each diagonal term contributes one coefficient magnitude squared.

So synthesis preserves lengths on coefficient space. It is an isometry.

If we analyze a synthesized vector, the measurement against a particular selected vector returns exactly that vector's coefficient. All the other vectors have zero inner product with it. Thus analysis after synthesis is the identity on coefficient space.

But synthesis after analysis need not be the identity on the whole Hilbert space. If the orthonormal family spans only a proper subspace, synthesis after analysis keeps the component in that span and discards everything perpendicular to it.

For example, choose only the horizontal unit vector in the plane. Analysis measures the horizontal coordinate. Synthesis rebuilds the horizontal part. The vertical coordinate disappears. So synthesis after analysis is the orthogonal projection onto the horizontal axis.

If the orthonormal family is a full orthonormal basis, including the appropriate completeness condition in an infinite-dimensional space, then synthesis after analysis recovers every vector as well.

That last sentence contains an important distinction. A finite orthonormal list behaves through finite sums. Infinite orthonormal families require convergence of their expansions. We will develop those convergence issues separately rather than hiding them in the word basis.

## Two orders of composition

Return to an arbitrary finite family. There are two ways to put analysis and synthesis together.

First, start with a vector, analyze it, and synthesize those measurements. This map begins and ends in the ambient Hilbert space. We call it the *frame operator*. It is synthesis after analysis.

Second, start with coefficients, synthesize a vector, and then analyze that vector. This map begins and ends in coefficient space. We call it the *Gram operator*. It is analysis after synthesis.

The maps go in opposite directions, so the two compositions live on different spaces. They are not interchangeable.

Take the two vectors we started with. Analysis of x with coordinates p and q gives p and p plus q. Synthesizing those measurements gives the vector with coordinates two p plus q, and p plus q. That is the frame operator acting on x.

Now start instead with coefficients a and b. Synthesis produces coordinates a plus b and b. Analyzing that vector gives coefficients a plus b, and a plus two b. That is the Gram operator acting on the coefficient list.

Their numerical matrices happen to be closely related in this example, but their input and output spaces are conceptually different. The Gram operator asks how the chosen vectors relate to one another. The frame operator asks how measurements against the family combine to act on an ambient vector.


## Positivity without eigenvalues

There is already an important theorem we can prove, even before learning the full spectral theorem.

Take an ambient vector x. Form the inner product of x with the frame operator applied to x. Because the frame operator is synthesis after analysis, and synthesis is the adjoint of analysis, we can move the synthesis step across the inner product. The result is the squared length of A of x.

That squared length cannot be negative. So the frame operator has a nonnegative quadratic form. We call such an operator positive semidefinite.

The same argument applies in coefficient space. The inner product of a coefficient list with its image under the Gram operator equals the squared length of the synthesized vector. Again it cannot be negative.

We did not need to diagonalize either operator. Their positivity follows directly from their construction as an operator followed by its adjoint.

## Reconstruction

There are three ideas worth reconstructing. First, explain why a nonzero coefficient list synthesizing to zero is exactly a linear-dependence relation. Second, prove from the inner-product identity that analysis is the adjoint of synthesis. Third, distinguish analysis after synthesis from synthesis after analysis, and say which space each composition acts on.


<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical statements and Lean correspondence (display only)

For a finite family \(v_i\in H\), with coefficient Hilbert space \(\mathbb K^I\) and inner product linear in the second argument, define

\[
S_v(c)=\sum_{i\in I}c_i v_i,\qquad
A_v(x)=(\langle v_i,x\rangle)_{i\in I}.
\]

Then \(A_v=S_v^*\), \(S_v=A_v^*\), the ambient frame operator is \(F_v=S_vA_v\), and the coefficient-space Gram operator is \(G_v=A_vS_v\). Consequently
\[
\langle x,F_vx\rangle=\|A_vx\|^2\ge0,\qquad
\langle c,G_vc\rangle=\|S_vc\|^2\ge0.
\]

**Lean bridge.** These are the original DKPS-staged definitions from `ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean`:

```lean
/-- Analysis map of a finite family, with coordinate `i` equal to `⟪v i, x⟫`.  The
inner-product argument order makes this map `𝕜`-linear. -/
noncomputable def finiteAnalysis (v : ι → E) : E →ₗ[𝕜] EuclideanSpace 𝕜 ι :=
  (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).symm.toLinearMap ∘ₗ
    LinearMap.pi fun i => (innerSL 𝕜 (v i)).toLinearMap

/-- Synthesis map `c ↦ ∑ i, c i • v i` of a finite family. -/
noncomputable def finiteSynthesis (v : ι → E) : EuclideanSpace 𝕜 ι →ₗ[𝕜] E where
  toFun c := ∑ i, c i • v i
  map_add' a b := by
    simp only [PiLp.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' r a := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

/-- Analysis and synthesis are adjoint to each other. -/
theorem adjoint_finiteAnalysis (v : ι → E) :
    (finiteAnalysis 𝕜 v).adjoint = finiteSynthesis 𝕜 v := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro c x
  rw [finiteSynthesis_apply, sum_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, finiteAnalysis_apply, RCLike.inner_apply]
  ring
```

`EuclideanSpace 𝕜 ι` represents the finite coefficient Hilbert space; `E →ₗ[𝕜] ...` and the reverse map distinguish the two directions. The theorem proves that the constructions are adjoints, rather than assuming they are inverses. This module identifies its original DKPS donor path and commit, and its staged `TauCeti` namespace preserves that ancestry. Excerpts were checked against the uploaded source snapshot; no new Lean compilation was performed.
