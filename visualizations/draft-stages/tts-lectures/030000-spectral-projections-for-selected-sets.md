# Spectral projections: selecting whole pieces of an operator

<!-- BEGIN SPOKEN LECTURE -->

Individual eigenvalues of a self-adjoint matrix can be ordered and compared using Rayleigh quotients and min-max characterizations. But many perturbation questions concern an entire selected collection of eigendirections rather than any one eigenvector.

But the Davis–Kahan theory that motivates this course is often not interested in one eigenvector at a time. It asks how a *subspace* associated with a group of eigenvalues behaves. To prepare for that question, we need a way to say: keep the part of a vector associated with these eigenvalues, and discard everything else.

The mathematical object that does exactly this is a spectral projection.

In finite dimensions, a spectral projection is determined by a selected set of eigenvalues; it cannot be defined by an arbitrary collection of vectors without checking that they form an invariant spectral subspace.

## Selecting frequencies in a simple analogy

Imagine a musical chord. It contains several pitches mixed together. If we could separate the chord into its pitch components, we might choose to keep only the notes above a certain frequency.

For a self-adjoint matrix, the finite spectral theorem gives an exact decomposition of every vector into orthogonal components belonging to distinct eigenvalues. We can select some of those components and suppress the others.

The analogy is imperfect: an eigenvalue need not be a frequency, and an operator need not describe sound. But the operation of selecting components is precisely the same kind of bookkeeping.

Let's build it from the eigenbasis rather than starting with a formula to memorize.

## The projector for one eigenspace

Suppose A is self-adjoint. Pick one of its eigenvalues, say lambda. All the vectors that A multiplies by lambda form the corresponding eigenspace.

Because the space is finite-dimensional, there is an orthogonal projection onto that eigenspace. Call it P lambda. Applying P lambda to a vector keeps the component in that eigenspace and removes all perpendicular components.

If we apply P lambda twice, the second application changes nothing. That is the defining behavior of a projection. If we take its adjoint, we get the same operator, because this is an *orthogonal* projection.

What happens if we project onto one eigenspace, then onto an eigenspace for a different eigenvalue? The result is zero. Distinct eigenspaces of a self-adjoint operator are perpendicular, so no nonzero component can survive both selections.

Finally, add the projections over all distinct eigenvalues. Every vector is the sum of all its spectral components, so that sum is the identity operator.

This gives us a collection of mutually compatible selectors, one for each distinct eigenvalue.

## Selecting a set of eigenvalues

Now choose any set S of real numbers. It might be a finite list, a closed interval, an open interval, or all numbers above a threshold.

For each eigenvalue belonging to S, keep its spectral projection. Add those projections together. Ignore the eigenvalues outside S. The resulting operator is the spectral projection of A onto S.

The set S itself can contain numbers that are not eigenvalues. Those extra numbers have no effect: there is no eigenspace component for them to select.

To calculate this projection on a vector, decompose the vector into eigenspace components, keep exactly the ones whose eigenvalues lie in S, and add them back together.

Because the selected eigenspaces are mutually perpendicular, the resulting operator is again an orthogonal projection. The subspace onto which it projects is the direct sum of the selected eigenspaces. We call that a spectral subspace.

The projection is not an arbitrary choice of coordinates. It is determined by the operator and the selected set of eigenvalues.

## A calculation we can hear

Consider the symmetric two-by-two matrix with rows two, one and one, two. We have used it before. Its eigenvalues are three and one. Its eigenvectors lie along the lines one, one and one, negative one.

Suppose S contains all real numbers greater than two. Only the eigenvalue three is selected. Projection onto its normalized eigenvector produces a matrix with one-half in each of its four entries.

Apply that projection to the vector with coordinates four and zero. We get the vector two, two. The component along the diagonal line is preserved; the perpendicular component is removed.

Now select the interval from zero through two instead. We keep the eigenvalue one, so the selected projector has one-half on the diagonal and negative one-half off the diagonal. Applied to four, zero, it returns two, negative two.

Add these two projections. We get the identity. Applied to four, zero, their outputs add to four, zero. We have split a vector into two perpendicular spectral pieces.

Notice that a selection interval can be broad. It does not need to contain exactly one eigenvalue. If we select all positive eigenvalues of this particular matrix, both eigenspaces survive and the projection is the identity.

## Why endpoints matter

Now imagine a selection rule that keeps eigenvalues greater than or equal to one. Our matrix has an eigenvalue exactly equal to one, so it is included. The projector is the identity.

Change just one word: keep eigenvalues *strictly* greater than one. Now the eigenspace for one is excluded, and only the eigenspace for three remains.

The difference between a closed and an open interval can therefore change the selected spectral subspace immediately when an eigenvalue lies on the boundary.

If we move a threshold through a region containing no eigenvalues, the projection does not change at all. If it passes an eigenvalue, the projection gains or loses the entire eigenspace associated with that value.

The selection rule is defined for a fixed self-adjoint matrix. Stability under perturbations is a separate problem, requiring spectral separation assumptions.

## What if an eigenvalue repeats?

Suppose A has diagonal entries four, four, and one. The eigenspace for four is a plane, and the eigenspace for one is a line perpendicular to it.

Selecting eigenvalue four keeps the *entire plane*. The spectral projection has diagonal entries one, one, and zero.

Could we instead select just one of the two coordinate axes in that plane? We could certainly project onto that line. Since A acts as four times the identity on the whole plane, the line projection would even commute with A.

But it would not be a spectral projection defined by a set of eigenvalues. The selection rule cannot distinguish two directions that carry exactly the same eigenvalue. It either includes the full eigenspace for four or excludes it.

This is the difference between a general invariant subspace and a subspace determined solely by spectral selection. It also explains why spectral projections do not depend on which orthonormal basis we choose inside a repeated eigenspace.

## Why a spectral projection commutes with the operator

Take any vector x. Split it into its selected spectral components and its unselected spectral components.

If we first apply the projection and then apply A, each selected component gets multiplied by its eigenvalue.

If we first apply A and then project, A multiplies *every* spectral component by its eigenvalue, but the projection removes the unselected ones afterward.

The same selected components survive with the same multipliers in either order. Therefore the spectral projection commutes with A.

That means its range is invariant under A, and so is its perpendicular complement. By definition, a spectral subspace is a *reducing* subspace.

Conversely, as the repeated-eigenvalue example shows, a reducing subspace need not arise by selecting whole eigenvalues. Commutation is a necessary property of spectral projections, but not a complete characterization of those particular selectors.

## Combining selections

The selection rules obey simple algebra. Selecting S and then selecting T is the same as selecting their intersection, because a component survives both steps exactly when its eigenvalue belongs to both sets.

If S and T are disjoint, their selected subspaces are orthogonal and the projection for their union is the sum of their projections.

Selecting the complement of S keeps everything that S discarded, so its projection is the identity minus the projection for S.

These identities are useful because they let us manipulate spectral regions using operators, without returning to coordinates after every step.

## Spectral selection as an operator function

Spectral selection is an example of applying a function to a self-adjoint operator. The indicator of a set S takes the value one on S and zero outside S. Applied to a finite-dimensional self-adjoint matrix through its eigenvalue decomposition, this indicator produces the corresponding spectral projection.

For an infinite-dimensional self-adjoint operator, the spectrum need not consist of isolated eigenvalues. A projection-valued spectral measure gives the correct extension of the indicator construction to that setting; the finite eigenbasis argument alone does not establish it.

For now, try reconstructing the two-by-two example. Explain why the projectors for three and one add to the identity. Then prove that any selected spectral projection commutes with A. Finally, explain why selecting one line in a repeated eigenspace is not the same as selecting an eigenvalue.

A selected spectral subspace is the range of a projection defined by a spectral set. Its projector commutes with the self-adjoint operator, and repeated eigenvalues must be selected together when the selection is made solely by eigenvalue.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical facts and Lean correspondence (display only)

Let \(A=A^*\) act on a finite-dimensional real or complex Hilbert space, with distinct eigenvalues \(\Lambda\) and orthogonal eigenspace projections \(P_\lambda\). For any \(S\subseteq\mathbb R\), define

\[
P_A(S)=\sum_{\lambda\in\Lambda\cap S}P_\lambda,\qquad
\operatorname{ran}P_A(S)=\bigoplus_{\lambda\in\Lambda\cap S}\ker(A-\lambda I).
\]

Then \(P_A(S)^2=P_A(S)=P_A(S)^*\), \(P_A(S)A=AP_A(S)\), and

\[
P_A(S\cap T)=P_A(S)P_A(T),\qquad
P_A(S^c)=I-P_A(S).
\]

For disjoint sets, \(P_A(S\cup T)=P_A(S)+P_A(T)\). A repeated eigenvalue is selected with its **whole** eigenspace. A commuting orthogonal projection need not be of the form \(P_A(S)\) when there is a repeated eigenvalue.

**Lean bridge.** The DKPS-local module `ForTauCeti/Analysis/Matrix/SpectralProjection.lean` supplies a threshold projector and its first two structural facts, in the pinned repository snapshot:

```lean
noncomputable def spectralProjectionIci (c : ℝ) (A : Matrix (Fin n) (Fin n) 𝕜)
    (_hA : A.IsHermitian) : Matrix (Fin n) (Fin n) 𝕜 :=
  cfc (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) A

/-- The matrix threshold indicator defines a self-adjoint projection. -/
theorem isHermitian_spectralProjectionIci (c : ℝ)
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    (spectralProjectionIci c A hA).IsHermitian := by
  exact (cfc_predicate (Set.indicator (Set.Ici c) (1 : ℝ → ℝ)) A).isHermitian
```

`Set.Ici c` is the **closed** interval \([c,\infty)\); a boundary eigenvalue equal to \(c\) is selected. `Set.indicator` makes the zero-or-one selection function, and `cfc` is continuous functional calculus as used for finite Hermitian matrix spectra. The full functional-calculus construction is taught later, in `032000`; here the code illustrates how the set-based selector is encoded. The same module proves `isIdempotentElem_spectralProjectionIci`, giving the idempotence property, and contains the eigenvector-column selection theorem. This displayed excerpt is copied from an existing DKPS-local file; it does not assert that the more general infinite-dimensional PVM construction has been proved in this lecture.
