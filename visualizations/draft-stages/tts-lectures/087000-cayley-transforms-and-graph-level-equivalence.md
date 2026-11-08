# 087000 — Cayley transforms and graph-level equivalence

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `014000` unitary operators, `083000` graphs, `086000` resolvents. **Next:** `088000` unbounded spectral theorem.

<!-- BEGIN SPOKEN LECTURE -->

# Turning an unbounded self-adjoint operator into a unitary

An unbounded self-adjoint operator has a difficult domain, but we have just shown that its nonreal resolvents are bounded everywhere-defined maps. The Cayley transform uses one of those resolvents to build a unitary operator.

The important point is that this construction retains the information needed to recover the original graph. We will prove both directions.

## Construct the transform

Let A be self-adjoint on a dense domain D in a complex Hilbert space. Choose the imaginary unit, i. The operators A plus i and A minus i both map D bijectively onto H, by self-adjointness and the resolvent bound at imaginary spectral parameters.

Define U by first applying the bounded inverse of A plus i, then applying A minus i. At first this looks dangerous: A minus i is unbounded. But the inverse of A plus i sends every input into D, so the composition is legally defined on all of H.

Algebra simplifies it. Since A minus i equals A plus i minus two i, we get U equals the identity minus two i times the resolvent at negative i. Both terms are bounded. Thus U is a bounded everywhere-defined operator.

Take a domain vector x. Because A is symmetric, the inner product of A x with x is real. Expanding the squared lengths shows that A plus i applied to x and A minus i applied to x have equal length.

Write any vector y in H as A plus i applied to x; we can do so by surjectivity. Then U y equals A minus i applied to x. The equality of lengths says U preserves the length of every y.

To see that U is onto, start with an arbitrary output v and solve A minus i applied to x equals v. Then y equals A plus i applied to x satisfies U y equals v. So U is a surjective isometry, which means U is unitary.

## Why the point one is special

Suppose U y equals y. Write y as A plus i applied to x. The equality says A minus i applied to x equals A plus i applied to x. Subtracting gives two i times x equals zero. Therefore x, and then y, are zero.

So U has no nonzero fixed vector. In spectral language, one is not an eigenvalue of U.

But one may still belong to the spectrum of U. For an unbounded A, high spectral values of A are carried by the scalar Cayley transformation close to one. A sequence of approximate eigenvectors can therefore have Cayley eigenvalues approaching one, without any vector being fixed exactly.

This distinction is essential. Saying one is not an eigenvalue is weaker than saying U minus the identity has a bounded inverse.

## Recover the domain from the unitary

Compute one minus U. From the formula above it equals two i times the inverse of A plus i.

The range of that resolvent is exactly D, since A plus i is a bijection from D onto H. Multiplying by the nonzero scalar two i does not change the range.

We have proved a concrete identity: the domain of A is the range of the bounded operator one minus U.

This is how the domain is encoded by a bounded unitary. The map one minus U is bounded and defined everywhere, but it need not be onto H. Its image is the proper dense domain of A.

Now take x in that range, so x equals one minus U applied to some y. The preimage y is unique because U has no nonzero fixed vector. We can define A x using y: it equals i times one plus U applied to y.

Why is that the original A? If we choose y equal to A plus i applied to a domain vector v, then one minus U applied to y equals two i times v, and i times one plus U applied to y equals two i times A v. The two sides scale together. So the recovery formula agrees with A on its full domain.

The recovery formula is often written as i times one plus U divided by one minus U. The division is symbolic shorthand. The inverse of one minus U is defined only on its range, and that range is exactly where the recovered unbounded operator is defined.

## The converse correspondence

Now begin instead with a unitary U having no nonzero fixed vector. Set D equal to the range of one minus U. This range is dense: if z is orthogonal to it, then the adjoint of one minus U annihilates z, meaning U star z equals z. Applying U shows U z equals z, so z is zero.

Define A on this dense range by A applied to one minus U of y equals i times one plus U of y. Uniqueness of y makes the definition unambiguous.

One can verify symmetry by expanding inner products and using U star U equals the identity. More decisively, the formulas for A plus i and A minus i show that both shifts are onto H. That fact forces the adjoint domain to coincide with the original domain: any adjoint-domain vector orthogonal to one of the shifts must vanish, and the resolvent construction supplies the inverse.

Thus A is self-adjoint. The Cayley transform of this recovered A is the original U.

We have a correspondence between self-adjoint operators and unitary operators without fixed vectors, with proper attention to domains.

## The scalar geometry

For a real scalar lambda, the Cayley symbol is lambda minus i divided by lambda plus i. Its magnitude is one because the numerator and denominator have equal absolute value. As lambda ranges over the real line, the symbol travels along the unit circle, never reaching one at a finite lambda.

The inverse relation recovers lambda as i times one plus w divided by one minus w. This is real whenever w lies on the unit circle and differs from one.

The point one represents the spectral behavior near arbitrarily large absolute values. That is why the Cayley transform is useful for unbounded spectral theory: it compactifies the real spectral parameter onto a circle, at the price of singling out one point.

## A diagonal Cayley example

For the diagonal operator with eigenvalues one, two, three, and so on, the basis vector e N is also an eigenvector of U. Its Cayley eigenvalue is N minus i divided by N plus i. Every such number lies on the unit circle, and none equals one. But as N grows, the ratio approaches one.

So one belongs to the spectrum of U as a limit point even though it has no eigenvector. The operator one minus U is injective, but its inverse cannot be bounded on all of H. If it were, the diagonal values of that inverse would remain uniformly bounded, whereas their magnitudes grow with N. That is exactly how the unboundedness of A is remembered by its bounded Cayley transform.

## Compatibility with spectral measures

The spectral theorem for bounded unitary operators provides a projection-valued measure on the unit circle. By pushing that measure back through the inverse Cayley coordinate, we obtain a projection-valued measure on the real line for A.

The construction must handle the exceptional circle point one. Because the Cayley unitary has no fixed vectors, the spectral projection of that singleton vanishes even if one belongs to the continuous spectrum. Thus no nonzero vector mass is lost when the real-line measure is recovered.

The real-line spectral measure then defines Borel functions of the self-adjoint operator. When a Borel function grows without bound, its operator is generally unbounded too and must carry an explicitly defined domain.

The practical lesson is that a bounded unitary can encode a self-adjoint operator's full graph. To recover the original operator, however, we must recover its domain as well as its values.

An unbounded self-adjoint operator can be reconstructed from its spectral measure only with a domain restriction: for each vector, the squared spectral variable must be integrable against its scalar spectral measure.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Use \(U=(A-iI)(A+iI)^{-1}=I-2i(A+iI)^{-1}\). This bounded operator is unitary, \(\ker(I-U)=0\), and \(D(A)=\operatorname{Ran}(I-U)\). Recover the graph by \(A((I-U)y)=i(I+U)y\). The source's `LinearPMap.resolvent A (-i)` is the inverse of \((-i)I-A\); hence its displayed identity \(I-U=-2iR(-i)\) agrees with the lecture's \(I-U=2i(A+iI)^{-1}\). The Cayley spectral point \(1\) can belong to continuous spectrum despite having no eigenvectors.

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `one_sub_cayley_apply`:

```lean
theorem one_sub_cayley_apply (ξ : H) :
    ((1 : H →L[ℂ] H) - A.cayley) ξ
      = -((2 * Complex.I) • resolvent A (-Complex.I) ξ) := by
```

This is the exact convention-sensitive Cayley/resolvent identity.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `injective_one_sub_cayley`:

```lean
theorem injective_one_sub_cayley :
    Function.Injective ((1 : H →L[ℂ] H) - A.cayley) := by
```

It proves the Cayley transform has no nonzero fixed vector.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` — `spectralPVM_def`:

```lean
theorem spectralPVM_def :
    spectralPVM hA
      = BorelCalculus.toProjValMeasure (hA.isStarNormal_cayley)
          (measurable_cayleyInv A) := (rfl)
```

The unbounded self-adjoint spectral measure is recovered by relabeling the Borel calculus of the Cayley unitary.

**Scope:** The full converse Cayley correspondence and graph-reconstruction calculations are established in the lecture; the displayed declarations are selected bridge results from the actual project source. These excerpts are from the supplied source snapshot and are not new compiled Lean code. Reusable `ForTauCeti` constructions have explicit DKPS donor/origin notes; the current file namespace does not imply an external origin.
