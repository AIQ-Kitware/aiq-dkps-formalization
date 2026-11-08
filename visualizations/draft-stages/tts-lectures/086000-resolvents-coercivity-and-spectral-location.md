# 086000 — Resolvents, coercivity, and spectral location

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `033000` positive forms, `081000` resolvent integrals, `084000` self-adjointness. **Next:** `087000` Cayley transforms.

<!-- BEGIN SPOKEN LECTURE -->

# Proving a shift has a bounded inverse

A resolvent turns a possibly unbounded operator into a bounded one. But that construction is legal only when the shifted operator is one-to-one, onto, and has an inverse defined on the entire Hilbert space.

Today we will prove these properties for nonreal shifts of a self-adjoint operator, then use coercivity to locate real intervals in the resolvent set. The same estimates will later control the spectral gaps in Davis–Kahan theory.

## What a resolvent has to accomplish

Let A be a densely defined self-adjoint operator with domain D in a complex Hilbert space. Choose a complex number z.

The shifted operator A minus z is defined on D. The statement that z belongs to the resolvent set means the shift maps D bijectively onto H and its inverse is a bounded, everywhere-defined operator from H back into H. The image of that inverse actually lies in D.

Its inverse is written as A minus z, all inverted. Some authors instead use z minus A inverted. The two conventions differ by a minus sign. The spectrum itself does not depend on that choice.

For a self-adjoint operator, all nonreal numbers lie in the resolvent set. We will prove this without pretending that A is a bounded matrix.

## A coercive estimate away from the real axis

Let z have nonzero imaginary part, and take a vector x in D. Expand the inner product of the shifted output with x.

Because A is symmetric, the inner product of A x with x is real. Its imaginary part vanishes. The imaginary part of the shift term is therefore the imaginary part of negative z times the squared length of x.

The magnitude of the imaginary part of the whole inner product is the absolute value of the imaginary part of z times the squared length of x.

But the magnitude of any inner product is at most the product of the lengths, by Cauchy–Schwarz. Therefore the length of the shifted output times the length of x is at least the absolute imaginary part of z times the squared length of x.

For nonzero x, divide by its length. We obtain the key inequality: the length of A minus z applied to x is at least the absolute imaginary part of z times the length of x.

First consequence: the shift is injective. If its output is zero, the inequality forces x to be zero.

Second consequence: its inverse, if it exists, has norm at most one divided by the absolute imaginary part of z.

The remaining task is surjectivity. A lower bound alone does not guarantee an operator maps onto H.

## Closed range plus density gives surjectivity

Since A is self-adjoint, it is closed. The shifted operator is also closed: if x N and the shifted outputs converge, add z times x N to the outputs and invoke closedness of A.

Now take a convergent sequence of outputs of A minus z. The lower bound shows the corresponding input sequence is Cauchy. Its limit belongs to the domain by closedness, and the output limit belongs to the range. So the range is closed.

We next prove that the range is dense. Suppose y is orthogonal to every shifted output. That means the inner product of A x with y equals the inner product of x with the conjugate shift times y, for every x in D. By the definition of the adjoint, y belongs to the adjoint domain and the adjoint of A applied to y equals the conjugate of z times y.

But A is self-adjoint. Thus y belongs to D, and it is a nonzero-shift eigenvector of A with the nonreal eigenvalue conjugate z, unless y is zero. The same lower bound excludes a nonzero such vector. Therefore y equals zero. The orthogonal complement of the range is zero, so the range is dense.

A range that is both closed and dense is all of H. The shift is bijective, and its inverse satisfies the norm bound we derived. We have constructed the nonreal resolvent.

This proof explains why self-adjointness is stronger than symmetry: we used equality of the adjoint and original domains to rule out vectors orthogonal to the range.

## Real shifts and lower form bounds

A similar argument works for real shifts that lie below a uniformly lower-bounded self-adjoint operator.

Suppose there is a real number a such that, for every x in D, the inner product of A x with x is at least a times the squared length of x.

Choose a real lambda strictly less than a. Then the inner product of A minus lambda applied to x with x is at least a minus lambda times the squared length of x.

Cauchy–Schwarz again gives a lower bound for the shifted output length, now with constant a minus lambda. The shift is injective and has closed range.

Its orthogonal complement is again the kernel of the adjoint shift. Since A is self-adjoint, the same lower bound applies to that kernel. Thus the range is dense and hence onto. The inverse norm is at most one divided by a minus lambda.

Therefore the entire interval below a lies in the resolvent set. Equivalently, the spectrum is contained in the real interval beginning at a and extending upward. An upper form bound gives the symmetric conclusion at the upper end.

This is an example of obtaining spectral location directly from a quadratic-form estimate, before using an explicit spectral integral.

## A diagonal example and the exact distance

For the diagonal operator on ell two, A multiplies coordinate N by N. Its spectrum is the positive integers, starting with one. The inverse of A minus z multiplies coordinate N by one divided by N minus z.

For a nonreal z, every denominator is nonzero. More generally, whenever z is not one of the positive integers, the denominators have a positive minimum distance from zero. The resolvent is bounded, with norm equal to the reciprocal of the distance from z to the spectrum.

The general self-adjoint spectral theorem gives that exact distance formula. Our elementary coercive argument has already proved the coarser but universally useful bound using the imaginary part of z.

Take z equal to negative one. The lower form bound a equals one, so the argument predicts inverse norm at most one half. In this diagonal example the first coordinate attains that bound, so it is exact.

At z equal to one, however, the first coordinate is an eigenvector in the kernel of the shifted operator, and the inverse does not exist.

## Coercive forms produce inverses another way

There is a second route that will be important for differential operators. Instead of beginning with an operator on H, begin with a Hilbert space V of admissible form vectors, continuously and densely embedded into H.

Suppose a bounded symmetric form on V satisfies a coercivity inequality: its energy on a vector controls a positive constant times that vector's squared V norm.

The Riesz representation theorem turns the form into a bounded positive self-adjoint operator F on V. Coercivity makes F invertible: the same lower-bound, closed-range, and orthogonal-complement argument applies in V.

If j embeds V into H, then for an ambient forcing vector f, solve F u equals j star f. The vector u equals F inverse j star f, and the ambient solution operator is j F inverse j star.

The resulting composition is bounded on the Hilbert space and can be the inverse of a self-adjoint unbounded operator obtained from a closed, lower-bounded quadratic form. This is one route to a rigorous beam operator, beyond formal integration by parts.

The two methods share their central estimate: a positive lower bound makes an inverse stable. The details of the domain are what determine which operator the bounded inverse belongs to.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For self-adjoint \(A\), \(\|(A-z)x\|\ge |\operatorname{Im}z|\,\|x\|\) on \(D(A)\) when \(\operatorname{Im}z\ne0\). Closed range and the adjoint orthogonality argument show \(A-z\) is onto; hence \(\|(A-z)^{-1}\|\le |\operatorname{Im}z|^{-1}\). A lower form bound \(\langle Ax,x\rangle\ge a\|x\|^2\) similarly places every real \(\lambda<a\) in the resolvent set with bound \((a-\lambda)^{-1}\). Source conventions distinguish the inverse of \(A-\lambda\) from the canonical inverse of \(\lambda-A\).

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `mem_realResolventSet_iff`:

```lean
theorem mem_realResolventSet_iff {A : E →ₗ.[𝕜] E} {lam : ℝ} :
    lam ∈ realResolventSet A ↔
      ∃ R : E →L[𝕜] E,
        (∀ x : A.domain, R (A x - (lam : 𝕜) • (x : E)) = (x : E)) ∧
        (∀ y : E, ∃ h : R y ∈ A.domain,
          A ⟨R y, h⟩ - (lam : 𝕜) • R y = y) :=
```

The source records two-sided inversion and explicit inverse-image membership in `A.domain`; its inverse is for `A - λ`.

`DavisKahan/SpectralTheory/FormSpectrumBounds.lean` — `realSpectrum_subset_Ici_of_le_re_inner_generic`:

```lean
theorem realSpectrum_subset_Ici_of_le_re_inner_generic
    {T : E →L[𝕜] E} {c : ℝ}
    (hform : ∀ z : E, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪T z, z⟫_𝕜) :
    realSpectrum T ⊆ Set.Ici c := by
```

For a bounded operator, a lower quadratic-form bound implies a corresponding lower real-spectral bound.

`DavisKahan/SpectralTheory/FormMethod/CoerciveFormResolvent.lean` — `formOperator_isUnit`:

```lean
theorem formOperator_isUnit (D : CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    IsUnit D.formOperator :=
```

The coercive-form method obtains a bounded inverse from a positive coercivity constant.

**Scope:** The exact nonreal-resolvent estimate for unbounded self-adjoint operators is proved in the narration; the source excerpts document related constructive resolvent and form techniques, not a replacement statement. These excerpts are from the supplied source snapshot and are not new compiled Lean code. Reusable `ForTauCeti` constructions have explicit DKPS donor/origin notes; the current file namespace does not imply an external origin.
