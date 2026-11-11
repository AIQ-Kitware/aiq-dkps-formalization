# 086000 — Resolvents, coercivity, and spectral location

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `033000` positive forms, `081000` resolvent integrals, `084000` self-adjointness. **Next:** `087000` Cayley transforms.

<!-- BEGIN SPOKEN LECTURE -->

# Resolvents, coercivity, and spectral location

An unbounded operator presents an apparent paradox. Its outputs can become arbitrarily large compared with its inputs. Yet the inverse of a shifted unbounded self-adjoint operator can be a bounded operator defined on the entire Hilbert space.

How can that happen? And how can we prove the inverse exists without first computing all the spectral values?

The key is a lower bound on the shifted operator. If applying the shift cannot make a vector too small, then reversing that operation cannot amplify an output without limit. For a self-adjoint operator, we can turn that observation into a complete invertibility proof.

We'll develop the argument on an abstract Hilbert space, check it on a concrete infinite sequence operator, and then see how the same idea appears when an operator is constructed from an energy form.

## A model that is genuinely unbounded

Take the Hilbert space of square-summable sequences. An element is an infinite list of numbers whose squared magnitudes add up to a finite total.

Define A by multiplying coordinate number n by n. The first coordinate gets multiplied by one, the second by two, the third by three, and so on.

This rule is unbounded. Put a single one at coordinate number one thousand and zeros everywhere else. The input has norm one, but its image has norm one thousand. We can make that output norm as large as we wish.

There is also a domain restriction. We can apply A only to sequences for which the sequence obtained by multiplying coordinate n by n is still square-summable. Equivalently, the sum of n squared times the squared magnitude of coordinate n must be finite.

The operator is self-adjoint on that domain. This means it agrees with its adjoint, including the set of inputs on which the adjoint is defined. It is the infinite-dimensional counterpart of a real symmetric diagonal matrix with increasingly large diagonal entries.

Now shift by negative one. Subtracting negative one is the same as adding one. The new operator multiplies coordinate n by n plus one.

Its inverse divides coordinate n by n plus one. Every division factor is at most one half, so the inverse is bounded on the whole square-summable space.

And the output of that inverse really does belong to the domain of A. Multiplying it back by n gives the factor n divided by n plus one, which is at most one. Thus the resulting weighted sequence is square-summable.

This illustrates the general goal. The original operator may have a proper domain. A resolvent takes an arbitrary Hilbert space vector as input and returns an element of that domain, with a bound on its size.

## State exactly what an inverse must do

Let H be a complex Hilbert space, and A a densely defined self-adjoint operator. Its domain is a collection of allowed inputs that need not equal all of H.

For a complex shift z, the operator A minus z times the identity is still defined only on that same domain.

To say that z belongs to the resolvent set means three things. The shifted operator gives a unique input for each output. Every vector in H is an allowed output. And the inverse, which takes arbitrary vectors of H back into the domain of A, is bounded when viewed as an operator from H into H.

The inverse is called the resolvent at z.

A lower bound will give uniqueness and boundedness. But we must also prove that every output can actually be reached. That second part is where self-adjointness plays its essential role.

## Start with a nonreal shift

Choose z with nonzero imaginary part. Take any vector x in the domain of A.

Look at the inner product of A applied to x, minus z times x, with x itself.

Because A is symmetric, the inner product of A x with x is real. Its imaginary part is zero. Consequently, the magnitude of the imaginary part of our shifted inner product is exactly the absolute value of the imaginary part of z times the squared length of x.

Cauchy–Schwarz tells us that the magnitude of the whole inner product is no greater than the length of the shifted output times the length of x.

Combine those facts and divide by the length of a nonzero x. We obtain a central inequality.

The length of A minus z times the identity, applied to x, is at least the absolute value of the imaginary part of z multiplied by the length of x.

Let's interpret it. If the imaginary part of z is one, the shifted operator cannot shrink any vector. If the imaginary part is one tenth, it cannot shrink a vector by more than a factor of ten.

If the output is zero, the lower bound forces x to be zero. So the shift is injective.

And if the inverse exists, its norm must be at most one divided by the absolute value of the imaginary part of z. That gives us the proposed stability bound before we've completed the existence proof.

## Why being bounded below is not yet enough

An injective operator can miss many output vectors. For example, the map that moves every sequence entry one place to the right, filling the first coordinate with zero, preserves lengths. Its output norm is always exactly the input norm. But it cannot produce a sequence whose first coordinate is one.

So a lower bound alone does not establish surjectivity.

For our self-adjoint shift, two more facts close the gap.

First, self-adjoint operators are closed. Closedness means that if a sequence of allowed inputs converges and their operator outputs also converge, the input limit remains allowed and produces the output limit.

Now take a convergent sequence of shifted outputs. Our lower bound forces the corresponding inputs to form a Cauchy sequence. The inputs converge in H. Closedness then places their limit in the original domain and shows that its shifted output is the desired limit.

Therefore the range of the shifted operator is closed.

Second, we show the range is dense. Suppose a vector y is orthogonal to every shifted output. The definition of the adjoint then says that y belongs to the adjoint domain and is annihilated by A adjoint minus the complex conjugate of z.

Self-adjointness means that A adjoint is A, including equality of domains. Thus y is an allowed input to A and satisfies a shifted equation with the conjugate of z.

That conjugate still has a nonzero imaginary part. Apply the lower bound again. It forces y to be zero.

So the only vector orthogonal to the range is zero. The range is dense. Since it is also closed, it must be all of H.

We have proved surjectivity, and therefore existence of the bounded inverse.

This is the nonreal resolvent theorem: every nonreal shift of a self-adjoint operator has a bounded inverse, with norm at most one divided by the magnitude of the shift's imaginary part.

Notice that symmetry by itself would not have justified the argument. We needed self-adjointness to identify the adjoint domain and rule out the missing output directions.

## Real shifts below the spectrum

The imaginary part gave us a lower bound for nonreal shifts. How can we locate real resolvent points?

Suppose A satisfies a lower energy estimate: for every allowed x, the inner product of A x with x is at least a times the squared length of x, for some real number a.

For our diagonal sequence operator, we can choose a equal to one. Every coordinate is multiplied by at least one, so the quadratic form is at least the squared norm.

Now choose a real shift lambda below a. The quadratic form of A minus lambda times the identity is at least a minus lambda times the squared norm.

Cauchy–Schwarz gives a lower bound on the length of the shifted output, with positive constant a minus lambda.

The range is closed by the same argument as before. Since A minus lambda times the identity is itself self-adjoint, a vector orthogonal to its range must lie in its kernel. The lower bound makes that kernel zero. Hence the range is dense, and the shift is onto.

So every real number below a belongs to the resolvent set. Its inverse norm is at most one divided by a minus lambda.

In spectral language, the entire spectrum lies at or above a. The lower quadratic-form bound has located one side of the spectrum without requiring us to diagonalize A.

For our sequence operator, choose lambda equal to negative one. Then a minus lambda is two. The theorem gives a resolvent norm at most one half. The inverse actually has norm one half, because its first coordinate multiplier is exactly one half.

At lambda equal to one, the shifted operator has the first coordinate direction in its kernel, so the resolvent fails to exist. The example shows both the power and the boundary of the estimate.

## From energy forms to operators

There is another place where lower bounds produce useful inverses: the construction of differential and other unbounded operators from quadratic forms.

Instead of beginning with an operator A whose domain is already known, start with a Hilbert space V of admissible energy vectors. Assume V is continuously and densely embedded in a larger Hilbert space H. Let j be the inclusion map from V into H.

On V, define a bounded symmetric bilinear or sesquilinear energy form. Suppose the form controls the squared V norm from below by a positive constant. We call this coercivity.

By the Riesz representation theorem on V, the form can be represented by a bounded self-adjoint operator F on V. Coercivity makes F invertible with bounded inverse.

If an ambient force f belongs to H, apply the adjoint of the inclusion to obtain a forcing functional represented in V. Solve the equation there using F inverse. Then include the solution back into H.

The resulting ambient solution operator has the form: inclusion, followed by F inverse, followed by the adjoint of inclusion. It is bounded on H. Under the standard assumptions for a densely defined closed positive form, it is the inverse of the associated positive self-adjoint operator on H.

Let's see that construction in our sequence example.

Use V for the sequences whose sum of n times the squared magnitude of coordinate n is finite. This energy space contains the operator domain, which instead requires the stronger weight n squared.

Define the energy of a sequence as that sum with weight n. With the corresponding inner product, the form operator F on V is simply the identity. The inclusion j forgets the stronger energy norm and regards the sequence as an element of ordinary square-summable space.

Now the formula involving j, F inverse, and j adjoint sends a sequence with coordinate f at position n to a sequence whose corresponding coordinate is f divided by n.

That's exactly the inverse of our unbounded diagonal operator A. And the resulting sequence lies in the domain of A, since multiplying it by n returns the original square-summable sequence.

This example distinguishes the three spaces and roles involved: the ambient Hilbert space, the form domain V where energy is measured, and the smaller operator domain where A actually acts.

## The conclusion to retain

A lower bound gives control over how small an operator's output can be. Inverting that inequality gives a bound on the inverse. For self-adjoint operators, closedness and the adjoint argument provide the missing surjectivity step.

For nonreal shifts, the imaginary part supplies the lower bound. For sufficiently low real shifts, a quadratic-form estimate supplies it. And in the form method, coercivity makes an energy equation solvable and produces an inverse for the associated operator.

The unbounded diagonal operator makes the ideas concrete. It can amplify selected unit vectors by arbitrary factors, while its resolvent at negative one is a bounded operator of norm one half defined on all square-summable sequences.

As a final reasoning check, explain why a lower bound alone cannot prove surjectivity, using the right-shift operator on sequences. Then identify the extra ingredient that makes the argument work for self-adjoint operators: the range is closed, and its orthogonal complement is forced to be zero.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For self-adjoint \(A\), \(\|(A-z)x\|\ge |\operatorname{Im}z|\,\|x\|\) on \(D(A)\) when \(\operatorname{Im}z\ne0\). Closed range and the adjoint orthogonality argument show \(A-z\) is onto; hence \(\|(A-z)^{-1}\|\le |\operatorname{Im}z|^{-1}\). A lower form bound \(\langle Ax,x\rangle\ge a\|x\|^2\) similarly places every real \(\lambda<a\) in the resolvent set with bound \((a-\lambda)^{-1}\). Source conventions distinguish the inverse of \(A-\lambda\) from the canonical inverse of \(\lambda-A\). For the sequence example,
\[
H=\ell^2,\qquad A(x_n)=(nx_n),\qquad
D(A)=\{x:\sum_{n\ge1}n^2|x_n|^2<\infty\}.
\]
The coercive form \(b(u,v)=\sum_{n\ge1}nu_n\overline{v_n}\) lives on
\(V=\{u:\sum_{n\ge1}n|u_n|^2<\infty\}\). With its energy inner product, the form operator on \(V\) is the identity, and \(jF^{-1}j^*=A^{-1}\) acts by dividing coordinate \(n\) by \(n\).

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
