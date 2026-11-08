# Adjoints and the Riesz representation theorem

<!-- BEGIN SPOKEN LECTURE -->

Here is a question that sounds simple but contains much of Hilbert-space operator theory. Suppose a linear operator transforms an input vector into an output vector. Then we measure the output by taking its inner product with some chosen direction. Can we express that same measurement directly in terms of the input, without computing the output first?

The answer is yes for bounded operators on Hilbert spaces. But there are two distinct constructions along the way: pulling back a linear functional, and representing that functional by a vector. Confusing them makes adjoints seem like a notation trick. Keeping them separate explains both why adjoints exist and why they reverse the direction of an operator.

## First, a measurement is not a vector

Let E and F be two normed vector spaces, and let T carry vectors from E to F. Think of a measurement on F as a continuous linear functional: a rule that takes an output vector and returns one real or complex number.

We studied such functionals in the dual-space lecture. If we have a measurement on F, we can create a measurement on E simply by composing it with T. For an input x, apply T, then measure the result.

This process is called pulling a functional back through T. It reverses the direction of the mapping, because it starts with a measurement that knows how to handle outputs and produces one that knows how to handle inputs.

Notice what it does not do. It does not send an output vector back to an input vector. T might not have an inverse. It might collapse many input directions together. The pulled-back measurement exists anyway, because composition makes sense even when inversion does not.

The dual map needs normed spaces and bounded maps; no inner product is required. To get an adjoint acting on vectors, we need something extra.

## Turning a vector into a measurement

In a Hilbert space, choose a vector w. We can use w to measure any other vector x by taking the inner product of w with x. We are using the convention that the inner product is linear in its second argument. With this convention, fixing w in the first slot gives a linear functional of x.

By Cauchy–Schwarz, the absolute value of this measurement is at most the length of w times the length of x. So it is continuous. Every Hilbert-space vector therefore defines a continuous linear functional.

Are there other continuous linear functionals that cannot be expressed in this way? The Riesz representation theorem says no. Every continuous linear functional on a Hilbert space is represented by a unique vector, and the functional's norm equals the length of that vector.

This is stronger than a convenient coordinate formula. In an infinite-dimensional space, we cannot write down a finite row vector of coefficients for an arbitrary functional. Riesz tells us that the inner product still gives a complete description of all continuous linear measurements.

The projection theorem says that every vector in a Hilbert space has a unique nearest point in a closed linear subspace, and that the difference is perpendicular to the subspace. We can use that decomposition to prove the adjoint statement.

## Building the Riesz representing vector

Let f be a continuous linear functional on a Hilbert space H. If f is identically zero, the representing vector is zero. So consider a nonzero f.

The kernel of f is the set of vectors that f sends to zero. Because f is continuous, its kernel is closed. Because f is linear, its kernel is a subspace. Call it M.

Choose a vector u whose measurement is not zero. Such a vector exists because f is not the zero functional. Project u orthogonally onto M, then subtract that projection. Call the remainder z.

By the projection theorem, z is perpendicular to M. Also z cannot be zero: if it were, u itself would belong to M, contradicting our choice. Applying f to z gives the same value as applying f to u, because the projected part lies in the kernel. Thus f of z is nonzero.

Scale z to make a new vector v with f of v equal to one. Since scaling preserves perpendicularity, v is still perpendicular to M.

Now take any x in H. Subtract f of x times v from x. The result lies in M, because f of x minus f of x times f of v is zero. This gives a decomposition of x into a part in M plus the scalar f of x times v.

Take the inner product of v with this decomposition. The M part vanishes because v is perpendicular to M. What remains is f of x times the squared length of v.

Therefore, if we divide v by its squared length and call the resulting vector w, the inner product of w with any x is exactly f of x. We have constructed the representing vector.

The proof has a pleasing structure. A functional's kernel is a closed hyperplane in the nonzero case. Orthogonal projection finds a direction perpendicular to that hyperplane. Scaling that direction recovers the functional everywhere.

## Uniqueness and norm equality

Suppose two vectors w and w prime represent the same functional. Their difference has inner product zero with every vector. Choose the test vector to be the difference itself. Its squared norm is zero, so the two representing vectors are equal.

For the norm, Cauchy–Schwarz gives the easy inequality: the size of the functional is no greater than the length of w. To obtain the reverse inequality, test the functional on w divided by its length, when w is nonzero. That test vector has length one, and the absolute value of the measurement is exactly the length of w. So the functional norm and the representing-vector norm are equal.

In complex Hilbert spaces, remember a detail from the inner-product lesson. The map from representing vectors to functionals is conjugate-linear, because multiplying the first inner-product input by a complex number conjugates that number. It is a perfect correspondence, but not literally a complex-linear identification of the two spaces under this convention.

This will keep the complex signs correct when we build an adjoint.

## Constructing an adjoint rather than guessing it

Let T be a bounded linear map from Hilbert space E to Hilbert space F. Choose a vector y in F. We want to measure T of x by taking the inner product of y with T of x.

As x varies, that expression defines a continuous linear functional on E. It is linear in x, and its absolute value is bounded by the length of y times the operator norm of T times the length of x.

By the Riesz theorem, there is a unique vector in E representing this measurement. Call that vector T adjoint of y, or T star of y.

We have obtained the defining adjoint identity: the inner product of y with T of x equals the inner product of T star of y with x, for every input x and every output-side vector y.

Read this identity as a comparison of two procedures. In the first, transform the input and measure the output. In the second, transform the measuring direction backward and measure the original input. The scalar answers agree.

This is an operator from F back to E, but it is not generally an inverse. It does not undo T. It translates output-side measurements into input-side measurements.

## A calculation in two coordinates

Consider a real operator that takes the vector with coordinates a and b and returns the scalar two a plus three b. This is a map from the plane into the real line.

To measure its output against a scalar c, simply multiply by c. The result is two c times a plus three c times b. That is the dot product of the input vector with the vector having coordinates two c and three c.

So the adjoint sends c to the two-dimensional vector with coordinates two c and three c. The original operator compresses two coordinates into one scalar. The adjoint sends an output-side measuring direction to the corresponding input-side measuring direction. It cannot reconstruct the original input from the scalar output.

For a complex matrix the same calculation conjugates the entries when moving them into the adjoint. For example, if T sends two complex coordinates to twice the first plus eye times the second, the adjoint sends c to the two-coordinate vector twice c and negative eye times c. This is why the matrix of an adjoint is the conjugate transpose, not merely the transpose.

## Consequences we can now derive

Why is T star linear? If we scale or add output-side measuring vectors, the associated input functionals scale and add, with the matching conjugations from the first argument of the inner product. Uniqueness of their Riesz representations shows that T star respects the original scalar multiplication and addition of vectors.

Why is it bounded? The norm of the functional represented by T star of y is the length of T star of y. But we already bounded that functional by the operator norm of T times the length of y. Thus the operator norm of T star is at most the operator norm of T.

Applying the adjoint construction twice gives T back. This follows from the defining identity and uniqueness of the representing vector. Applying our norm estimate in both directions then shows the norm of T star equals the norm of T.

Finally, suppose T is followed by another bounded map S. An output measurement must first be pulled back through S, then through T. So the adjoint of S after T is T star after S star. The order reverses. This is the operator version of the reversal we saw for dual maps.

Later, a self-adjoint operator will mean an operator equal to its own adjoint. A unitary operator will have its adjoint as its inverse. And our future Gram operators will have the forms T star T or T T star. These expressions are no longer arbitrary symbols; they describe the geometry of how maps act on vectors and measurements.

## Reconstruction

To check your understanding, reconstruct three things without looking at the formal formulas. First, start with a nonzero continuous functional and use its kernel and an orthogonal projection to build the unique representing vector. Second, explain why the adjoint sends output vectors back to input vectors without being an inverse. Third, compute the adjoint of the real map that sends a pair of numbers to their difference.

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (display only)

Let \(E,F\) be real or complex Hilbert spaces and adopt the convention that the inner product is linear in its **second** argument. The Riesz correspondence is
\[
f(x)=\langle w,x\rangle,\qquad \|f\|=\|w\|,
\]
where the correspondence \(w\mapsto f_w\) is conjugate-linear over \(\mathbb C\). For \(T:E\to F\) bounded, the adjoint \(T^*:F\to E\) is uniquely characterized by
\[
\langle y,Tx\rangle_F=\langle T^*y,x\rangle_E.
\]
It satisfies \((ST)^*=T^*S^*\), \((T^*)^*=T\), and \(\|T^*\|=\|T\|\).

**Lean bridge.** The checked local source `ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean` directly relates its finite analysis map and synthesis map by the adjoint:

```lean
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

`finiteAnalysis 𝕜 v` sends an ambient vector to its coefficients \(\langle v_i,x\rangle\); `finiteSynthesis 𝕜 v` sends a coefficient family to its linear combination of the \(v_i\). The theorem identifies the map that reverses the measurement direction. `LinearMap.eq_adjoint_iff` expresses equality to an adjoint in terms of inner products. The surrounding module assumes a finite-dimensional real-or-complex inner-product space and a finite index type. In later Gram lectures, the two compositions are compared:

```lean
theorem finiteFrameOperator_eq_adjointCompSelf (v : ι → E) :
    finiteFrameOperator 𝕜 v = (finiteAnalysis 𝕜 v).adjoint.comp (finiteAnalysis 𝕜 v) := by
  rw [finiteFrameOperator, adjoint_finiteAnalysis]
```

The local source contains provenance information tracing this finite-frame infrastructure through its DKPS-to-TauCeti migration. The mathematical Riesz proof in the narration is not claimed to be a new local Lean declaration. Both displayed snippets were checked against the uploaded source snapshot; new Lean code was not compiled.
