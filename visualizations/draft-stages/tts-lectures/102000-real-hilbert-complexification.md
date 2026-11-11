# 102000 — Real Hilbert complexification

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `007000` real and complex scalars, `009000` inner products, `012000` adjoints, `100000` modulus and ideal invariance. **Next:** `103000` real and complex spectra and functional calculus.

<!-- BEGIN SPOKEN LECTURE -->

# Why give a real Hilbert space complex scalars?

Imagine rotating a vector in the real plane by ninety degrees.

Point right and the rotation sends you up. Point up and it sends you left. If you apply the rotation twice, you get a half turn, which is multiplication by negative one.

Could this rotation have an eigenvector? Over the real numbers, no. There is no nonzero direction that a ninety-degree rotation leaves on its own line.

But if we allow complex scalars, the rotation has eigenvalues i and negative i. The missing spectral description appears when we enlarge our scalars.

This gives us a reason to complexify a real Hilbert space. We want access to complex spectral theory while preserving the original real geometry. We also want to know which results can be brought back to the real setting without changing their constants.

## One complex vector is two real vectors

Start with a real Hilbert space E. It could be the plane, or it could be an infinite-dimensional space of real square-summable sequences.

Construct a new space whose elements are pairs of real vectors, x and y. We write the pair as x plus i y.

This notation is literal: x is the real component and y is the imaginary component. Both belong to E.

Addition works component by component. To multiply x plus i y by a complex number a plus i b, use ordinary complex multiplication: the new real component is a x minus b y, and the new imaginary component is b x plus a y.

Try multiplying by i alone. It sends x plus i y to negative y plus i x. Do it a second time and you get negative x minus i y. So multiplication by i really does square to negative one.

We have constructed a complex vector space from the original real one.

There is one dimension point worth keeping straight. The real plane becomes a complex space with complex dimension two, even though it has four real coordinates when viewed without its complex structure. We have not thrown away the original plane. It sits inside as vectors whose imaginary component is zero.

## Preserve lengths and completeness

We need more than complex scalar multiplication. A Hilbert space has a notion of distance, and it must be complete.

Define the squared norm of x plus i y to be the squared norm of x plus the squared norm of y.

This makes geometric sense. The two copies of E are perpendicular in the underlying real geometry. Multiplying by i exchanges those copies with a sign, so it preserves length.

For example, if x has length three and y has length four, the complexified vector has length five.

The complex inner product is chosen to extend the original real inner product, with the appropriate cross terms. Its value on a vector paired with itself is precisely the squared norm we just defined.

Completeness is inherited coordinatewise. A Cauchy sequence of these pairs has a Cauchy sequence of real components and a Cauchy sequence of imaginary components. Since E is complete, both converge. Their pair is the limit in the complexification.

So we've genuinely built a complex Hilbert space, not just adopted a notation.

## Apply the same real operator to both coordinates

Suppose T is a bounded real-linear operator from a real Hilbert space E to another real Hilbert space F.

Define its complexification in the obvious way: apply T to x, and separately apply T to y. Thus x plus i y is sent to T x plus i T y.

It's important to check that this is complex linear. Multiplication by i exchanges the two real coordinates with a sign, and applying a real-linear T commutes with that exchange. The same holds for any complex scalar.

Complexification also respects composition and addition. If one real operator is applied after another, doing that first and complexifying gives the same result as complexifying both and then composing.

Let's look at a simple diagonal matrix. Suppose T multiplies the first real coordinate by two and the second by five. Applied to a complex vector, it multiplies the first complex coordinate by two and the second by five. No new stretching has appeared.

In fact, the operator norm is exactly preserved for every bounded real-linear T.

## Why the norm does not change

Take any vector x plus i y. The squared length of its image under complexified T is the sum of the squared lengths of T x and T y.

Each term is at most the square of the original operator norm times the squared length of its input. Add the two inequalities. The norm of complexified T cannot exceed the norm of T.

Now restrict the input to vectors with imaginary component zero. On those vectors, the complexified operator behaves exactly like T, with exactly the same lengths. That gives the reverse inequality.

So the two operator norms are equal.

This is stronger than saying complexification is continuous. Any quantitative estimate that depends only on bounded operator norms can carry over with its numerical constant intact, provided the other hypotheses also survive.

## Adjoints, self-adjointness, and conjugation

The adjoint is defined by an inner-product relation: pairing T x with a target vector equals pairing x with the adjoint applied to that target vector.

Because the complex inner product was built from the real one, this relation holds separately for the real and imaginary components and their cross terms. The complexification of the real adjoint is the adjoint of the complexified operator.

Consequently, a bounded real self-adjoint operator becomes a bounded complex self-adjoint operator. Its Gram operator also transfers: complexifying T adjoint T gives the Gram operator of complexified T.

Now consider the operation of complex conjugation. It sends x plus i y to x minus i y. The original real vectors are exactly the ones fixed by this operation.

Every complexified real operator commutes with conjugation. You get the same result whether you conjugate the input first or conjugate the output afterward.

There's also a converse. Suppose a bounded complex-linear operator on this complexified space commutes with conjugation. It must send real fixed vectors to real fixed vectors. Restrict it to that real copy of E, and it becomes a bounded real-linear operator. Complexifying the restriction reconstructs the original complex operator.

That gives us a test for whether an operator constructed in complex space really comes from the real space.

## Revisit the rotation

Our ninety-degree real rotation has no real eigenvectors. Its complexification has two complex eigenvalues, i and negative i. So complexification can reveal spectral features that aren't expressible as real eigenvalues.

But the rotation is not self-adjoint. For self-adjoint operators, the complex spectrum lies on the real axis. That observation makes the transfer of their spectral information much cleaner.

We have to keep the two claims separate. Complexifying any bounded real map preserves its norm and algebraic structure. Complexifying a self-adjoint real map also makes complex spectral theory available, but recovering a particular spectral projection requires checking that the construction respects conjugation.

The useful mental picture is a real space embedded inside two coordinated real copies. Operators extend by acting on each copy in the same way. Their norms and adjoints stay intact. And conjugation tells us exactly which bounded complex operators can be returned to the real setting.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

The construction is `RealComplexification E = E ⊕₂ E`, with complex multiplication `(a+ib) • (x,y) = (ax−by,bx+ay)`. The real embedding `ofReal x = (x,0)` is isometric. For `T : E →L[ℝ] F`, `complexify T` acts on both coordinates, satisfies `‖complexify T‖=‖T‖`, respects composition and adjoint, and commutes with canonical conjugation.

### Worked example: the real plane and rotation

For \(E=\mathbb R^2\), the complexification has complex dimension two and is canonically identifiable with \(\mathbb C^2\). The real rotation
\[
R=\begin{pmatrix}0&-1\\1&0\end{pmatrix}
\]
satisfies \(R^2=-I\). Its complexification has eigenvalues \(i\) and \(-i\), while the real operator has no nonzero real eigenvector. For \(T=\operatorname{diag}(2,5)\), \(\|\operatorname{complexify}T\|=\|T\|=5\).

### Actual Lean source declarations

`ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean` — `complexify` (exact declaration header; proof omitted):

```lean
def complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) : RealComplexification E →L[ℂ] RealComplexification F := by
```

`ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean` — `norm_complexify` (exact declaration header; proof omitted):

```lean
theorem norm_complexify [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (T : E →L[ℝ] F) : ‖complexify T‖ = ‖T‖ := by
```

`ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean` — `complexify_isSelfAdjoint_iff` (exact declaration header; proof omitted):

```lean
theorem complexify_isSelfAdjoint_iff [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (T : E →L[ℝ] E) :
    IsSelfAdjoint (complexify T) ↔ IsSelfAdjoint T := by
```

`ForTauCeti/Analysis/InnerProductSpace/Complexification/FunctionalCalculus.lean` — `complexify_adjoint` (exact declaration header; proof omitted):

```lean
theorem complexify_adjoint (T : E →L[ℝ] F) :
    complexify T.adjoint = (complexify T).adjoint := by
```

**Type and hypothesis map.** `complexify` takes a real continuous linear map `E →L[ℝ] F` to a complex continuous linear map between the two real complexifications. The norm theorem is an equality. The self-adjointness equivalence adds a complete real Hilbert space assumption; the adjoint bridge handles rectangular maps. These are bounded operator declarations, distinct from the later unbounded partial-map transport.

These Lean snippets are copied exactly from the supplied DKPS repository snapshot. The narration is an independent mathematical derivation; this appendix does not claim that the narrated text was compiled in Lean. Foundational results currently in `ForTauCeti` may have been developed in DKPS before upstreaming.
