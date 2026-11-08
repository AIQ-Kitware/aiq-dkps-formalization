# 102000 — Real Hilbert complexification

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `007000` real and complex scalars, `009000` inner products, `012000` adjoints, `100000` modulus and ideal invariance. **Next:** `103000` real and complex spectra and functional calculus.

<!-- BEGIN SPOKEN LECTURE -->

# Giving a real Hilbert space complex coordinates

Much of spectral theory is easiest to state over complex Hilbert spaces. Complex exponentials solve differential equations, complex resolvents detect the spectrum, and several functional-calculus constructions are available first in the complex setting.

But the original operator may act on a real Hilbert space. A stability theorem about a real symmetric matrix should remain a theorem about that real matrix. We need a controlled way to move into complex Hilbert space, use the analytic theory, and come back without altering the quantities in the conclusion.

The construction is called complexification. We will build it explicitly, rather than treat it as an unnamed change of scalars.

## Build complex vectors from two real vectors

Let E be a real Hilbert space. Define its complexification to consist of ordered pairs of vectors from E. We write such a pair as x plus i y, with x and y in E.

Addition is coordinatewise. A complex scalar with real part a and imaginary part b acts by sending x plus i y to the vector whose real coordinate is a x minus b y, and whose imaginary coordinate is b x plus a y.

Check multiplication by i. It sends x plus i y to minus y plus i x. Apply i again and you get minus x minus i y. Thus multiplication by i twice is multiplication by minus one, as required.

The real space sits inside the complexification as vectors x plus i zero. The inclusion preserves addition, real scalar multiplication, and distances. Yet the complexification now allows multiplication by any complex scalar.

The norm is determined by the two coordinates. The square of the norm of x plus i y is the squared norm of x plus the squared norm of y.

Why this definition? It makes the real and imaginary copies orthogonal in the underlying real geometry, and multiplication by i preserves length. Indeed, replacing x,y by minus y,x leaves the sum of squared norms unchanged.

The complex inner product can be constructed by extending the real inner product and imposing complex sesquilinearity. Its real part pairs the real coordinates and imaginary coordinates. Its imaginary part is built from the two cross terms, with signs determined by which argument is complex linear. The resulting squared norm is exactly the one we specified.

Completeness follows from completeness of E. If a sequence of complex vectors is Cauchy, each real coordinate sequence and each imaginary coordinate sequence is Cauchy in E. They converge to vectors x and y. The complex sequence then converges to x plus i y.

## Complexify an operator coordinate by coordinate

Let T be a bounded real-linear map from E into another real Hilbert space F. Define its complexification by applying T separately to the real and imaginary coordinates.

So T complexified sends x plus i y to T x plus i T y.

This rule is complex linear. To check it, apply a plus i b to x plus i y and then apply T. Real linearity distributes T across each of the four real terms, producing exactly the result of multiplying T x plus i T y by a plus i b.

The construction also respects addition and composition. If S follows T, the complexification of S composed with T equals the complexification of S composed with the complexification of T. The identity remains the identity.

These are essential properties: any algebraic equation built from addition, real scalar multiplication, and composition survives the transfer.

There is a warning here. Complexification of operators is real-linear as a map between operator spaces, but it is not a complex-linear map defined on the real operator space. We have only real scalars to multiply the original operator by. Once T is complexified, the resulting operator itself is complex linear on the complexified vector space.

## Prove the operator norm is exactly preserved

We want more than a bound. We want equality between the norm of T and the norm of its complexification.

First take any complex vector x plus i y. The squared norm of its image is the squared norm of T x plus the squared norm of T y. Each term is bounded by the square of the norm of T times the squared norm of its input coordinate. Adding gives the upper bound: the complexified operator norm is at most the real operator norm.

For the reverse bound, restrict to vectors with imaginary coordinate zero. The complexified operator acts on x plus i zero as T x plus i zero and preserves the norm of the underlying real vector. Whatever upper bound holds for the complexified operator therefore also bounds the original operator. This gives the reverse inequality.

So the norms are equal, exactly.

Apply this identity to the difference of two real bounded operators. Because complexification preserves subtraction, the distance between their complexifications equals the distance between the original operators. Thus complexification is an isometric embedding of real operator spaces, not just a collection of unrelated norm equalities.

## The adjoint survives transfer

In perturbation theory, taking adjoints and forming Gram operators is routine. We need those constructions to commute with complexification.

Recall the defining equation for the adjoint. Pair T x with y in the target space, and the result equals the pairing of x with T adjoint y in the source space.

Apply that identity separately to the real and imaginary coordinates, including the cross terms that define the complex inner product. The complex adjoint identity follows. Consequently, the complexification of T adjoint is exactly the adjoint of the complexification of T.

Combining this with compatibility with composition gives the Gram identity. Complexifying T adjoint T produces the complex adjoint of T complexified, followed by T complexified.

Therefore positivity of the Gram operator and the lengths of singular-value constructions are compatible with transfer. The detailed approximation-number identity requires another argument, because low-rank approximation on complex spaces permits complex subspaces not initially presented as complexified real subspaces. The repository establishes that comparison separately.

## Conjugation tells us which objects come from real space

There is a canonical operation on the complexification: complex conjugation. It sends x plus i y to x minus i y.

It preserves length and applying it twice restores the original vector. It is conjugate linear rather than complex linear, because conjugating a complex scalar changes the sign of its imaginary part.

The real copy of E consists exactly of the vectors fixed by this conjugation. If x plus i y equals x minus i y, then y is zero.

Likewise, every complexified real operator commutes with conjugation. Apply the operator and then conjugate; or conjugate first and then apply the operator. Either route produces T x minus i T y.

Conversely, suppose a bounded complex-linear operator on the complexification commutes with conjugation. It sends each fixed real vector into another fixed real vector. Restricting it to the real copy gives a bounded real-linear operator. The original complex operator is recovered by extending that real restriction coordinatewise.

Thus commuting with conjugation is the criterion for descending a bounded complex operator to the real space. This criterion will matter when our complex proof constructs a spectral projection or a functional-calculus operator rather than merely transporting an operator already defined over the reals.

## A symmetric matrix and a rotation

Take a real two-by-two diagonal matrix with entries two and five. Its complexification applies the same matrix to both coordinates. Its operator norm remains five, its adjoint remains itself, and the real eigenvectors remain eigenvectors after embedding.

Now consider the real rotation by ninety degrees. This operator is not self-adjoint. Over the complex numbers it has eigenvalues i and minus i, even though it has no real eigenvectors. Complexification has allowed new spectral information to appear.

This example explains why statements about arbitrary real and complex spectra need precise definitions. For self-adjoint operators, however, the complex spectrum lies on the real axis, and comparison of their real spectral information becomes much cleaner.

## What we have earned

We can now move a real bounded operator into complex Hilbert space without changing its operator norm, adjoint relations, or composition identities. We can recognize which bounded complex operators come back to the real space by checking compatibility with conjugation.

In the next lecture we will apply these facts to spectra and the continuous functional calculus. A spectral projection obtained through a real-valued functional-calculus expression will commute with conjugation and therefore descend. But a projection defined by a discontinuous indicator needs special care at a spectral boundary.

The transferable object is the whole proof, including its hypotheses, not just the final inequality.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

The construction is `RealComplexification E = E ⊕₂ E`, with complex multiplication `(a+ib) • (x,y) = (ax−by,bx+ay)`. The real embedding `ofReal x = (x,0)` is isometric. For `T : E →L[ℝ] F`, `complexify T` acts on both coordinates, satisfies `‖complexify T‖=‖T‖`, respects composition and adjoint, and commutes with canonical conjugation.

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
