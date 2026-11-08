# 081000 - Resolvents from spectral integrals

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `008000` resolvents, `031000` spectral separation, `075000-080000` spectral calculus and measurable restriction. **Next:** `082000` spectral approximation by cutoffs.

<!-- BEGIN SPOKEN LECTURE -->

# Reading the spectrum through inverse operators

We began this course by defining the spectrum using invertibility. A complex number z is outside the spectrum of A when A minus z times the identity has a bounded inverse. That inverse is called the resolvent at z.

Now that we have spectral integration, we can write the resolvent explicitly. We will see why its norm is controlled by the distance from z to the spectrum, why resolvents become large near spectral values, and how their matrix elements encode the scalar spectral measures.

Throughout today, A is a bounded self-adjoint operator on a nonzero complex Hilbert space. Its spectrum is a nonempty compact subset of the real line.

## Inverting pointwise on the spectrum

Choose a complex number z outside the spectrum. The scalar function g of lambda equals one divided by lambda minus z.

Because the denominator never vanishes on the compact spectrum, g is continuous and bounded there. We may therefore apply the continuous functional calculus, or equivalently the bounded Borel calculus, to obtain g of A.

Multiply g of lambda by lambda minus z. At every spectral point, the product is one. Functional calculus preserves products and the constant-one function, so g of A times A minus z times the identity equals the identity. The reverse product is also the identity because both factors belong to the same commutative functional calculus.

Thus g of A is the resolvent of A at z.

In spectral-integral notation, the resolvent is the integral of one divided by lambda minus z against the projection-valued measure E.

This argument is the infinite-dimensional analogue of inverting a diagonal matrix by taking reciprocals of its diagonal entries. It works even for operators with continuous spectrum and no eigenvectors.

## The distance estimate

Let d be the distance from z to the spectrum of A. Because z is outside that compact set, d is positive.

The modulus of one divided by lambda minus z is at most one over d on the spectrum. The operator norm estimate for functional calculus therefore gives the resolvent norm at most one over d.

For a bounded self-adjoint operator, this is an equality. The continuous functional calculus is isometric: the norm of a continuous function of A equals its maximum absolute value on the spectrum. The reciprocal symbol attains its maximum at a spectral point nearest to z, so the resolvent norm equals one divided by the distance.

This is a precise equality, not merely a qualitative statement that inverse operators become large near singularity.

For a general nonnormal operator the equality may fail badly. Nonnormal matrices can have large resolvent norm far from their eigenvalues. The sharp inverse-distance formula depends on normality, which self-adjoint operators possess.

## An explicit two-level example

Take the matrix with diagonal entries minus two and three. Choose z equal to i, the imaginary unit. The resolvent is diagonal, with entries one divided by minus two minus i, and one divided by three minus i.

The magnitudes of these entries are one over the square root of five and one over the square root of ten. The operator norm is their maximum, one over the square root of five.

The distance from i to the spectrum consisting of minus two and three is the square root of five, exactly as the formula predicts.

If z approaches minus two along the imaginary direction, say z equals minus two plus i times eta with eta positive, one denominator has magnitude eta. The resolvent norm is therefore at least one over eta, and in fact equals that value for sufficiently small eta.

Nothing in this calculation required an eigenvector expansion in the general theorem. The finite example merely makes the spectral-integral formula visible.

## Why spectral points prevent a bounded inverse

We have shown that every z outside the spectrum has the displayed inverse. Can we recognize the converse using spectral projections?

Take a real spectral point c. For every positive epsilon, the interval of radius epsilon around c must have a nonzero spectral projection. If some such interval had zero projection, the reciprocal of lambda minus c could be defined as a bounded Borel function on the remaining spectral support, and would produce a bounded inverse. That would contradict c being spectral.

Choose a unit vector x sub epsilon in the range of the projection onto that small interval. The squared norm of A minus c acting on x sub epsilon is the integral of the squared quantity lambda minus c over its scalar spectral measure.

All of that measure is supported inside the epsilon interval, so the norm of A minus c acting on x sub epsilon is at most epsilon.

As epsilon approaches zero, these are approximate eigenvectors. There may be no actual eigenvector with eigenvalue c, but the operator A minus c still cannot have a bounded inverse, since a bounded inverse would give a positive lower bound on its action on unit vectors.

This is how spectral support recovers the spectrum even in the continuous-spectrum case.

## The resolvent identity

There is an algebraic identity connecting resolvents at two points z and w, both outside the spectrum.

Subtract the scalar reciprocal functions. One divided by lambda minus z, minus one divided by lambda minus w, equals z minus w divided by the product of those two denominators.

Apply functional calculus. We obtain that the resolvent at z minus the resolvent at w equals z minus w times the product of the two resolvents.

Because these resolvents are functions of the same A, they commute. The identity can also be proved abstractly by multiplying out inverses, so it is valid for general bounded operators at points of their resolvent sets.

Taking norms yields a local continuity estimate. At fixed positive distance from the spectrum, the two resolvent norms remain uniformly bounded, and their difference is controlled by the distance between z and w.

In particular, the resolvent depends continuously on z outside the spectrum. More advanced analysis shows it is analytic there; that fact will later support contour formulas for spectral projections.

## Matrix elements are scalar integral transforms

Fix a vector x. The diagonal matrix element of the resolvent is the integral of one over lambda minus z against the positive spectral measure mu sub x.

This is often called a Cauchy transform or Stieltjes transform of the measure. It connects an operator-valued inverse to an ordinary scalar integral.

Let z have real part u and positive imaginary part eta. The imaginary part of the scalar reciprocal one over lambda minus u minus i eta is eta divided by the sum of the square of lambda minus u and eta squared.

Consequently, the imaginary part of the diagonal resolvent matrix element is the integral of this nonnegative kernel against mu sub x. It is nonnegative.

As eta becomes small, the kernel concentrates near u. After the appropriate normalization, its integral over u recovers spectral mass on intervals, with endpoint conventions requiring care. This is one route to recovering the spectral measure from the resolvent.

For an eigenvector at c, the scalar measure is an atom at c, and the matrix element has a reciprocal singularity at c. For continuous spectral measure, the behavior is spread across a continuum.

## Cutoffs and the approach to unbounded theory

The reciprocal formula is simple for a bounded self-adjoint A because its spectral coordinate is bounded and its resolvent symbol is bounded whenever z avoids the spectrum.

Later we will consider unbounded self-adjoint operators. Their coordinate function is itself unbounded and has a proper domain. Nevertheless, the scalar reciprocal one over lambda minus z is bounded for every nonreal z, since its denominator is at least the magnitude of the imaginary part.

That observation will allow resolvents to remain bounded even when the original self-adjoint operator is unbounded. The spectral theorem for such operators is constructed with measurable cutoffs and careful domain statements.

We must not treat those domain issues as merely notation. An identity for a bounded resolvent does not automatically make the unbounded operator act on every vector.

## The thread connecting the unit

We began with projections assigned to Borel sets. We converted them into scalar and complex measures, used those measures to construct functional calculus, and represented the operator as multiplication on cyclic L two spaces. Restricting to spectral subspaces and inverting scalar functions then became compatible operations.

The resolvent formula completes this chain: outside the spectrum, inversion of A minus z is simply division by lambda minus z inside the spectral integral. Its norm records the exact spectral distance for self-adjoint A.

The next lecture turns from fixed Borel symbols to approximating spectral expressions by finite partitions and cutoffs. That approximation machinery is what we need before introducing unbounded operators with explicit domains.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

With `A = A*` bounded and `z` in the complex resolvent set, `R_A(z) = (A - z I)^(-1) = integral (lambda - z)^(-1) dE(lambda)`, and `||R_A(z)|| = 1 / dist(z,spectrum(A))` on a nonzero Hilbert space. For a scalar spectral measure `mu_x`, `<x,R_A(z)x> = integral (lambda-z)^(-1) d mu_x(lambda)`. The source formalizes inverse-distance *upper bounds* for bounded self-adjoint resolvents and resolvent identities; the full equality and scalar-transform interpretation here are derived mathematically, not attributed to those specific theorem headers.

**Lean bridge (verbatim source declaration headers).**

`DavisKahan/SpectralTheory/ResolventOperator.lean` - `resolvent_identity`:

```lean
theorem resolvent_identity
    (A : E →L[𝕜] E) {z w : 𝕜}
    (hz : InResolventSet A z) (hw : InResolventSet A w) :
    resolventOperator A z - resolventOperator A w =
      (z - w) • (resolventOperator A z ∘L resolventOperator A w) :=
```

This module defines its bounded resolvent as the inverse of `A - z I`; the displayed identity uses that sign convention.

`DavisKahan/SpectralTheory/ResolventOperator.lean` - `complex_inResolventSet_and_norm_resolvent_le_inv_distance`:

```lean
theorem complex_inResolventSet_and_norm_resolvent_le_inv_distance
    (A : H →L[ℂ] H) (hA : A.IsSymmetric)
    (z : ℂ) (delta : ℝ) (hdelta : 0 < delta)
    (hsep : ∀ lam ∈ realSpectrum A, delta ≤ ‖z - (lam : ℂ)‖) :
    InResolventSet A z ∧ ‖resolventOperator A z‖ ≤ delta⁻¹ :=
```

For symmetric bounded complex operators, a positive lower bound `delta` on spectral distance yields resolvent-set membership and the norm upper bound `delta^-1`.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralMeasure/Construction.lean` - `spectralPVM_resolvent_formula`:

```lean
theorem spectralPVM_resolvent_formula (hzr : z ∈ resolventSet A) (ξ : H) :
    ⟪ξ, resolvent A z ξ⟫_ℂ
      = ∫ s, (z - (s : ℂ))⁻¹ ∂((spectralPVM hA).diag ξ) :=
```

This theorem concerns an unbounded self-adjoint operator and uses the separate convention `resolvent A z = (z I - A)^-1`, so its integrand is `(z-lambda)^-1`, the negative of the bounded resolvent convention used in this lecture. Do not identify the two without a minus sign.

**Scope:** The excerpts are declaration headers, not complete proof bodies. Their enclosing modules supply scalar types, normality/self-adjointness assumptions, and typeclass instances. The prose derives the mathematical statements and does not claim that all of the pedagogical arguments have separate local Lean theorems.
