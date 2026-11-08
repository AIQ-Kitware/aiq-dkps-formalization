# 077000 - Scalar spectral measures and polarization

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `006000` dual spaces, `009000` polarization, `073000-074000` measures and integration, `076000` projection-valued measures. **Next:** `078000` cyclic decompositions.

<!-- BEGIN SPOKEN LECTURE -->

# How diagonal spectral measurements determine an operator

The measure of a spectral set B was the squared length of the projection of x onto that set. These diagonal measurements are especially natural because they cannot be negative.

But an operator is determined by what happens between two potentially different vectors. If we only know the squared lengths of spectral pieces, can we recover inner products involving an arbitrary pair x and y?

Yes. The key is the complex polarization identity: inner products can be reconstructed from the squared norms of sums of vectors and their multiples by the imaginary unit. Today we will reconstruct the missing cross terms, explain why they form complex measures, and see how those measures let us define the Borel functional calculus.

## Begin with the diagonal

Let A be bounded and self-adjoint on a complex Hilbert space, and let E denote its projection-valued measure. For each vector x, write mu sub x of B for the inner product of x with E of B applied to x.

Because E of B is an orthogonal projection, mu sub x of B is the squared norm of E of B applied to x. It is a nonnegative finite measure, and its total mass is the squared norm of x.

In a diagonal three-by-three example, say A has diagonal entries minus two, zero, and five. If x has coordinates one, two, and three, the spectral masses are one at minus two, four at zero, and nine at five. Their sum is fourteen, the squared norm of x.

If an eigenvalue is repeated, the mass at that eigenvalue is the squared norm of the entire component in its eigenspace, independent of which orthonormal basis we choose inside the eigenspace.

The same formula remains meaningful when there is no discrete eigenvalue list. For multiplication by t in L two, the measure has density equal to the squared magnitude of the representing function.

## The four-vector polarization trick

Consider any bounded operator T and the expression obtained by pairing x with T applied to x. Call this its diagonal quadratic expression. If T is self-adjoint, it is real-valued, but the complex polarization identity works more generally for the sesquilinear form obtained from T.

Evaluate that diagonal expression at four vectors: x plus y, x minus y, x plus i times y, and x minus i times y. Expanding the inner products gives a system of four equations. The diagonal contributions cancel when we take the appropriate signed combination. What remains is the desired cross term involving x and T applied to y.

The exact signs depend on which inner-product argument is complex-linear. The essential point is invariant: four diagonal measurements determine one off-diagonal matrix element. This is why working over the complex field requires keeping track of multiplication by i, rather than using only sums and differences.

Apply this calculation with T equal to the spectral projection E of B. Every diagonal expression becomes one of the positive measures we already know. Their signed complex combination defines a set function, which we can denote mu sub x comma y.

For each Borel set B, that complex number is the inner product of x with E of B applied to y.

## Why the cross term is a measure

A complex measure is countably additive but may take complex values. Positivity is no longer expected for two different vectors. We need to know that the sum over disjoint sets converges and behaves correctly.

The polarization formula expresses each cross set function as a fixed finite linear combination of four positive finite measures. A finite linear combination of finite complex measures is a finite complex measure. Countable additivity therefore follows directly.

Alternatively, look at the projections. If B-one, B-two, and so forth are disjoint, the sum of the projected pieces of y converges in norm to the projection of the union applied to y. Pairing with x is continuous, so the scalar cross terms converge to the cross term of the union.

There is also a useful bound. By Cauchy-Schwarz,

The magnitude of the inner product of x with E of B applied to y is at most the length of E of B applied to x times the length of E of B applied to y.

That is at most the product of the norms of x and y. In fact, applying the same estimate over a disjoint partition and then Cauchy-Schwarz for sums gives a bound on the total variation of the complex measure by the product of those two norms.

This uniform bound is what allows integration against bounded measurable symbols.

## Spectral integrals as matrix elements

Let f be a bounded Borel function on the real line. For each pair x and y, integrate f against the complex measure mu sub x comma y. Call the resulting number B sub f of x and y.

The map is sesquilinear in the two vectors. Its magnitude is bounded by the supremum of the absolute value of f times the norms of x and y. This is a bounded sesquilinear form.

Now fix y. The map from x to this complex number is a bounded linear or conjugate-linear functional according to our inner-product convention. The Riesz representation theorem supplies a unique vector z with the required inner products against every x. Define f of A applied to y to be z.

We must also show dependence on y is linear and bounded. Linearity follows because the defining matrix elements are linear in y. The same uniform estimate gives the bound on its operator norm.

This is an actual construction of an operator from integrals, not merely an abbreviation. It converts the scalar spectral measures into a bounded functional calculus.

## Working with a two-level operator

Take a two-dimensional space with A diagonal, having eigenvalues zero and two. Let x have coordinates one and i, and let y have coordinates one and one.

The spectral measure on the eigenvalue zero depends only on the first coordinates. Its cross term is the inner product of the first component of x with the first component of y. The measure on two depends only on the second coordinates and may be complex because of i.

For the symbol f with f of zero equal to seven and f of two equal to minus one, the integral of f against the cross measure equals the matrix element of the diagonal operator with entries seven and minus one.

The diagonal measures alone did not visibly contain that complex cross term. Polarization recovered it without choosing any basis as part of the construction.

## Extension from continuous to measurable symbols

The extension from continuous to bounded Borel functions needs a limiting argument. A bounded Borel function can be approximated in an L-one sense against a suitable finite spectral measure, even when uniform approximation by continuous functions is impossible.

For one fixed pair x and y, we need to control four diagonal measures from the polarization formula. Take their sum. It is another finite positive measure and dominates all four. Approximate the Borel symbol against this single measure. The resulting integrals converge for the four pieces together.

When proving an identity involving finitely many vectors and finitely many symbols, use one dominating finite measure for all of them. The continuous identity can then pass to bounded Borel symbols through the integral estimate.

This method proves more than existence. It transports addition, multiplication, and adjoints from continuous functional calculus to the Borel calculus. Those identities depend on handling all matrix elements consistently, which is why the polarizing construction matters.

Notice the strength and the limitation of the approximation. L one convergence depends on the selected measures. It does not imply uniform convergence of the symbols, and it need not imply convergence in operator norm. The operator-level conclusions follow from separate bounds and uniqueness of matrix elements.

## What happens at an atom

Suppose x is an eigenvector with eigenvalue c. The scalar measure mu sub x is concentrated entirely at c, with total mass equal to the squared norm of x.

Integrating f against that measure gives f of c times the squared norm of x. The same polarization calculation implies that f of A sends x to f of c times x.

By contrast, for the multiplication operator on the interval with Lebesgue measure, a single point has zero spectral mass for every vector. Changing f at one such point does not change f of A.

These two cases explain why the Borel calculus is determined by how all scalar spectral measures see a function, rather than by bare pointwise equality on a formal parameter set.

## The bridge to multiplication models

We now have a strong dictionary. A vector supplies a positive measure. Two vectors supply a complex measure. A bounded Borel function supplies an operator whose matrix elements are the integrals of that function against the cross measures.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Given spectral projections `E(B)`, define the finite positive measure `mu_x(B) = <x,E(B)x>` and the complex cross measure `mu_{x,y}(B) = <x,E(B)y>`. Polarization reconstructs the cross measure as a complex linear combination of four diagonal measures. The spectral integral `f(A)` is specified weakly by `<x,f(A)y> = integral f d mu_{x,y}`. The quoted `pair` API takes normal operators and symbols on their complex spectrum; the self-adjoint real-spectrum construction transports it to `R`.

**Lean bridge (verbatim source declaration headers).**

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/PVM.lean` - `specDiag`:

```lean
noncomputable def specDiag (κ' : spectrum ℂ a → ℝ) (ξ : H) : Measure ℝ :=
```

The scalar diagonal measure is the push-forward of a continuous-calculus representation measure along the measurable spectral coordinate.

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean` - `pair`:

```lean
noncomputable def pair (f : spectrum ℂ a → ℂ) (ψ ξ : H) : ℂ :=
```

The off-diagonal pairing is constructed from four diagonal integrals. The displayed declaration is the construction of scalar matrix elements, before their representation by a bounded operator.

`ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Polarization.lean` - `pair_of_continuous`:

```lean
theorem pair_of_continuous (f : C(spectrum ℂ a, ℂ)) (ψ ξ : H) :
    pair ha (fun x => f x) ψ ξ = ⟪ψ, cfcHom ha f ξ⟫_ℂ :=
```

For continuous symbols, the polarized integral equals the matrix element of continuous functional calculus. The bounded Borel extension uses approximation and continuity.

**Scope:** The excerpts are declaration headers, not complete proof bodies. Their enclosing modules supply scalar types, normality/self-adjointness assumptions, and typeclass instances. The prose derives the mathematical statements and does not claim that all of the pedagogical arguments have separate local Lean theorems.
