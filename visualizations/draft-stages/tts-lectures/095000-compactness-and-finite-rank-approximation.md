# 095000 — Compactness and finite-rank approximation

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `072000` infinite-dimensional Hilbert examples, `082000` spectral cutoffs, `095000` begins the compact ideal unit. **Next:** `096000` approximation numbers and singular-value sequences.

<!-- BEGIN SPOKEN LECTURE -->

# When infinitely many directions become manageable

An infinite-dimensional Hilbert space can contain a sequence of mutually perpendicular unit vectors. No two of those vectors get closer than the square root of two. Consequently, its closed unit ball is not compact. Yet some operators turn that noncompact ball into a set whose closure is compact. Those operators are called compact operators.

Today we will define compactness carefully, prove that finite-rank maps are compact, and establish the converse approximation principle: on Hilbert spaces, a bounded operator is compact exactly when it can be approximated in operator norm by finite-rank maps.

This theorem explains why finite matrix methods remain useful in infinite dimensions. But it also tells us precisely when that usefulness stops.

## What compactness asks

Let T be a bounded linear map from a Hilbert space E to a Hilbert space F. The operator T is compact if the image of the closed unit ball has compact closure. Equivalently, whenever we choose a bounded sequence of input vectors, their output vectors have a norm-convergent subsequence.

We need to distinguish this from ordinary boundedness. A bounded operator merely sends bounded inputs to bounded outputs. Compactness supplies convergent subsequences of outputs, even if the original inputs have no convergent subsequence.

Consider ell two, the space of square-summable sequences, with standard unit vectors e one, e two, and so on. The identity operator maps each e n to itself. These outputs have no norm-convergent subsequence, so the identity is not compact.

Now take a diagonal operator D that multiplies the n-th coordinate by one divided by n. It maps e n to one over n times e n, which tends to zero. That observation alone is not a complete proof of compactness, because we must control every bounded sequence, not only the basis vectors. We will get that stronger control from finite-rank approximation.

## Why finite rank guarantees compactness

An operator has finite rank if all its outputs lie in a fixed finite-dimensional subspace. Suppose T has finite rank and the input sequence is bounded. Since T is bounded, its outputs form a bounded sequence in that finite-dimensional range.

The finite-dimensional Bolzano–Weierstrass theorem provides a convergent subsequence. The range is closed, so its limit belongs to the range. Thus T is compact.

The argument uses two ingredients: finite-dimensional balls are compact, and a bounded map sends a bounded set into a bounded set. It applies equally to real and complex Hilbert spaces.

What about the converse? We should not expect a compact operator to have literally finite rank. Our diagonal D has infinitely many nonzero diagonal entries, hence infinitely dimensional range. Nevertheless, its small tail should be approximable by zero.

## Truncating the diagonal example

Define D sub N to retain only the first N diagonal entries of D and set all later entries to zero. This operator has rank N.

For any unit vector x, the squared norm of D x minus D sub N x is the sum over n greater than N of the squared absolute values of x n divided by n squared. Every denominator is at least N plus one, so the norm of the difference is at most one divided by N plus one.

Taking x equal to e sub N plus one shows the bound is exact. Therefore the operator norm of D minus D sub N equals one divided by N plus one, which tends to zero.

Every D sub N is compact. We will soon prove that an operator-norm limit of compact operators is compact. Thus D is compact, as promised.

Now replace the diagonal coefficients by ones. The corresponding truncations are the projections P sub N onto the first N coordinates. For each fixed x in ell two, P sub N x tends to x, because the tail of a square-summable sequence tends to zero in norm. But the operator norm of identity minus P sub N remains one: applying it to e sub N plus one proves that fact.

This is the distinction between strong convergence and operator-norm convergence. Strong convergence controls one fixed vector at a time. Operator-norm convergence controls every unit vector by a single bound.

## Compact operators form an operator-norm closed class

Suppose T sub n are compact and converge in operator norm to T. We want to show T is compact.

Take any bounded sequence x sub j. First choose a compact approximation T sub n so close to T that its output error on every x sub j is small. Because T sub n is compact, its output sequence has a convergent subsequence.

There is a subtlety: the subsequence may depend on n. To handle every desired accuracy, select successively smaller errors, passing to subsequences each time, and then take a diagonal subsequence. On that diagonal subsequence, the outputs of T are Cauchy: they are uniformly close to the outputs of a compact approximation, which are Cauchy sufficiently far along.

Completeness of F supplies a limit. Hence T is compact.

There is also a useful total-boundedness proof. Compact images of the unit ball have finite epsilon-nets. If T is uniformly close to one such compact operator, the same finite collection of centers provides a slightly larger epsilon-net for the image under T. This works at every positive accuracy, establishing precompactness.

The second proof highlights why the convergence must be in operator norm. Only then does one epsilon control all unit vectors at once.

## The converse: compactness produces finite-rank approximations

Assume T is compact. Fix a positive error epsilon. The closure of the image of the unit ball is compact, so finitely many small balls cover it. Choose centers y one through y m in F, each within epsilon of some relevant outputs.

Let W be the finite-dimensional span of those centers and let Q denote the orthogonal projection onto W. For every unit vector x, the output T x is within epsilon of a center in W. Because Q T x is the nearest point in W, the distance from T x to Q T x is at most epsilon.

Take the supremum over all unit vectors. We get that the operator norm of T minus Q T is at most epsilon.

Since Q T has range in W, it has finite rank. As epsilon can be made arbitrarily small, T is an operator-norm limit of finite-rank maps.

Notice how the projection theorem does the work. We do not have to choose coordinates in the entire infinite-dimensional space. We only need a finite-dimensional output space that approximates T's image of the unit ball.

Combining both directions proves the equivalence.

## Compactness survives multiplication

If T is compact and A and B are bounded maps of compatible types, then A T B is compact.

To see this, start with any bounded sequence of inputs. Applying B gives a bounded sequence. Compactness of T provides a subsequence whose T B outputs converge in norm. Continuity of A preserves that convergence.

This is why compact operators form a two-sided operator ideal: composing them on either side with arbitrary bounded operators stays within the compact class.

Likewise, sums and scalar multiples of compact operators are compact. And because the class is operator-norm closed, it is a complete normed space with the operator norm.

## What compactness buys us later

For a compact operator T, the modulus of T is positive and compact. Its positive eigenvalues can be listed with multiplicities, descending toward zero. Those eigenvalues are the nonzero singular values of T.

For a noncompact bounded operator, we can still define approximation numbers, but they need not tend to zero. The identity is the simplest example: no finite-rank approximation gets within operator-norm distance less than one.

We will next measure that distance at every prescribed rank. The resulting sequence will play the role of singular values even before we assume compactness.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For Hilbert spaces E and F and a bounded operator T, compactness is equivalent to: for every positive epsilon there exists a finite-rank R with operator norm of T minus R less than epsilon. The forward implication uses finite epsilon-nets for the image of the unit ball and orthogonal projection onto the span of their centers. The reverse implication uses operator-norm closedness of compact operators. For D on ell two with diagonal 1/n, truncations satisfy norm of D minus D sub N equal to 1/(N+1). The identity's finite coordinate projections converge strongly but not in operator norm.

### Actual Lean source declarations

`ForTauCeti/Analysis/OperatorIdeal/Family/CompactOperator.lean` — `mem_finiteSubmodule_compactOperatorIdealFamily` (declaration header, proof omitted):

```lean
theorem mem_finiteSubmodule_compactOperatorIdealFamily {A : E →L[𝕜] F} :
    A ∈ ((compactOperatorIdealFamily.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule ↔
      IsCompactOperator A := by
```

`ForTauCeti/Analysis/OperatorIdeal/Family/CompactOperator.lean` — `gauge_compactOperatorIdealFamily_of_isCompactOperator` (declaration header, proof omitted):

```lean
theorem gauge_compactOperatorIdealFamily_of_isCompactOperator
    {A : E →L[𝕜] F} (hA : IsCompactOperator A) :
    (compactOperatorIdealFamily.{u, v, w} 𝕜).gauge A = ‖A‖ₑ := by
```

**Type and hypothesis map.** The carrier is exactly the compact maps; `E →L[𝕜] F` permits rectangular source and target. For members, the compact-ideal extended gauge is the operator `enorm`.

These are exact excerpts from the supplied DKPS source snapshot. The mathematical narration develops its arguments independently; citing these declarations does not assert that the narrated intermediate proof has been separately compiled in Lean. Where the current declaration lives in `ForTauCeti`, its placement does not imply the mathematical result originated outside the DKPS project.
