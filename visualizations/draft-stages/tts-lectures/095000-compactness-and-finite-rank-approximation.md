# 095000 — Compactness and finite-rank approximation

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `072000` infinite-dimensional Hilbert examples, `082000` spectral cutoffs, `095000` begins the compact ideal unit. **Next:** `096000` approximation numbers and singular-value sequences.

<!-- BEGIN SPOKEN LECTURE -->

# Why some infinite-dimensional operators behave like matrices

Imagine an instrument that accepts an infinite list of numbers and produces another infinite list. Each input coordinate is an independent direction. If we could only keep the first ten directions, how much of the instrument's output would we lose?

For some operators, the answer depends dramatically on which ten directions we choose. For others, a carefully chosen finite collection of directions captures almost everything, with a guaranteed error even for the worst possible unit input. Compact operators are precisely the bounded operators for which we can make that error arbitrarily small using finite-dimensional output spaces, when we work between Hilbert spaces.

That statement is useful because it tells us when an infinite-dimensional problem can genuinely be approximated by finite matrices. Let's see what it means with one operator that works and one that does not.

## An infinite diagonal instrument

Our input and output space will be ell two: infinite sequences whose squared entries have a finite sum. The norm of a sequence is the square root of that sum. Every standard coordinate vector has norm one, and two different coordinate vectors are perpendicular.

First consider the identity operator. It sends every sequence to itself. Suppose we keep only the first N output coordinates and discard the rest. For a particular square-summable input, the discarded tail eventually becomes small. But there is always an input concentrated entirely in coordinate N plus one. For that input, our finite-coordinate approximation misses everything. The error is one, regardless of how large N becomes.

Now consider a different operator, D. It multiplies coordinate number one by one, coordinate number two by one half, coordinate number three by one third, and generally coordinate number n by one over n.

If we keep the first N output coordinates of D and discard the rest, every discarded coefficient is at most one over N plus one. Consequently, for any unit input at all, the discarded output has norm at most one over N plus one. And the input concentrated in coordinate N plus one achieves that bound exactly.

So our worst-case error tends to zero. Ten coordinates give an error of one eleventh. A hundred coordinates give one over a hundred and one. We can choose a finite number of coordinates that meets any positive error tolerance.

That difference between the identity and D is the central picture behind compactness. The identity preserves infinitely many independent unit directions at full size. D compresses the higher directions more and more strongly.

## The formal meaning of compact

Let's define what we have been seeing.

An operator is bounded if there is one constant that bounds its output norm by that constant times the input norm. Boundedness prevents unlimited amplification of unit inputs. Both the identity and D are bounded, with operator norm one.

Compactness asks for more. Take every input vector of norm at most one and look at the entire set of outputs. An operator is compact when that output set has compact closure. In a Hilbert space, this means that whenever we choose a bounded sequence of inputs, some subsequence of their outputs converges in norm.

Why is the sequence formulation helpful? Because we can test the identity immediately. Feed it the first standard basis vector, then the second, then the third, forever. Every output has norm one. Any two different outputs are distance square root of two apart, so no subsequence can converge. The identity is not compact on infinite-dimensional ell two.

Don't confuse compactness with sending a single chosen sequence to a convergent sequence. We need a convergent output subsequence for every bounded input sequence. It is a uniform kind of finite-dimensional behavior.

## Start with operators of finite rank

An operator has finite rank when all its outputs lie in one fixed finite-dimensional subspace. Suppose the range fits in a plane, even if the input has infinitely many dimensions.

A bounded collection of inputs produces a bounded collection of outputs. But a bounded sequence in a finite-dimensional plane always has a convergent subsequence. This is the finite-dimensional Bolzano-Weierstrass property. Therefore every bounded finite-rank operator is compact.

The word bounded is important in that statement. We are talking about continuous linear maps between Hilbert spaces. A finite-dimensional range alone would not make a discontinuous linear map a compact operator.

Our truncations of D are bounded finite-rank operators. Each one retains only a finite number of diagonal coefficients, and their operator-norm errors approach zero. Can we conclude that D itself is compact? Yes, provided we establish one more fact: an operator-norm limit of compact operators is compact.

## Why the type of convergence is crucial

Recall our two approximations. The coordinate projections onto the first N directions converge to the identity on every fixed vector in ell two. This is called strong operator convergence. Yet the worst-case error remains one, because the neglected direction can change with N.

For D, in contrast, the worst-case error goes to zero. This is operator-norm convergence. It uses one error bound that works simultaneously for every unit input.

Compactness survives the second kind of limit, but not the first. Let's see the reason without getting buried in subsequences.

Suppose T is very close in operator norm to a compact operator C. Because C is compact, the outputs C produces from the unit ball can be covered by finitely many small balls in the output Hilbert space. In ordinary language, there are finitely many representative output vectors, and each C output is near at least one representative.

Now compare T to C. A uniform operator-norm bound says every T output lies close to its corresponding C output. Therefore those same finitely many representatives also approximate every T output, with a slightly larger error.

If we can choose C arbitrarily close to T, we can make such finite approximations at every desired accuracy. In a complete output Hilbert space, that establishes compactness.

This argument would collapse under strong convergence, because strong convergence lets the bad input depend on the approximation index. The identity projections are the precise counterexample.

## The converse: compactness gives finite-dimensional approximations

We have established that finite rank implies compactness, and that operator-norm limits of compact operators are compact. Now ask the more interesting question: does every compact operator admit finite-rank approximations in operator norm?

Between Hilbert spaces, the answer is yes.

Take a compact operator T and choose a positive error tolerance, say one hundredth. Its outputs on the unit ball form a set with compact closure. Such a set can be covered by finitely many balls of radius one hundredth.

Choose the finitely many centers of those balls and form their linear span. Call this finite-dimensional output subspace W. Every output T x from the unit ball is close to at least one point of W.

Because we are in a Hilbert space, we can orthogonally project onto W. An orthogonal projection gives the closest point in W to any output. So projecting T x onto W makes an error no larger than the distance to the nearest chosen center.

Define a new operator by first applying T and then projecting its output onto W. This new operator has finite rank, because every result lies in W. And its operator-norm distance from T is at most our chosen error tolerance.

Repeat with a smaller tolerance. We obtain finite-rank operators converging to T in operator norm.

Put the two directions together. A bounded operator between Hilbert spaces is compact if and only if it is an operator-norm limit of finite-rank operators.

Notice what the proof did not require. We did not need an eigenvector basis for T. We did not need T to be self-adjoint. We only used compactness of the output set and the Hilbert-space projection theorem.

## What survives composition

Suppose T is compact. Put a bounded operator B before T and a bounded operator A after T, with compatible input and output spaces. The combined operator, written A T B and applied from right to left, is also compact.

The reason follows directly from sequences. B sends bounded inputs to bounded vectors. T turns some subsequence of those vectors into convergent outputs. A is continuous, so it preserves convergence.

That is why compact operators form a two-sided operator ideal. Sums and scalar multiples of compact operators are compact as well. In this setting, the compact operators form a norm-closed space under the ordinary operator norm.

## What we gained

Return to D, the operator with coefficients one over n. It has infinitely many nonzero output directions, so it is not finite rank. But its finite-rank truncations approximate it in operator norm, and that makes it compact.

The identity is bounded but not compact. Its finite-coordinate truncations approach it strongly, yet never approach it in operator norm.

The distinction is practical. Compactness says we can capture the action on every unit input to any desired accuracy with finitely many output directions. It is the justification for applying finite-dimensional approximation methods to a particular class of infinite-dimensional operators.

For compact operators, we can go a step further. We can rank the important directions according to how much the operator stretches them. Those magnitudes are its singular values, and they tell us exactly how much error the best finite-rank approximation must leave behind.

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
