# 128000 — Spectral cutoff and finite-rank source lemmas

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `082000`, `095000`, `096000`, `099000`, `127000`. **Next:** `129000`, a complete original-paper proof reconstruction.

<!-- BEGIN SPOKEN LECTURE -->

# Spectral cutoff and finite-rank source lemmas

Some proofs in perturbation theory look like finite matrix arguments even when the theorem concerns an infinite-dimensional Hilbert space. The missing work is often hidden in a phrase such as, pass to finite-rank cutoffs. Davis and Kahan's source includes results that justify these passages. We will study two of them: convergence of singular-value data under finite-dimensional approximation, and Lemma six point three, which says that almost saturating a leading singular-value energy budget forces an unwanted block to be small.

These are analytic proof obligations. Their hypotheses determine when one may replace an infinite-dimensional operator with a finite matrix calculation and return to the original operator.

## How a basis cutoff works

Choose an orthonormal basis of a Hilbert space. For each finite set of basis indices, take the orthogonal projection onto their span. As the finite set grows, its projection converges strongly to the identity.

Strong convergence means that for each fixed vector x, the length of the omitted tail tends to zero. It does not mean the operator norm of the difference from the identity tends to zero. If the Hilbert space is infinite dimensional, every finite-rank projection leaves some unit vector untouched in its orthogonal complement. On that vector, identity minus the projection still has norm one.

This distinction prevents us from invoking operator-norm continuity without proof.

## Approximation numbers as finite-rank measurements

For a bounded operator T, its approximation number at index n is the infimum of the operator norm error over approximants of rank at most n, using zero-based indexing. In finite dimensions these are the usual singular values in descending order. In Hilbert space they provide a useful extension even when T is not compact.

Compose T on the right with an increasing finite-basis projection. The resulting operator has finite rank. The source proves that each fixed approximation singular value of these cutoffs converges to the corresponding approximation singular value of T.

The proof depends on a min–max characterization, not on an invalid assertion of operator-norm convergence of the finite sections. Every cutoff is a contraction, so its approximation numbers never exceed those of T. To prove convergence from below, select a nearly maximizing finite-dimensional test space for the min–max problem. Strong convergence is uniform on that fixed finite-dimensional space, allowing the cutoff to recover its near-optimal lower bound.

The dimension in that argument is fixed before the cutoff grows. This order of quantifiers is important.

## Compactness gives a stronger statement

If T is compact, strong convergence of finite-rank projections applied on the output side upgrades to operator-norm convergence for T. The reason is that T maps the unit ball to a set with compact closure, and strong convergence is uniform on compact sets.

With input cutoffs, apply the same argument to the adjoint of T. In a Hilbert space the adjoint of a compact operator is compact, so both sides can be controlled.

For an arbitrary bounded noncompact T, this upgrade is false. A cutoff of the identity on an infinite-dimensional space remains at operator-norm distance one from the identity, no matter how many basis vectors we include.

Nevertheless, each fixed approximation number can still be recovered through the min–max route. Compactness and fixed-index singular-value convergence are different statements.

## Recover the square energy

The Hilbert–Schmidt energy is the sum of the squares of all approximation singular values, interpreted in the extended nonnegative reals when necessary.

For a finite-rank cutoff this is a finite sum and equals the sum of squared lengths of the operator applied to a suitable finite orthonormal basis. As the cutoffs increase, the supremum of their energies equals the full operator energy.

Why is the supremum legitimate? The projection cutoffs give no larger energy than the full operator. Conversely, every finite set of coordinate contributions is eventually included, and the source's basis-energy identity shows that no contribution is permanently missed.

The extended-valued formulation is helpful: it states the equality even when the operator is not Hilbert–Schmidt. In that case both sides can grow without finite bound.

## State the finite-rank leakage problem

Now take a bounded operator K between two Hilbert spaces. Let P be an orthogonal projection on the source and Q a projection on the target. Assume Q has rank at most a positive integer n.

The key block-invariance hypothesis is that K maps vectors in the range of P into the range of Q. In operator form, K P equals Q K P.

This is weaker than the tempting condition K P equals Q K. The latter would also force K to have no leakage from P perpendicular into Q, making the intended conclusion trivial. The paper assumes only the former.

We want to bound the leakage operator that first restricts to P perpendicular, applies K, and then projects into Q. It is Q K times one minus P.

## What is nearly maximal singular-value energy?

For any operator T, take the sum of squares of its first n approximation singular values. Call this its leading n energy.

Suppose the leading n energy of K P is greater than the leading n energy of K minus eta squared, where eta is positive. In words, the selected source block almost captures all the leading n energy available in K.

Lemma six point three says that the leakage from P perpendicular into Q has operator norm less than eta.

This is an implication with a numerical deficit. It is not a statement that a large singular value alone forces a small cross block. We need near-saturation of the entire leading n square-energy budget.

## Derive the leakage inequality

Form L equal to Q K. Since its range lies in Q, L has rank at most n. Split the source into the orthogonal pieces P and P perpendicular. The Hilbert–Schmidt square energy of L splits exactly into the square energy of L P plus that of L times one minus P.

The block-invariance hypothesis identifies L P with K P. Therefore the energy of L is the energy of K P plus the energy of the leakage operator.

Left compression by Q cannot increase any approximation singular value. Hence the leading n energy of L is at most that of K. Since L has rank at most n, its total Hilbert–Schmidt energy is already its leading n energy.

Subtract the near-saturation inequality. The leakage's squared Hilbert–Schmidt norm is strictly less than eta squared.

Finally, the operator norm of any operator is at most its Hilbert–Schmidt norm. Thus the leakage operator has norm strictly less than eta. This completes the proof.

Notice where the rank bound was used: to identify the total square energy of Q K with its first n terms. Where was positive n used? To ensure the leading prefix includes the top singular value and therefore dominates the operator norm. Neither assumption can be dropped casually.

## A two-by-two witness

Take P and Q both as projection onto the first coordinate axis. Let K have first row three and b, and second row zero and zero.

Then K P maps the first axis into Q, so block invariance holds. Its leading one energy is nine. The full K has one nonzero singular value equal to the square root of nine plus b squared, so its leading one energy is nine plus b squared.

The leakage Q K times one minus P has operator norm equal to the absolute value of b. The near-saturation hypothesis requires nine greater than nine plus b squared minus eta squared, equivalently b squared less than eta squared. The conclusion is exactly the same strict inequality on the leakage.

This example shows that the eta threshold is sharp in the natural scaling.

## Where the lemma enters the source

A finite-rank spectral selection argument may control how much of an operator's leading singular-value energy is captured by a chosen subspace. Lemma six point three converts that energy information into an operator-norm bound on the unwanted cross block.

The Hilbert-Schmidt Pythagorean identity can be proved in complex Hilbert space, and its real version follows by complexification with preservation of the squared norm. Other ideal norms need their own dominance argument.

For unbounded operators, finite spectral cutoffs also enforce domain legality. One first proves identities on bounded spectral pieces and then passes to a limit in the topology justified by the hypotheses. That limiting topology may be strong convergence, graph-norm convergence on the domain, or an ideal-gauge convergence, and these are not interchangeable.

## Close

We now have two distinct ways to pass from infinite Hilbert-space data to finite calculations: fixed-index approximation singular values under strong basis cutoffs, and quantitative control of unwanted finite-rank blocks from near-maximal square energy.

These lemmas will remain available whenever an infinite-dimensional proof needs to justify an infinite-dimensional approximation.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)


For a basis cutoff \(P_s\) and zero-based approximation singular values \(a_n\), the source proves
\[a_n(TP_s)\longrightarrow a_n(T)\quad\text{for each fixed }n,\]
without claiming \(\|TP_s-T\|\to0\) for every bounded operator. It also identifies Hilbert–Schmidt square energy with the supremum over finite-basis cutoff energies.

For Lemma 6.3 let \(P,Q\) be orthogonal projections, \(0<n\), \(\operatorname{rank}Q\le n\), and require exactly \(KP=QKP\). If
\[\sum_{j<n}a_j(KP)^2>\sum_{j<n}a_j(K)^2-\eta^2,\]
then \(\|QK(I-P)\|<\eta\). Replacing \(KP=QKP\) by \(KP=QK\) would force a zero leakage block and change the source result.


### Exact Lean declaration excerpts


`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtBasis.lean` — `approximationSingularValue_cutoff_tendsto` (exact declaration header; proof body omitted):

```lean
theorem approximationSingularValue_cutoff_tendsto {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) (n : ℕ) :
    Tendsto
      (fun s : Finset ι => ((A ∘L basisProjection b s).singularValue n : ℝ))
      atTop (𝓝 ((A.singularValue n : ℝ))) :=
```


`DavisKahan/Sources/DavisKahan1970/Ideals/HilbertSchmidtBasis.lean` — `approximationNumberEnergy_eq_iSup_cutoff` (exact declaration header; proof body omitted):

```lean
theorem approximationNumberEnergy_eq_iSup_cutoff {ι : Type*}
    (b : HilbertBasis ι 𝕜 F) (A : F →L[𝕜] E) :
    approximationNumberEnergy A =
      ⨆ s : Finset ι,
        approximationNumberEnergy (A ∘L basisProjection b s) := by
```


`DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean` — `lemma6_3_approximationNumber_leakage_complex` (exact declaration header; proof body omitted):

```lean
theorem lemma6_3_approximationNumber_leakage_complex
    (K : E' →L[ℂ] F')
    (P : Submodule ℂ E') [P.HasOrthogonalProjection]
    (Q : Submodule ℂ F') [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (_hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear : approximationEnergy (K ∘L P.starProjection) n >
      approximationEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
```



**Mapping.** `basisProjection` is the orthogonal projection onto a finite subset of a Hilbert basis; the convergence is indexed over finite sets ordered by inclusion. `approximationEnergy` is a prefix square sum of the zero-based singular values. The leakage theorem explicitly requires `hKP`, `hrankQ`, a positive integer `n`, and the strict near-energy inequality `hnear`; these are not derived from finite dimensionality alone.

