# 141000 — How much can a distance-only gap say

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `031000`, `062000–071000`, `107000–110000`, `126000`. **Next:** `142000`.

<!-- BEGIN SPOKEN LECTURE -->

# How much can a distance-only gap say?

We have finished the free-beam calculation, where a low cluster and a high cluster lie on opposite sides of a large spectral gap. The geometry was favorable: all the trial values were below all the complementary values. But what if the spectral sets are separated by a positive distance without being ordered?

This is the question Davis and Kahan raise in Question ten point one. It asks how sharply we can control the angle of a trial subspace using a residual if we know only that every trial spectral value is at least delta away from every complementary exact spectral value.

The source points to two earlier difficulties. A single scalar denominator is easy to control. A whole matrix of denominators can behave differently depending on the operator norm we choose. Today we will prove the easy result, disprove a tempting stronger one, and explain the general estimate that survives.

## The compressed equation returns

Let E map the trial coordinate space isometrically into our Hilbert space. Let F one map the exact complementary spectral space into that Hilbert space. The trial compression is A zero, and the exact complementary compression is Lambda one.

Form the residual by applying the original operator to E and subtracting E times A zero. Project that residual onto the exact complementary space. Because that space reduces the exact operator, the projected residual equals Lambda one times F one star E, minus F one star E times A zero.

Call X the map F one star E and C the projected residual. We obtain the Sylvester equation Lambda one X minus X A zero equals C.

The singular values of X are the directed principal sines from the trial space toward the exact complementary subspace. Thus a bound for X gives an angle estimate. And since F one star is a contraction, the norm of C cannot exceed the residual norm in any compatible invariant norm.

So everything reduces to an inverse estimate for this Sylvester equation.

## Pairwise separation solves the scalar equations

Start with finite-dimensional self-adjoint blocks. Choose orthonormal eigenbases of Lambda one and A zero. Write their eigenvalues as lambda i and alpha j.

In those coordinates, the Sylvester equation says that lambda i minus alpha j, multiplied by the entry X i j, equals C i j. If the two spectra have pairwise distance at least delta, then every denominator has absolute value at least delta.

Thus each entry of X has absolute value at most the corresponding entry of C divided by delta. That immediately proves a Frobenius estimate: square all entries, add, and take the square root. Delta times the Frobenius norm of X is no greater than the Frobenius norm of C.

This is the clean constant-one result. It remains valid even if the two spectra are wildly interlaced. The Frobenius norm is built from the sum of squared matrix entries in orthonormal bases, and the Sylvester operator acts diagonally on those matrix units.

For Hilbert–Schmidt operators in Hilbert space, the same argument is expressed by a spectral product measure or the Hilbert–Schmidt group representation. The essential point is unchanged: each spectral-pair frequency has multiplier whose absolute value is at least delta.

## Why operator norm is harder

Now attempt the same proof for operator norm. The inequality on each matrix entry is still true, but operator norm is not the maximum absolute entry. It depends on how entries cooperate when the matrix acts on a vector.

Entrywise multiplication by a bounded coefficient matrix is called a Schur multiplier. Its operator norm can exceed the largest absolute coefficient. That is exactly what happens when the inverse Sylvester operator divides entries by different signed spectral differences.

We can demonstrate the failure in two dimensions without approximation.

Take A to be the diagonal matrix with entries one and minus one. Take B to be the diagonal matrix with entries zero and two. Their spectra are one and minus one, and zero and two. Every pairwise spectral distance is at least one.

Choose X to be the symmetric matrix with rows three, minus three, and minus three, one. Compute A X minus X B. The result C has rows three, three, and three, minus three.

The operator norm of C is three times square root of two. The operator norm of X is two plus square root of ten. Since two plus square root of ten is larger, the proposed inequality norm of X no greater than norm of C, with delta equal to one, fails.

Yet the Frobenius comparison holds: X has squared Frobenius norm twenty-eight, while C has squared Frobenius norm thirty-six. No contradiction occurs because these norms use different aggregation rules.

This example proves that the constant-one operator-norm estimate cannot follow from pairwise spectral distance alone.

## Ordered separation changes the proof

Suppose instead every eigenvalue of Lambda one lies at least delta above every eigenvalue of A zero. Then we can use a single exponential integral.

The solution X is the integral, from zero to infinity, of the semigroup generated by negative Lambda one on the left and positive A zero on the right, acting on C. In other words, every component decays with its spectral difference.

The entire operator integrand is bounded by the norm of C times exponential decay at rate delta. Integrate that scalar bound and obtain one over delta. This proof works for operator norm and compatible ideal norms because we estimate the whole product of operators, not its entries separately.

The precise improvement comes from the order assumption. It provides a common direction of decay across every spectral pair. Mere distance separation does not.

## What survives without order

For self-adjoint spectra that are disjoint with a positive distance, the inverse Sylvester operator can instead be represented using oscillatory unitary groups and a Fourier kernel. The scalar kernel reproduces the reciprocal of a frequency away from the forbidden gap around zero.

Its integrable norm yields a general operator-norm estimate with a larger constant, commonly expressed as pi over two divided by delta in the separated self-adjoint setting addressed by the repository's Fourier argument.

The proof is more delicate than entrywise division. One must construct a Fourier representation of the reciprocal multiplier on the allowed frequency set and bound the integral of conjugations by unitary groups. For unbounded self-adjoint blocks, one also needs the domain-aware Sylvester identity before invoking the formula.

This does not say the constant pi over two is necessarily optimal for every restricted spectral configuration. It gives a general guarantee where the naive constant one fails. If more is known about the arrangement of spectra, stronger bounds can be recovered.

One useful intermediate result involves low rank. If C has rank r, its Frobenius norm is at most square root of r times its operator norm. Combining that with the Frobenius Sylvester estimate and the fact that operator norm is at most Frobenius norm gives delta times the operator norm of X no greater than square root of r times the operator norm of C. It may be weaker than the Fourier bound for large r, but it is elementary and sometimes useful when r is small.

## Read Question ten point one precisely

The historical question asks how sharp a residual-to-angle theorem can be under distance-only spectral separation. The source's Theorem six point two already supports constant one for Hilbert–Schmidt control. The broader operator-norm story requires different techniques and constants. Our two-by-two example rules out a universal constant-one result in operator norm.

We must also specify which angle we control. X equals the exact complementary projection composed with the trial inclusion. It records directed sines. If the trial and exact subspaces have unequal dimensions or unmatched defects, an ambient projection-gap conclusion requires more information than one directed Sylvester equation.

Thus four questions accompany any proposed distance-only estimate. Which spectral sets are compared? Does their separation have a common order? Which norm measures the residual and angle? And is the target a directed angle or an ambient angle?

These distinctions lead directly into the next open problem. With two subspaces we could describe all relative geometry using a cosine–sine block. With three reducing subspaces, several off-diagonal overlaps interact, and a pairwise gap theorem may fail to capture their joint structure.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For finite-dimensional self-adjoint blocks \(A,B\) with \(\operatorname{dist}(\sigma(A),\sigma(B))\ge\delta>0\), and \(AX-XB=C\), the spectral matrix-unit decomposition proves
\[\delta\|X\|_{S_2}\le\|C\|_{S_2}.\]
The same constant one is not generally valid in operator norm. A direct witness is
\[
A=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
B=\begin{pmatrix}0&0\\0&2\end{pmatrix},\quad
X=\begin{pmatrix}3&-3\\-3&1\end{pmatrix},\quad
C=AX-XB=\begin{pmatrix}3&3\\3&-3\end{pmatrix},
\]
with \(\delta=1\), \(\|X\|=2+\sqrt{10}>3\sqrt2=\|C\|\). Ordered gaps give the stronger norm-generic constant-one estimate through semigroup decay; pairwise separation admits a Fourier-based larger constant under the precise self-adjoint hypotheses. The historical Question 10.1 is an investigation of the sharpest conclusion from the weaker data, not a claim that its full optimal answer is supplied by the transcription.

## Exact Lean declaration excerpts


**`hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct`.** Disjoint *pairwise* self-adjoint spectra with gap delta and Hilbert–Schmidt residual membership yield Hilbert–Schmidt solution membership and the constant-one estimate.

`DavisKahan/Sources/DavisKahan1970/Sylvester/HilbertSchmidtPairwise.lean` — `hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct` (exact declaration header; proof body omitted):

```lean
theorem hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    {X C : F →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C)
    (hC : approximationNumberEnergy C ≠ ⊤) :
    approximationNumberEnergy X ≠ ⊤ ∧
      δ * ContinuousLinearMap.hilbertSchmidtNorm X ≤ ContinuousLinearMap.hilbertSchmidtNorm C :=
```


**`opNorm_sylvester_le_of_pairwiseSpectrumGap`.** The source proves an operator-norm estimate with factor square root of rank under the additional finite-rank residual hypothesis.

`DavisKahan/Sources/DavisKahan1970/Sylvester/OperatorNormEstimate.lean` — `opNorm_sylvester_le_of_pairwiseSpectrumGap` (exact declaration header; proof body omitted):

```lean
theorem opNorm_sylvester_le_of_pairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →ₗ.[ℂ] E}
    {B : F →ₗ.[ℂ] F}
    {X C : F →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : PairwiseSpectrumGap A B δ)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C)
    {r : ℕ} (hRank : C.rank ≤ (r : Cardinal)) :
    δ * ‖X‖ ≤ ‖C‖ * Real.sqrt r :=
```


**`sharp52_constant_one_too_small`.** The actual real two-by-two witness refutes the constant-one operator-norm conclusion under pairwise distance only; it does not refute the Hilbert–Schmidt estimate.

`DavisKahan/Sources/DavisKahan1970/Sylvester/OperatorNormEstimate.lean` — `sharp52_constant_one_too_small` (exact declaration header; proof body omitted):

```lean
theorem sharp52_constant_one_too_small :
    ‖sharpC52.toContinuousLinearMap‖ < 1 * ‖sharpX52.toContinuousLinearMap‖ :=
```
