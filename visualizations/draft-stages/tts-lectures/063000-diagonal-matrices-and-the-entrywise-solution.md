# 063000 — Diagonal matrices and the entrywise solution

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `026000` finite spectral theorem; `031000` spectral separation; `057000` Frobenius norm; `062000` scalar Sylvester equation. **Next:** Kronecker sums and Sylvester invertibility.

<!-- BEGIN SPOKEN LECTURE -->

# Solve every spectral block, then put the answer together

When A and B are diagonal in orthonormal eigenbases, the unknown matrix coefficient between eigenvalues a and b is multiplied by a minus b.

For diagonal coefficient matrices, the Sylvester equation can be solved entry by entry. The cross-eigenvalue differences determine uniqueness, the available solutions when spectra overlap, and a sharp Frobenius estimate under positive separation.

Along the way, we will connect the entrywise formula to ordinary resolvents and to the coordinate-free language of spectral projections. The goal is to make the finite Sylvester inverse something we can derive rather than a formula we have to remember.

## Write the matrix equation in coordinates

Let A be a diagonal matrix with m diagonal entries, and B a diagonal matrix with n diagonal entries. Let X and C be rectangular matrices with m rows and n columns.

We want to solve A X minus X B equals C.

What is the entry in row i and column j of A X? Because A is diagonal, it is the i-th diagonal entry of A multiplied by the corresponding entry of X.

What about X B? Because B is diagonal, its entry in that position is the entry of X multiplied by the j-th diagonal entry of B.

Subtracting, the coefficient of X is the i-th eigenvalue of A minus the j-th eigenvalue of B.

Therefore the full matrix equation is equivalent to one scalar equation for every row and column: the spectral difference times the unknown entry equals the corresponding entry of C.

If every spectral difference is nonzero, the unique answer is obtained by dividing each entry of C by its spectral difference.

No matrix inverse of A or B is required. We invert the Sylvester operator by dividing in the product eigenbasis of its left and right actions.

## A complete two-by-two example

Let A have diagonal entries one and four. Let B have diagonal entries zero and three.

The difference associated with the first row and first column is one minus zero, which is one. For the first row and second column it is one minus three, which is negative two.

For the second row and first column it is four minus zero, which is four. And for the second row and second column it is four minus three, which is one.

Thus the matrix of denominators, read row by row, is one, negative two, four, one.

Let C have first row two, six and second row eight, ten.

Divide corresponding entries. The solution X has first row two, negative three and second row two, ten.

Let's verify directly. A X has first row two, negative three and second row eight, forty. X B has first row zero, negative nine and second row zero, thirty. Subtracting gives first row two, six and second row eight, ten, exactly C.

The check also fixes the order of multiplication. If we had written X A or B X instead, the denominators would be attached to the wrong row or column.

## Why uniqueness follows

Suppose X and Y both solve the same equation. Subtract their equations. The difference Z, defined as X minus Y, satisfies A Z minus Z B equals zero.

For every entry, the corresponding spectral difference times the entry of Z is zero. If all differences are nonzero, every entry of Z must vanish. Therefore X equals Y.

This is the entire uniqueness proof in diagonal coordinates.

Equivalently, the homogeneous Sylvester operator has trivial kernel. Since it acts on a finite-dimensional space of m times n matrix entries, injectivity implies surjectivity. But the explicit division formula already gives surjectivity constructively.

The proof works whether the spectra are ordered or interlaced. Only nonvanishing of every cross difference is needed for finite-dimensional existence and uniqueness.

## What if a denominator vanishes?

Suppose A has an eigenvalue three and B has an eigenvalue three. On the corresponding row and column, the equation becomes zero times an unknown entry equals the matching entry of C.

If that entry of C is nonzero, no solution exists. The left side can never produce it.

If the entry of C is zero, every choice of the corresponding entry of X satisfies that scalar equation. So the solution is not unique.

This gives a complete compatibility criterion in diagonal coordinates: every entry of C that joins equal eigenvalues must vanish. For all other entries, divide as usual. At positions joining equal eigenvalues, choose arbitrary values of X.

For repeated eigenvalues, one must count entire blocks, not just individual positions. Suppose a particular eigenvalue has multiplicity r in A and multiplicity s in B. The homogeneous solution has an arbitrary r-by-s block connecting the two corresponding eigenspaces. That contributes r times s degrees of freedom over the scalar field.

Summing those products over eigenvalues shared by A and B gives the dimension of the Sylvester operator's kernel.

This reveals precisely what goes wrong when the spectral separation hypothesis fails. The failure is localized to matching spectral blocks, and we can name both the obstruction to existence and the freedom in nonunique solutions.

## A sharp Frobenius estimate

Assume now that the eigenvalues of A and B are separated by a positive distance delta. That means every absolute spectral difference is at least delta.

For each entry, the solution formula gives the magnitude of X's entry at most the magnitude of C's entry divided by delta.

Square this inequality for each row and column, and add over all entries. The sum of squared magnitudes of X is at most one over delta squared times the corresponding sum for C.

These sums are the squares of the Frobenius norms. Taking square roots gives the bound: the Frobenius norm of X is at most the Frobenius norm of C divided by delta.

The constant one is sharp. To see it, take a right-hand side C that is zero everywhere except in one position where the spectral difference has the smallest absolute value delta. In that position, the solution is exactly C divided by that difference, so equality holds in the norm bound.

This sharp estimate depends on the fact that the Frobenius norm is the Euclidean length of the full list of matrix entries in orthonormal coordinates.

## Why this does not prove the same operator-norm bound

It is tempting to use the same argument for the ordinary operator norm. Every entry of X is bounded in magnitude by the corresponding entry of C divided by delta, so perhaps the operator norm of X is at most the operator norm of C divided by delta.

That conclusion does not follow from entrywise inequalities. The operator norm is not monotone under entrywise absolute-value comparison for arbitrary matrices. Changing signs and arrangements of matrix entries can change how they combine when acting on a vector.

Our entrywise proof gives the Frobenius bound immediately. It also gives a weaker operator-norm bound through the inequality between Frobenius and operator norms, with a dimension factor.

For a sharp operator-norm bound, we need an argument adapted to the geometry of the spectra. Under ordered spectral separation, a decaying exponential integral gives a constant-one estimate. For interlaced spectral sets, more elaborate Fourier-kernel techniques enter, and the universal sharp framework has a different constant.

For now, keep the simple and correct statement: pairwise separation gives the sharp Frobenius estimate through entrywise orthogonality.

## From diagonal entries to spectral projections

The formula is not tied to any particular choice of eigenvectors.

Let P for each distinct eigenvalue of A denote its orthogonal spectral projection. Let Q for each distinct eigenvalue of B denote the corresponding projection.

Every map C can be decomposed into rectangular spectral blocks by placing a projection P on the left and a projection Q on the right. Summing all of these pieces recovers C because the spectral projections on each side sum to the identity.

On one such block, the Sylvester operator multiplies by the scalar eigenvalue of A minus the scalar eigenvalue of B. This is the coordinate-free version of the entrywise calculation.

When the spectra are disjoint, construct X by summing each block of C divided by that spectral difference.

This formulation handles repeated eigenvalues naturally. A repeated eigenspace is one projection block, and we never have to choose a preferred orthonormal basis inside it.

The spectral-block reconstruction is legitimate because the spectral projections are idempotent, mutually orthogonal, and sum to the identity, and because every cross-spectral difference in the denominators is nonzero.

## A resolvent is a special case

Suppose B is a scalar multiple of the identity, with scalar b. Then X B equals b times X. The equation becomes A X minus b X equals C, or A minus b identity, followed by X, equals C.

If b is not an eigenvalue of A, the operator A minus b identity is invertible. Therefore X is obtained by applying its inverse to C on the left.

That inverse is a resolvent operator, up to the conventional sign used when defining a resolvent. In diagonal coordinates, it divides each spectral component by a minus b.

For self-adjoint A, its operator norm equals the reciprocal of the distance from b to the spectrum of A. That is the one-parameter version of our spectral denominator story.

The full Sylvester problem is a two-sided generalization: instead of one scalar b, the right action has many spectral values, and every left-right pair creates its own denominator.

## What to reconstruct

Solve the two-by-two example and verify by direct multiplication. Prove the uniqueness statement by subtracting two solutions. Then classify existence and free parameters when A and B share an eigenvalue of multiplicities r and s.

Derive the Frobenius bound from the coefficient formula, and produce a one-entry example attaining equality. Finally, write the spectral-projection formula for the solution and show why it is independent of the chosen bases inside repeated eigenspaces.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For diagonal \(A=\operatorname{diag}(a_i)\) and \(B=\operatorname{diag}(b_j)\),
\[
(AX-XB)_{ij}=(a_i-b_j)X_{ij},\qquad
X_{ij}=\frac{C_{ij}}{a_i-b_j}\quad\text{if }a_i\ne b_j.
\]
When \(a_i=b_j\), solvability requires \(C_{ij}=0\), and \(X_{ij}\) is free. If \(\delta=\min_{i,j}|a_i-b_j|>0\), then \(\|X\|_{S_2}\le\delta^{-1}\|C\|_{S_2}\). The spectral-projection solution is
\[
X=\sum_{i,j}\frac{P_i C Q_j}{a_i-b_j},
\]
with \(P_i,Q_j\) complete orthogonal spectral projections. This formula is valid for real or complex finite-dimensional self-adjoint operators; the cited formal block proof is stated over \(\mathbb C\).

**Lean bridge (verbatim excerpts).**

`DavisKahan/Sylvester/FiniteBlockReconstruction.lean`:

```lean
theorem eq_sum_rectangular_blocks
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (hPsum : ∑ i, P i = (1 : F →L[ℂ] F))
    (hQsum : ∑ j, Q j = (1 : E →L[ℂ] E))
    (X : E →L[ℂ] F) :
    X = ∑ i, ∑ j, P i ∘L X ∘L Q j := by
```

Completeness of the two spectral projection families reconstructs the original operator by summing its rectangular blocks.

`DavisKahan/Sylvester/FiniteBlockReconstruction.lean`:

```lean
theorem finiteDiagonal_sylvester_solution
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hPid : ∀ i, P i * P i = P i)
    (hPorth : ∀ i j, i ≠ j → P i * P j = 0)
    (hPsum : ∑ i, P i = (1 : F →L[ℂ] F))
    (hQid : ∀ i, Q i * Q i = Q i)
    (hQorth : ∀ i j, i ≠ j → Q i * Q j = 0)
    (hQsum : ∑ i, Q i = (1 : E →L[ℂ] E))
    (hne : ∀ i j, a i - b j ≠ 0)
    (C : E →L[ℂ] F) :
    finiteDiagonalOperator P a ∘L
        (∑ i, ∑ j, ((((a i - b j)⁻¹ : ℝ) : ℂ)) • (P i ∘L C ∘L Q j)) -
      (∑ i, ∑ j, ((((a i - b j)⁻¹ : ℝ) : ℂ)) • (P i ∘L C ∘L Q j)) ∘L
        finiteDiagonalOperator Q b = C := by
```

This is the explicit finite blockwise solution in complex Hilbert spaces under the nonzero cross-difference hypothesis. The displayed formula does not itself state the Frobenius inequality.

`DavisKahan/Sources/DavisKahan1970/Sylvester/HilbertSchmidtPairwise.lean`:

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
      δ * ContinuousLinearMap.hilbertSchmidtNorm X ≤ ContinuousLinearMap.hilbertSchmidtNorm C := by
```

This theorem supplies the pairwise-gap Hilbert–Schmidt estimate in the broader closed-operator setting. Its explicit energy-membership hypotheses are part of its formal statement; the lecture gives the finite-dimensional orthonormal-coordinate proof.

**Reconstruction exercise:** Reprove the principal displayed identity from the spoken lecture, then identify the exact source/target types and extra assumptions in each displayed Lean declaration.
