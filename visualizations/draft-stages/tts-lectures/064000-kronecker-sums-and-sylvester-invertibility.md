# 064000 — Kronecker sums and Sylvester invertibility

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `024000` eigenvalues and multiplicities; `026000` spectral theorem; `062000–063000` Sylvester equations and spectral blocks. **Next:** ordered spectral separation.

<!-- BEGIN SPOKEN LECTURE -->

# Turn an equation of matrices into one linear map

In the previous lecture we solved A X minus X B equals C by dividing spectral blocks. Today we will treat the entire left-hand side as a single linear operator. Its input is a matrix X, and its output is the matrix A X minus X B. Once we understand the spectrum of that operator, we can state precisely when the Sylvester equation has a unique solution for every right-hand side.

There are two reasons to do this. First, it reveals why the differences of eigenvalues are unavoidable. Second, it separates an algebraic question, invertibility, from a quantitative question, how large the inverse can be.

## A linear operator on a space of matrices

Let A be an m-by-m matrix and B an n-by-n matrix. The unknown X has m rows and n columns. The space of possible X matrices is a vector space of dimension m times n.

Define a map S by the rule: S applied to X equals A X minus X B. Multiplication distributes over sums, so S is linear. Solving the Sylvester equation means solving S of X equals C.

Why bother naming this map? Because we can ask ordinary questions about its kernel, eigenvalues, determinant, and inverse. The unknown is itself a matrix, but the problem is now a familiar linear system with m times n scalar unknowns.

## Stacking columns into a vector

Take a matrix with two rows and two columns. Stack its first column above its second. We obtain a vector with four entries. This operation is often called vectorization. For general m and n, it identifies matrices with vectors having m times n coordinates.

What happens to left multiplication by A? Each column of X is transformed by the same matrix A. Thus, in the stacked representation, A appears in n identical diagonal blocks.

What happens to right multiplication by B? It mixes the columns of X according to B's coefficients. The resulting matrix is described using the Kronecker product: the matrix of S is identity of size n tensor A, minus the transpose of B tensor identity of size m.

The transpose is important. Right multiplication mixes column labels in the opposite index order from left multiplication. If we forget that transpose, the displayed Kronecker formula generally becomes false.

A tensor or Kronecker product is just a systematic way to build a block matrix. If R has scalar entries and T is another matrix, their Kronecker product replaces each entry of R by that entry multiplied by the full matrix T. No abstract tensor theory is needed to verify the formula, only the row and column indices.

## A diagonal example

Take A diagonal with entries one and four, and B diagonal with entries zero and three. Use column-stacking order.

The first column of X has spectral differences one minus zero and four minus zero. Those are one and four. The second column has differences one minus three and four minus three. Those are negative two and one.

Therefore the four-by-four matrix of S is diagonal with entries one, four, negative two, one. Its determinant is negative eight, so the map is invertible.

For any right-hand side, invert this diagonal matrix by dividing the four coordinates by those entries. This agrees exactly with the entrywise construction from the last lecture.

If we change the second eigenvalue of B from three to four, one diagonal entry becomes zero. Then S has a nonzero kernel: a matrix whose only nonzero entry connects the four-eigenspace of A with the four-eigenspace of B. So S is not invertible.

## Why all eigenvalue differences occur

The diagonal calculation proves the claim for diagonal matrices. But the spectrum of S is determined by cross differences even when A and B are not self-adjoint or diagonalizable, provided we work with finite complex matrices.

Here is a route to the general statement. Every complex square matrix has an eigenvector. Starting with that eigenvector and extending to a basis puts the matrix into upper block-triangular form. Repeat on the remaining block. Induction gives an upper-triangular matrix, even when no eigenbasis exists.

Apply this procedure separately to A and B. Changing bases on the left and right of X changes coordinates in the matrix space, so it conjugates S by an invertible coordinate transformation. Conjugation preserves eigenvalues.

Now write A and B as upper-triangular matrices in their chosen bases. Their diagonal entries list their eigenvalues with algebraic multiplicity. In a suitable ordering of the matrix units, the Sylvester map is triangular with diagonal entries consisting of every eigenvalue of A minus every eigenvalue of B.

A triangular matrix has characteristic polynomial equal to the product of its diagonal factors, because its determinant is the product of its diagonal entries. Thus the characteristic polynomial of S is the product, over every left and right eigenvalue pair, of the scalar variable minus their difference.

That statement includes algebraic multiplicities. If an eigenvalue occurs twice on the left and three times on the right, their difference contributes six entries to the multiset of eigenvalues of S.

## Invertibility and disjoint spectra

A finite square matrix is invertible exactly when zero is not an eigenvalue. For S, zero occurs as an eigenvalue precisely when an eigenvalue of A equals an eigenvalue of B.

We have proved the finite-dimensional Sylvester invertibility criterion: S is invertible if and only if A and B have no eigenvalue in common.

Notice what it does not require. The eigenvalues do not have to be arranged in order. A could have eigenvalues negative two and positive two while B has eigenvalue zero. Every cross difference remains nonzero, so the Sylvester map is invertible.

Nor does it require A and B to be diagonalizable. Triangularization was enough for the invertibility criterion. However, the convenient formula obtained by independently dividing orthogonal spectral blocks only applies directly when suitable spectral decompositions exist, as for self-adjoint matrices.

## Being invertible is not the same as being well conditioned

Now suppose A is the two-by-two upper-triangular matrix with ones on its diagonal and a large positive number M in its upper-right corner. Let B be the one-by-one zero matrix. Then X is a two-entry column and the Sylvester map is simply multiplication by A.

Both eigenvalues of A are one, and B's only eigenvalue is zero. The spectral distance is one, independent of M.

But the inverse of A has ones on its diagonal and negative M in its upper-right corner. Apply it to the second standard basis vector. The result has entries negative M and one, whose length is the square root of M squared plus one. Therefore the norm of the inverse grows without bound as M grows.

This example is a warning. For arbitrary nonnormal matrices, spectral distance alone does not bound the inverse Sylvester operator by one over the distance. The algebraic invertibility criterion remains correct, but useful norm estimates need additional structure.

When A and B are self-adjoint, orthogonal spectral decompositions and unitary groups provide that structure. Different geometric positions of their spectra then yield different quantitative bounds.

## Connecting back to the coordinate-free equation

In the bounded-operator setting, S acts on a space of bounded linear maps between two Banach spaces. It is still linear, and it is bounded because the triangle inequality gives the norm of S applied to X at most the sum of the norms of A and B times the norm of X.

In finite dimensions, disjoint spectra guarantee invertibility of S by our triangularization argument. In infinite-dimensional Banach spaces, that same general conclusion requires a deeper theorem: the Sylvester–Rosenblum result, which uses resolvents and contour integration. We will prove its mechanism after studying exponential representations.

For now, rebuild the vectorization formula by examining one entry at a time. Verify the four-by-four diagonal example. Then prove the finite invertibility criterion by triangularizing A and B, and explain why the large-M example defeats a naive universal norm bound.

These are three different accomplishments: describing S, deciding whether S is invertible, and controlling the size of its inverse. We will use all three in the perturbation theory to come.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For column-stacking vectorization,
\[
\operatorname{vec}(AX-XB)=\bigl(I_n\otimes A-B^{\mathsf T}\otimes I_m\bigr)\operatorname{vec}(X).
\]
For complex finite-dimensional square matrices,
\[
\sigma(\mathcal S_{A,B})=\{\lambda-\mu:\lambda\in\sigma(A),\ \mu\in\sigma(B)\}
\]
with algebraic multiplicity. In particular, \(\mathcal S_{A,B}\) is invertible exactly when \(\sigma(A)\cap\sigma(B)=\varnothing\). The example \(A=\begin{pmatrix}1&M\\0&1\end{pmatrix}\), \(B=0\) demonstrates why this alone yields no norm bound depending only on spectral distance for arbitrary nonnormal operators.

**Lean bridge (verbatim source excerpts).**

`DavisKahan/Sylvester/FiniteBlockReconstruction.lean` — `finiteDiagonal_sylvester_block`:

```lean
theorem finiteDiagonal_sylvester_block
    {m n : ℕ}
    (P : Fin m → F →L[ℂ] F) (Q : Fin n → E →L[ℂ] E)
    (a : Fin m → ℝ) (b : Fin n → ℝ)
    (hPid : ∀ i, P i * P i = P i)
    (hPorth : ∀ i j, i ≠ j → P i * P j = 0)
    (hQid : ∀ i, Q i * Q i = Q i)
    (hQorth : ∀ i j, i ≠ j → Q i * Q j = 0)
    (X : E →L[ℂ] F) (i : Fin m) (j : Fin n) :
    P i ∘L (finiteDiagonalOperator P a ∘L X -
      X ∘L finiteDiagonalOperator Q b) ∘L Q j =
      (((a i - b j : ℝ) : ℂ)) • (P i ∘L X ∘L Q j) := by
```

The projection-block identity is the source-backed finite self-adjoint counterpart of the eigenvalue-difference calculation. The Kronecker spectrum formula for arbitrary finite complex matrices is proved pedagogically above, but this declaration is not itself a general Kronecker-spectrum theorem.

`DavisKahan/Sylvester/PairwiseHomogeneousUniqueness.lean` — `Sylvester_solution_unique_of_disjoint_spectrum`:

```lean
theorem Sylvester_solution_unique_of_disjoint_spectrum
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X Y C : F →L[ℂ] E}
    (hdisj : Disjoint
      (_root_.LinearPMap.spectrum A)
      (_root_.LinearPMap.spectrum B))
    (hX : _root_.LinearPMap.SylvesterEquation A B X C)
    (hY : _root_.LinearPMap.SylvesterEquation A B Y C) :
    X = Y := by
```

Uniqueness under disjoint spectra is stated for self-adjoint partial maps between complex Hilbert spaces; it does not assert the general nonnormal finite-dimensional result or existence.

