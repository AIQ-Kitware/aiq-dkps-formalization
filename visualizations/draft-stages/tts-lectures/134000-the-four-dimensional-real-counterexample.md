# 134000 — The four-dimensional real counterexample

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `042000–045000`, `132000–133000`. **Next:** `135000`.

<!-- BEGIN SPOKEN LECTURE -->

# The four-dimensional real counterexample

We will now disprove the printed universal claim of Proposition four point four by a complete calculation in four real dimensions. We need an acute pair of two-dimensional subspaces, an orthogonal transformation taking one onto the other, and a unitarily invariant norm in which that competitor beats the canonical direct rotation. Everything will be exact, including the principal angles and the displacement singular values.

## Start with an orthogonal four-by-four matrix

Let U be the plane spanned by the first and second standard coordinate vectors in real four-space. Define a matrix W by taking one half of the following four-by-four sign matrix. Its first row is one, minus one, minus one, minus one. Its second row is one, one, one, minus one. Its third row is minus one, minus one, one, minus one. Its fourth row is one, minus one, one, one.

The matrix looks cumbersome when read aloud, but it has a simple property: each row has four entries of magnitude one, and distinct rows have dot product zero. After multiplication by one half, each row has length one. Thus W is orthogonal.

Define V to be W of U. By construction W is admissible as a transporter from U to V. We now need to determine the geometric position of V and then compare the costs of W and the canonical direct rotation.

## Verify both principal angles

Use the first two columns of W as an orthonormal basis of V. Their top two coordinates form the two-by-two matrix whose rows are one half times one, minus one and one half times one, one. This is the cross-Gram matrix between the standard basis of U and our chosen basis of V.

Multiply this cross-Gram matrix by its transpose. The result is one half times the two-by-two identity. Hence both singular values of the cross-Gram matrix are one over square root of two.

Principal cosines are precisely those singular values. Therefore both principal angles equal forty-five degrees. They are strictly acute, and forty-five degrees is less than the sixty-degree threshold required by the printed proposition.

The geometry satisfies every condition relevant to the purported universal small-angle conclusion. We have not selected a borderline right angle or a nonmatching pair of dimensions.

## Compute the competitor's displacement

The special advantage of W is its own spectral decomposition. There is an orthonormal plane on which W makes a quarter-turn and an orthogonal complementary plane on which W acts as the identity. In the chosen standard coordinates, the turning plane is spanned by the normalized sums of the first and third basis vectors and of the second and fourth basis vectors. One can verify directly by applying the matrix to those two vectors that their images form a ninety-degree rotation.

Thus the eigenvalues of W, after allowing complex eigenvalues to describe a real rotation, are positive i, negative i, one, and one. Its displacement operator identity minus W has singular values square root of two, square root of two, zero, and zero.

Why? For a unitary eigenvalue e to the i phi, the magnitude of one minus that eigenvalue is two times the absolute value of sine phi over two. A quarter-turn has phi ninety degrees and therefore gives square root of two. The fixed directions give zero.

The trace norm of identity minus W, which is the sum of all four singular values, is therefore two square roots of two. Numerically that is about two point eight two eight.

Notice that the competitor moves only one two-dimensional plane. That plane is not one of the two canonical principal planes. The competitor mixes the repeated-angle directions, yet still maps the prescribed U onto the prescribed V.

## Compute the direct rotation

Now construct the canonical direct rotation D between U and V. Since both principal angles are forty-five degrees, the cosine–sine decomposition tells us that D is a direct sum of two forty-five-degree rotations in orthogonal principal planes.

Each two-dimensional principal rotation has displacement singular values equal to two sine of twenty-two point five degrees, repeated twice. Across two principal planes, all four singular values of identity minus D equal two sine of twenty-two point five degrees.

Use the half-angle identity. Two sine of twenty-two point five degrees equals the square root of two minus square root of two. This number is approximately point seven six five.

The direct rotation's trace-norm cost is four times that number, or about three point zero six one. The competitor's cost was approximately two point eight two eight. The competitor is strictly better.

The inequality can be checked exactly without decimals. Square the two positive quantities. The direct cost squared is sixteen times two minus square root of two. The competitor cost squared is eight. The direct cost is larger precisely because square root of two is less than three halves, which is an elementary inequality.

We have therefore established a complete contradiction to the printed claim for trace norm, despite both principal angles satisfying the stated sixty-degree bound.

## Why this does not contradict earlier propositions

Let us compute the positive squared displacement and compare its Ky Fan sums. For D, all four squared displacement singular values equal two minus square root of two, approximately point five eight six.

For W, the squared displacement singular values are two, two, zero, zero. At the first prefix, point five eight six is less than two. At the second, about one point one seven two is less than four. At the third, about one point seven five seven is less than four. At the fourth, about two point three four three is less than four.

Thus the direct rotation really does minimize every Ky Fan sum of the **squared** displacement in this example. It also minimizes the Frobenius norm of the unsquared displacement, because that norm squares and sums its singular values.

But the trace-norm totals of the unsquared lists reverse: four copies of about point seven six five sum to more than two copies of square root of two. Square-rooting entries changes their aggregate comparison.

Proposition four point three survives, while Proposition four point four fails. This example exposes exactly why one cannot pass from squared Ky Fan dominance to unsquared Ky Fan dominance.

## An equality with the projection lower bound

A universal bound says that every admissible W satisfies trace norm of P minus Q no greater than trace norm of identity minus W.

For each principal angle theta, the projection difference has two singular values equal to sine theta. Here there are two angles, both forty-five degrees. Therefore the four singular values of P minus Q are all one over square root of two, whose sum is two square roots of two.

That is exactly the trace norm of our competitor's displacement. So the competitor is not merely better than D; it attains the universal lower bound and is a global trace-norm minimizer.

That conclusion is stronger than the bare refutation, and its proof is short once the general projection lower bound and the explicit singular-value computation are both available.

## The entire acute family

The four-dimensional construction extends to every principal angle strictly between zero and ninety degrees: take two equal angles theta and choose a real orthogonal competitor with one rotation through twice theta and two fixed directions. Its singular-value distribution can differ from that of two independent direct rotations.

The competitor's nonzero displacement singular values are two sine theta, twice. Its trace cost is four sine theta. The canonical direct rotation has four singular values equal to two sine theta over two, so its trace cost is eight sine theta over two.

Use sine theta equal two sine theta over two times cosine theta over two. Then four sine theta equals eight sine theta over two times cosine theta over two. Because cosine theta over two is strictly less than one for every positive theta, the competitor is strictly cheaper for every positive angle in the family.

Consequently no positive universal angle threshold can repair the printed statement across all real dimensions. The failure persists arbitrarily close to coincident subspaces.

## Closing diagnosis

The formal counterexample uses a concrete four-by-four orthogonal matrix, an acute source-target pair, a trace norm represented as a Ky Fan sum, and exact trigonometric calculations. It proves the negation of the universal proposition, not just a gap in an argument.

The physical lesson is about where movement occurs. The canonical direct rotation spreads displacement over two prescribed principal planes. A competing real orthogonal transport can couple the planes and concentrate movement into a different two-plane. For squared cost this is expensive; for trace cost it can be cheaper.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

With \(U=\operatorname{span}(e_1,e_2)\) and
\[
W=\tfrac12\begin{pmatrix}
1&-1&-1&-1\\1&1&1&-1\\-1&-1&1&-1\\1&-1&1&1
\end{pmatrix},\quad V=WU,
\]
the cross-Gram matrix has \(C^*C=\tfrac12I_2\), so \(\theta_1=\theta_2=\pi/4\). The singular values are
\[
s(I-W)=(\sqrt2,\sqrt2,0,0),\qquad
s(I-D)=(\sqrt{2-\sqrt2},\sqrt{2-\sqrt2},\sqrt{2-\sqrt2},\sqrt{2-\sqrt2}).
\]
Hence \(\|I-W\|_1=2\sqrt2<4\sqrt{2-\sqrt2}=\|I-D\|_1\). Yet \(s((I-D)^*(I-D))\prec_w s((I-W)^*(I-W))\). The exact matrix and refutation are in `ShortRotationCounterexample.lean`; a continuum of equal-angle examples is documented in `papers/dk_formalization_journal/counterexample.tex`.

## Exact Lean declaration excerpts

**`Wmat`.** The explicit real `4×4` witness matrix is `½` times a sign matrix. Its orthogonality and transport properties are established elsewhere in the same source module.

`DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean` — `Wmat` (exact declaration header; proof body omitted):

```lean
@[expose] def Wmat : Matrix (Fin 4) (Fin 4) ℝ :=
```

**`principalAngle_le`.** The source proves the maximal principal angle is at most `π/3` for the exact witness (and the module establishes that both angles equal `π/4`).

`DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean` — `principalAngle_le` (exact declaration header; proof body omitted):

```lean
theorem principalAngle_le : Submodule.principalAngles U4 V4 0 ≤ Real.pi / 3 :=
```

**`kyFanSum_lt`.** This proves the strict reversed trace-norm comparison at full Ky Fan rank four.

`DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean` — `kyFanSum_lt` (exact declaration header; proof body omitted):

```lean
theorem kyFanSum_lt :
    (LinearMap.id - Wequiv.toLinearMap).kyFanSum 4 <
      (LinearMap.id -
        (directRotation U4 V4 acute).toLinearMap).kyFanSum 4 :=
```

**`shortRotation_fullDisplacement_refuted`.** The witness includes real subspaces, acuteness, an admissible unitary, a short largest principal angle, and a strict trace-norm improvement.

`DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean` — `shortRotation_fullDisplacement_refuted` (exact declaration header; proof body omitted):

```lean
theorem shortRotation_fullDisplacement_refuted :
    ∃ (U V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)))
      (hacute : Submodule.IsAcute U V)
      (W : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)),
      U.map W.toLinearMap = V ∧
      Submodule.principalAngles U V 0 ≤ Real.pi / 3 ∧
      (LinearMap.id - W.toLinearMap).kyFanSum 4 <
        (LinearMap.id - (directRotation U V hacute).toLinearMap).kyFanSum 4 :=
```

**`not_davisKahanProposition4_4_Finite`.** This discharges the formal negation of the universal proposition by instantiating it with trace norm.

`DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean` — `not_davisKahanProposition4_4_Finite` (exact declaration header; proof body omitted):

```lean
theorem not_davisKahanProposition4_4_Finite :
    ¬ DavisKahanProposition4_4_Finite.{0} :=
```

