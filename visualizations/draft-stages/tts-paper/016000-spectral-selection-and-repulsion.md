# 016000 — Spectral selection and repulsion

**Track:** G3 audio paper track. **Draft:** adapted from G2 lecture 119000. **Section:** reflection-selection. **Audience:** prior linear algebra and basic analysis.

<!-- BEGIN SPOKEN LECTURE -->

# Spectral selection and repulsion

An off-diagonal perturbation preserves the form gap between two ordered diagonal blocks. The block-sign reflection makes the reason visible: it gives a positive coercive form even when the off-diagonal coupling is arbitrarily large. We will turn that estimate into a spectral theorem, not merely an argument excluding eigenvectors, and identify the canonical perturbed spectral subspace.

This is the starting point of Davis and Kahan's Theorem eight point one. We will derive the gap protection, identify the selected reducing branch, and explain the cosine factors in the theorem's stronger comparisons.

## Build the two-block setting

Let A be self-adjoint. Decompose the Hilbert space orthogonally into a subspace P and its perpendicular complement. Suppose P reduces A, so A is block diagonal relative to this decomposition.

Assume the spectrum of the first block is at most alpha, while the spectrum of the second block is at least alpha plus delta, where delta is positive. We call P the low subspace and its complement the high subspace.

Let H be self-adjoint and off-diagonal: both diagonal compressions of H vanish. In block-matrix form, H has zeros on the diagonal and an operator B in the lower-left corner, with B adjoint in the upper-right corner.

Define S to be A plus H. No smallness assumption on the norm of H has been made. Off-diagonality is the structural assumption.

## Prove the spectral gap survives

Choose any real number lambda strictly between alpha and alpha plus delta. We want to prove S minus lambda times the identity is invertible.

In a finite-dimensional model, write its diagonal blocks as A low minus lambda and A high minus lambda. The first is strictly negative, and the second strictly positive. Suppose S has an eigenvector with eigenvalue lambda. Write it as a pair x and y in the low and high subspaces.

The eigenvalue equations say that A low minus lambda applied to x plus B adjoint applied to y is zero, and B applied to x plus A high minus lambda applied to y is zero.

Take the inner product of the first equation with x and of the second with y. Subtract the first real identity from the second. The real off-diagonal contributions cancel because B and B adjoint have matching pairings.

The remainder is the positive quantity associated with lambda minus A low on x, plus the positive quantity associated with A high minus lambda on y. Each term is bounded below by its distance from the corresponding edge of the gap times the squared norm of its vector. Hence both x and y are zero, a contradiction.

This excludes eigenvalues in the gap. In infinite-dimensional Hilbert space, simply excluding eigenvectors would not be enough. Instead, use the same coercive estimate with a block-sign reflection to obtain a lower norm bound for S minus lambda. Self-adjointness makes the range dense; bounded below and closed range then make it surjective. Thus lambda lies in the resolvent set. The argument proves full spectral repulsion, not merely absence of point spectrum.

## See the effect in a plane

Let A have diagonal entries negative one and one. The gap is the open interval from negative one to one. Add an off-diagonal symmetric perturbation whose two off-diagonal entries are h.

The eigenvalues of S are negative and positive square root of one plus h squared. Both move away from zero as h increases. Neither can enter the original gap. For h equal to three, they become approximately negative three point one six two and positive three point one six two.

The new low eigenspace rotates, but the gap itself remains protected, no matter how large h becomes. This phenomenon is often called spectral repulsion.

A diagonal perturbation would destroy the argument. If the original low eigenvalue is shifted upward sufficiently, it can move into the former gap. Thus the hypothesis that H is off-diagonal is doing indispensable work.

## Select the canonical branch

Since S has no spectrum in the open gap, define Q as its spectral subspace for eigenvalues at most alpha. In a finite-dimensional matrix, Q is the span of all eigenvectors with eigenvalues at most alpha. In Hilbert space it is the range of the bounded Borel spectral projection for the half-line ending at alpha.

This definition has no arbitrary eigenbasis or angle choices. The spectral repulsion result shows that the complementary subspace automatically has spectrum at least alpha plus delta. Q and its complement reduce S.

Theorem eight point one goes further: the maximal angle between P and this Q is strictly below forty-five degrees. Consequently the canonical branch is on the correct side of the doubled-angle ambiguity, even for large off-diagonal couplings.

The source also proves uniqueness: a reducing subspace with the relevant spectral orientation and the closed quarter-angle characterization must coincide with Q. This is stronger than saying that some nearby subspace exists.

## Recover the block compression inequality

Why do cosines of principal angles appear in Theorem eight point one's later parts? Decompose the original high subspace using the new low and high spectral projections of S.

Write C for the overlap from the original high subspace into the new high subspace. The complementary overlap goes into the new low subspace. Since the original high compression of H is zero, compressing S to the original high subspace gives exactly the original high block of A.

Subtract alpha from the corresponding quadratic form. On the new low spectral component, S minus alpha is nonpositive. Dropping that contribution can only increase the form. We are left with an upper bound supplied by the new high component, weighted by the overlap C.

Symbolically, this is the inequality that the original high block minus alpha is at most C adjoint times the new high block minus alpha times C. The precise placement of adjoints depends on which coordinate space is used. The lower-block statement follows by the same argument with signs reversed.

In a principal-vector basis, the singular values of C are cosines of principal angles. Thus a cosine-squared factor is not an ornamental correction: it records the loss when a vector of the old high block is projected into the new high subspace.

## From forms to eigenvalue comparisons

For a finite-dimensional self-adjoint matrix, Courant–Fischer characterizes its k-th largest eigenvalue by maximizing, over k-dimensional subspaces, the smallest Rayleigh quotient on that subspace. Consequently, a quadratic-form inequality between self-adjoint matrices implies the corresponding order of their decreasing eigenvalue lists. Applying this min–max principle to the compression inequality gives repulsion estimates for ordered eigenvalues, with cosine factors.

The source also proves dimension-free approximation-number formulations and finite-dimensional inequalities for symmetric gauges. Those conclusions require an additional step: comparing positive compressed operators at the level of singular-value prefixes, then passing from weak majorization to each supported symmetric gauge.

We should not jump directly from one scalar operator-norm inequality to every individual eigenvalue comparison. The theorem contains a hierarchy: spectral gap preservation, ordered form inequalities, approximation numbers, and symmetric-gauge inequalities.

## The role of the quarter angle

In the two-by-two model, the low eigenvector of S is rotated from the old low axis by theta satisfying tangent twice theta equal to the magnitude of h. This always puts theta below forty-five degrees. As h tends to infinity, the angle approaches forty-five degrees from below.

So the strict threshold does not imply that the subspaces remain extremely close for a large perturbation. It asserts that the canonical low branch cannot exchange roles with the high branch. That is exactly the information a doubled-sine estimate lacks.

The sharp part of Theorem eight point one is structural: no finite off-diagonal coupling causes a spectral crossing, and the selected branch remains on the near-zero side of the quarter angle.

## Why dimensions and defects still matter

For finite-dimensional P and Q, the low spectral branch has the same rank as P. A continuous deformation from zero coupling is one way to see this; the spectral-gap argument prevents an eigenvalue from crossing the separating threshold.

In infinite dimensions, equal cardinal dimensions do not force the two directed projection gaps to agree. A full symmetric-angle statement needs additional compatibility of the crossed defects or suitable finite-dimensional hypotheses. Otherwise retain the directed conclusion.

For the canonical branch theorem, these issues are addressed in its actual conclusion and hypotheses; one should not import an equal-rank simplification from finite-dimensional matrices into an arbitrary Hilbert space proof.

## What to retain

We now have a concrete mechanism for identifying the intended spectral subspace: form-separated diagonal blocks plus an off-diagonal self-adjoint perturbation preserve the open gap, define a canonical spectral projection, and keep the selected branch below a quarter turn. The compression identities then yield the eigenvalue and norm inequalities.

The strict quarter-angle branch comes from off-diagonal structure and the ordered form gap, even for an arbitrarily large finite coupling. Smallness of the perturbation relative to the gap is useful when one wants a small numerical angle bound; it is not a prerequisite for selecting the branch.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Assume `A=A*`, `P` reduces `A`, `A|P≤α`, `A|Pᗮ≥α+δ` with `δ>0`; let `H=H*` satisfy `PHP=(I-P)H(I-P)=0`. Then

\[\sigma(A+H)\subset(-\infty,\alpha]\cup[\alpha+\delta,\infty),\quad Q=\operatorname{Ran}E_{A+H}(( -\infty,\alpha]).\]

The source `Theorem81Conclusion` bundles repulsion, selected reducing property, two form bounds, two spectral placements, and strict quarter-angle control. Its stronger block estimates use compression and Ky Fan/approximation-number machinery. The spoken proof of full spectral repulsion uses the bounded-below/dense-range argument appropriate to self-adjoint operators.

### Exact Lean declaration excerpts

`DavisKahan/Sources/DavisKahan1970/Section8/Theorem81.lean` — `canonicalLowBranch` (exact declaration header; proof body omitted):

```lean
def canonicalLowBranch (B : E →L[ℂ] E) (hB : B.IsSymmetric)
    (alpha : ℝ) : Submodule ℂ E :=
```

`DavisKahan/Sources/DavisKahan1970/Section8/Theorem81.lean` — `theorem8_1_canonicalBranch` (exact declaration header; proof body omitted):

```lean
theorem theorem8_1_canonicalBranch
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hHP : ∀ x ∈ P, H x ∈ Pᗮ)
    (hHPperp : ∀ x ∈ Pᗮ, H x ∈ P) :
    Theorem81Conclusion A H P
      (canonicalLowBranch (A + H)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hH)) alpha)
      alpha delta := by
```

`DavisKahan/Sources/DavisKahan1970/Section8/Theorem81.lean` — `theorem8_1_maximalAngle_le_iff_spectrumIn` (exact declaration header; proof body omitted):

```lean
theorem theorem8_1_maximalAngle_le_iff_spectrumIn
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hHP : ∀ x ∈ P, H x ∈ Pᗮ)
    (hHPperp : ∀ x ∈ Pᗮ, H x ∈ P)
    (M : Submodule ℂ E) [M.HasOrthogonalProjection]
    (hMreduces : Submodule.IsReducing M (A + H)) :
    maximalAngle P M ≤ Real.pi / 4 ↔
      (SpectrumIn (A + H) M (Set.Iic alpha) ∧
        SpectrumIn (A + H) Mᗮ (Set.Ici (alpha + delta))) := by
```

**Mapping.** `canonicalLowBranch` is the spectral subspace selected by a Borel half-line indicator. `theorem8_1_canonicalBranch` assumes a self-adjoint block-diagonal `A` separated by `delta` and a self-adjoint off-diagonal `H` and returns `Theorem81Conclusion`, which includes repulsion, form bounds, spectral orientation, and quarter acuteness. The characterization theorem compares maximal angle with both spectral placement conditions for another reducing subspace.

