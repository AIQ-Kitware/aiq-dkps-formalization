# 143000 — Joint movement of eigenvalues and angles

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `024000–030000`, `106000–117000`, `140000`, `142000`. **Next:** `144000`.

<!-- BEGIN SPOKEN LECTURE -->

# Joint movement of eigenvalues and angles

Suppose we perturb a self-adjoint operator. One theorem tells us how much its eigenvalues can shift. Another tells us how far a selected eigenspace can rotate. Davis and Kahan's Question ten point three asks for the best inequalities that treat those changes simultaneously. A joint bound must account for the interaction between eigenvalue shifts and eigenvector rotations. Rayleigh quotient identities provide exact relations, and a two-dimensional model shows when separate worst-case bounds lose information.

## The two quantities

Start in finite dimensions. Let A be self-adjoint, and let B equal A plus a self-adjoint perturbation H. Imagine A has a simple eigenvalue lambda zero and a normalized eigenvector u. Let v be a normalized eigenvector of B with eigenvalue mu, chosen as the continuation of the same isolated spectral cluster.

Our scalar quantities are the eigenvalue displacement, mu minus lambda zero, and the angle theta between u and v. The sine of theta measures how much v escapes the line through u. The cosine measures the overlap between the two directions.

The familiar Weyl bound gives the absolute eigenvalue displacement at most the operator norm of H, once the eigenvalues are matched by order. A sine-theta bound gives an angle estimate in terms of H and an appropriate spectral separation. These statements are valid and useful, but they may be far from simultaneously sharp. The perturbation that maximizes the eigenvalue displacement need not maximize the rotation.

To see the distinction, separate diagonal and off-diagonal perturbations. A diagonal perturbation can change an eigenvalue without rotating its eigenvector. A purely off-diagonal perturbation often rotates an eigenvector at first order but changes its eigenvalue only at second order. The geometry of H matters.

## The exact two-level model

Let A be a real two-by-two diagonal matrix, with entries minus g over two and plus g over two, where g is positive. Let H have zero diagonal and equal off-diagonal entries t. Then B has entries minus g over two, t, t, and plus g over two.

Compute the characteristic polynomial. Its roots are plus and minus the square root of g squared over four plus t squared. The lower eigenvalue moves downward by the amount equal to that square root minus g over two. The eigenvectors rotate by an angle theta satisfying tangent of twice theta equals two t over g, taking the acute branch with theta below forty-five degrees when t is positive.

These two formulas can be combined. Write a for g over two. The magnitude of the lower eigenvalue shift is square root of a squared plus t squared, minus a. From the two-level eigenvector equation we also have tangent theta equals that displacement divided by t. Therefore the exact scalar relation is: eigenvalue shift magnitude equals t times tangent theta.

That identity is more informative than applying Weyl and sine-theta independently. For small t, theta is approximately t over g, while the eigenvalue displacement is approximately t squared over g. In other words, the angle responds linearly and the eigenvalue shift quadratically. For a perturbation with a diagonal component, the eigenvalue shift can instead have a first-order contribution.

Another equivalent formula uses the cosine of twice theta. It equals g divided by the square root of g squared plus four t squared. The displacement and the angle are two aspects of one characteristic equation; they are not free variables.

## Rayleigh quotients measure angle with spectral weights

There is a useful exact identity for a general self-adjoint A. Suppose u is a lowest-eigenvalue vector with eigenvalue lambda zero. Expand an arbitrary unit vector v in an orthonormal eigenbasis beginning with u. Let its coefficient along u have magnitude cosine theta. The remaining coefficients have squared magnitudes summing to sine squared theta.

The Rayleigh quotient of v minus lambda zero is the sum, over the remaining eigenvectors, of each spectral distance above lambda zero times the corresponding squared coefficient. If every other eigenvalue is at least lambda zero plus g, that difference is at least g times sine squared theta.

This is a rigorous joint restriction: a unit vector that rotates away from the lowest eigenline must pay Rayleigh-quotient energy, weighted by the gap. The relation becomes equality in the two-level model when all the leaked mass lands in the next eigenspace.

Now let v be an eigenvector of B. Its Rayleigh quotient for A equals mu minus the expectation of H on v. Therefore mu minus lambda zero is at least g sine squared theta minus the operator norm of H. A reverse estimate is available when A has an upper spectral bound on the complementary subspace. The identity relates angular leakage, spectral location, and the diagonal expectation of the perturbation.

## Residuals add further structure

For an approximate eigenvector v and candidate eigenvalue mu, consider the residual A v minus mu v. Expand v in the eigenbasis of A. Each coefficient is multiplied by its spectral difference from mu. The squared residual norm is the sum of squared differences times coefficient energies.

If mu is isolated from every unwanted eigenvalue by a distance delta, then the unwanted squared coefficient mass is at most residual squared divided by delta squared. Thus the sine of the relevant subspace angle is at most residual norm divided by delta. This is the scalar instance of the complementary Sylvester argument.

But notice the requirement that we know which eigenvalue is intended. A Rayleigh quotient alone can be deceptive. Take a three-by-three diagonal matrix with eigenvalues minus one, zero, and one. Choose a unit vector that is the equal-weight combination of the minus-one and plus-one eigenvectors. Its Rayleigh quotient is zero, exactly matching the middle eigenvalue, yet the vector is perpendicular to the true middle eigenvector. Its residual is not zero.

So joint control of eigenvalue location and vector angle needs either a spectral-selection rule or residual information. Numerical closeness of the Rayleigh quotient to an eigenvalue is not sufficient.

## A gap measured at the moving eigenvalue

There is a second useful bound. Project the equation Bv equals mu v onto the orthogonal complement of u. Since B equals A plus H, the unwanted component of v satisfies an equation involving A restricted to that complement minus mu. The right-hand side is minus the complementary component of H v.

If mu lies at least delta away from the complementary spectrum of A, the inverse of that restricted operator has norm at most one over delta. Hence sine theta is at most the norm of H divided by delta. This gap is measured from the moving eigenvalue mu, rather than automatically from lambda zero.

Weyl's theorem can relate the two distances. If the original gap is g and the eigenvalue shift has magnitude at most h, then the moving gap is at least g minus h, provided h is smaller than g. Inserting that lower bound yields the common perturbation estimate sine theta at most h over g minus h.

That estimate remains conservative: our exact off-diagonal model carries an additional relationship between mu and theta that the bound does not exploit.

## A coupled energy theorem already available

Chandler Davis established a related sum-of-squares estimate under a particular separation condition on the ordered eigenvalues of two self-adjoint matrices and a compatible nonzero-overlap matching of their eigenvectors. The sum of gap-squared angular errors and squared matched eigenvalue changes is bounded by the Frobenius norm squared of the perturbation. The matching and spectral separation are essential hypotheses.

That is a genuinely joint inequality. It allocates one finite perturbation-energy budget between turning eigenvectors and moving eigenvalues. An estimate formed by taking the worst separate eigenvalue and angle bounds would not express this tradeoff. The theorem requires its stated cross-eigenvalue separation, not merely a gap within each unperturbed cluster. The chosen matching and nonzero-overlap assumption also matter, particularly when eigenvalues are repeated or labels can exchange.

We can derive its basic intuition from orthogonal eigenvector expansions. Express the perturbation between eigenbases of the two operators. Its Frobenius energy is the sum of squared spectral differences weighted by squared cross-overlaps. Split this sum into matched diagonal contributions and off-diagonal mixing. A lower bound on each off-diagonal spectral denominator gives the rotation term; the matched terms give eigenvalue displacement. The two contributions add before we compare against the perturbation energy.

This is the right mathematical model for Question ten point three, though it does not settle every possible best-constant or block-multiplicity version of that question.

## What the optimization question really asks

To formulate a best possible joint theorem, we must decide what data are fixed. Is the perturbation bounded only in operator norm? Do we know its diagonal and off-diagonal blocks separately? Is the selected eigenvalue extremal, interior, simple, or part of a cluster? Are we allowed to choose an arbitrary nearby eigenvector, or must we follow a specified spectral projection?

Different answers produce different feasible regions for the pair consisting of eigenvalue shift and angle. A scalar inequality describing that region may be sharp in dimension two but fail when eigenvalues are clustered, because several unwanted directions can share the leakage. For matrix-valued statements, the natural objects are ordered eigenvalue displacements alongside a list of principal angles, possibly compared through a symmetric gauge.

Question ten point three remains broader than the available estimates. The two-level equality and Rayleigh identity settle particular cases; a general sharp inequality must also account for interactions among several spectral channels, already present in dimension three.

As an exercise, reproduce the two-level eigenvalue and angle formulas without memorizing them. Then prove the Rayleigh lower bound for an extremal eigenvalue and construct the three-level counterexample to Rayleigh-quotient-only identification. Those calculations show why joint perturbation bounds need more than two independent worst-case estimates.

<!-- END SPOKEN LECTURE -->

---

## Display-only mathematical and Lean correspondence

The original source's `DK-10.3` is an open question on simultaneous eigenvalue/eigenvector displacement; see `prose/distilled_literature/DavisKahan1970_part_III.tex`. The exact two-level model has

\[\mu_{\pm}=\pm\sqrt{g^2/4+t^2},\qquad \tan(2\theta)=2t/g,\qquad \Delta\mu=t\tan\theta.\]

For an extremal eigenpair `Au=λ₀u` and spectral gap `g>0` on `u⊥`, the Rayleigh identity yields

\[\langle v,Av\rangle-\lambda_0\ge g\sin^2\angle(u,v).\]

These are finite-dimensional derivations, not a claim that the whole of Question 10.3 has been solved by a single Lean theorem. The source excerpts below supply the variational and perturbation components.

## Exact Lean declaration excerpts

**`totalRotation_add_eigenvalueMotion_le`** — A completed joint energy inequality: the `hover` premise fixes nonzero matched eigenvector overlaps; `hsep` is a CROSS-list separation inequality; `γ² totalRotationEnergy + eigenvalueMotionEnergy` is bounded by the squared Frobenius perturbation energy. This is a special-case theorem, not a general solution of Question 10.3.

Source: `DavisKahan/Sources/Davis1963/RotationEnergy.lean`; exact declaration header (proof body omitted).

```lean
theorem totalRotation_add_eigenvalueMotion_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {n : ℕ} (hn : finrank 𝕜 E = n)
    (hover : ∀ i, ⟪hB.eigenvectorBasis hn i, hA.eigenvectorBasis hn i⟫_𝕜 ≠ 0)
    {γ : ℝ}
    (hsep : ∀ i j, i ≠ j →
      γ ^ 2 + (hA.eigenvalues hn i - hB.eigenvalues hn i) ^ 2 ≤
        (hA.eigenvalues hn i - hB.eigenvalues hn j) ^ 2) :
    γ ^ 2 * totalRotationEnergy hA hB hn hover +
        eigenvalueMotionEnergy (hA.eigenvalues hn) (hB.eigenvalues hn) ≤
      UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A) ^ 2 := by
```

**`equation1_8_residual_norm_minimized_by_rayleighQuotient`** — The Ritz compression minimizes residual operator norm among coordinate operators on the same trial subspace, giving the residual counterpart to the eigenpair discussion.

Source: `DavisKahan/Sources/DavisKahan1970/Section1.lean`; exact declaration header (proof body omitted).

```lean
theorem equation1_8_residual_norm_minimized_by_rayleighQuotient
    (T : H →L[𝕜] H) (P : Submodule 𝕜 H) [P.HasOrthogonalProjection]
    (A₀ : P →L[𝕜] P) :
    ‖DavisKahan.residual T P.subtypeL (DavisKahan.Sylvester.compressOperator P T)‖ ≤
      ‖DavisKahan.residual T P.subtypeL A₀‖ := by
```

