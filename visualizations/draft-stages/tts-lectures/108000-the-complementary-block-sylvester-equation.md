# 108000 — The complementary-block Sylvester equation

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `017000` orthogonal coordinates; `063000–071000` Sylvester equations; `093000` common domains; `107000` trial residuals. **Next:** `109000` directed sine geometry.

<!-- BEGIN SPOKEN LECTURE -->

# The complementary-block Sylvester equation

Let E be an orthonormal frame for a trial subspace, let F zero span the exact selected spectral subspace of a self-adjoint operator A, and let F one span its orthogonal complement. A residual measures the failure of E to describe an invariant space. Projecting that residual through F one adjoint produces a Sylvester equation whose unknown represents the complementary overlap.

This equation is the complementary-block Sylvester equation. Its derivation takes only a few lines of matrix algebra, but understanding the roles of the blocks prevents several errors that would otherwise appear in a perturbation bound.

## Start with an exact reducing decomposition

Let A be a self-adjoint operator on an ambient Hilbert space H. Choose a reducing subspace U and its orthogonal complement. Represent U by an isometric coordinate map F zero, and its complement by an isometric coordinate map F one.

Because these two coordinate ranges form an orthogonal decomposition of H, the sum of their range projections equals the identity. In symbols spoken aloud, F zero F zero adjoint plus F one F one adjoint is the identity.

On the exact target subspace, the operator A is represented by a self-adjoint block Lambda zero. On the complement it is represented by a self-adjoint block Lambda one. In the corresponding exact coordinates, A is block diagonal. The crossed blocks vanish because U is reducing.

We are about to compare a trial space against U. Therefore Lambda one, the block on the unwanted exact complement, will be the decisive operator. The spectrum of Lambda zero is important for identifying the target cluster, but it is Lambda one that enters the Sylvester equation for the error.

## Introduce the trial map and residual

Let E be an isometric trial map from coordinate space F into H. Let A zero be a self-adjoint operator on F. It might be the Ritz compression E adjoint A E, but the algebra does not require that choice.

Define the residual R as A E minus E A zero. This is a map from F into H. If the trial vectors were exact eigenvectors, with A zero giving their eigenvalues, R would vanish.

We want to measure how much the trial space lies in the exact complement U perpendicular. Define X to be F one adjoint E. For a trial-coordinate vector x, X x tells us its coordinates in that exact complement.

Notice that X is bounded and has norm at most one. It is the product of an adjoint isometry and an isometry. Its norm will later become the largest directed sine of a principal angle.

## Derive the equation, one factor at a time

Start with R equals A E minus E A zero. Apply F one adjoint on the left. Then F one adjoint R equals F one adjoint A E minus F one adjoint E A zero.

The second term is simply X A zero, by the definition of X.

For the first term, use the exact reducing decomposition. Applying A and then taking complementary coordinates is equivalent to taking complementary coordinates first and then applying Lambda one. Thus F one adjoint A E equals Lambda one F one adjoint E, which equals Lambda one X.

Combining the terms gives F one adjoint R equals Lambda one X minus X A zero.

This is a Sylvester equation. The unknown is X, the complementary overlap of the trial frame. The right-hand side is the compressed residual F one adjoint R. Its two coefficient operators are Lambda one and A zero, acting on different coordinate Hilbert spaces.

No approximation was made in deriving the equation. It is an exact identity.

## Why the compression is part of the proof

The residual R is ambient-valued. The Sylvester unknown X is complementary-coordinate-valued. These maps do not even have the same target space, so they cannot be substituted for one another.

The factor F one adjoint sends the ambient residual into the correct target coordinates. Since F one is an isometry, its adjoint is a contraction. Consequently, the norm of F one adjoint R is at most the norm of R. The same contraction statement holds for compatible symmetric operator ideals, provided their membership and composition hypotheses are in force.

This is the first of two inequalities in the sine theorem. The exact equation gives the stronger right-hand side F one adjoint R; replacing it with R is a convenient bound.

There is a similar but not identical equation obtained by taking adjoints. Its unknown becomes E adjoint F one, and its right-hand side involves the adjoint residual. We may use either orientation, but we must change the coefficient order and sign consistently.

## A worked diagonal model

Let A be diagonal on the plane, with entries zero and five. Take the exact target U to be the horizontal axis and the exact complement to be the vertical axis. Therefore Lambda one is the scalar five.

Choose the trial unit vector u with coordinates cosine theta and sine theta. E sends one to u. The complementary overlap X sends one to sine theta.

First choose A zero to be the scalar zero. Then the residual A u minus zero times u is five sine theta times the vertical basis vector. Its complementary coordinate is five sine theta.

The Sylvester equation becomes five times sine theta minus sine theta times zero equals five sine theta. Both sides agree. If theta is thirty degrees, X is one half and the right-hand side is two point five.

Now choose the Ritz operator instead. The Ritz scalar is five sine squared theta. The residual becomes A u minus five sine squared theta times u. Its vertical coordinate is five sine theta minus five sine cubed theta, which simplifies to five sine theta times cosine squared theta.

The Sylvester left-hand side is now five times sine theta minus five sine squared theta times sine theta, exactly the same expression.

Both equations are valid. But their spectral gaps are different. In the first, the distance between A zero and Lambda one is five. In the second, it is five cosine squared theta. The residual shrinks under Ritz compression, but the gap may shrink too.

This example is why the spectral-gap theorem must use the coefficient A zero actually present in the residual identity. Substituting a different reference eigenvalue changes both sides of the relevant estimate.

## Apply a genuine Sylvester bound

Suppose the spectra of Lambda one and A zero satisfy an ordered gap of size delta, or another separation condition covered by the appropriate Sylvester theorem. Then the Sylvester inverse controls X by F one adjoint R.

In the simplest operator-norm case with an ordered self-adjoint gap, delta times the norm of X is at most the norm of F one adjoint R, hence at most the norm of R.

The result is already a bound on the amount of trial space outside the exact target.

Do not replace the gap hypothesis by the statement that Lambda one and A zero have different eigenvalues. In dimensions greater than one, interlaced spectral sets can have positive pairwise distance and still require a weaker norm constant. We developed those distinctions in the Sylvester unit precisely because the perturbation theorem inherits them.

## Restore the domain conditions for unbounded A

For unbounded self-adjoint A, the line A E minus E A zero is not automatically a globally defined bounded map. We require E to carry the domain of A zero into the domain of A, and R to be the bounded extension of the corresponding difference.

Likewise F one must take vectors in the domain of Lambda one to legal vectors in the domain of A. To justify applying the complementary block, one uses the reducing property together with the corresponding adjoint intertwining identity on the relevant domains.

Then X maps the domain of A zero into the domain of Lambda one, and the Sylvester equation holds there. This is the closed-operator equation to which our unbounded Sylvester estimates apply.

We have completed the algebraic bridge: exact reducing coordinates, trial residual, complementary overlap, and a domain-aware Sylvester equation.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

With reducing coordinates `F₀,F₁`, `F₁* A=Λ₁ F₁*` on the legal domain. For `R=AE−EA₀` and `X=F₁*E`, derive `F₁*R=Λ₁X−XA₀`. A valid `FormBoundedSylvesterGap` plus the domain-aware `SylvesterEquation` gives `δ gauge(X)≤gauge(F₁*R)` in the supported symmetric ideal family, including the membership conclusion. The orientation in some Lean statements is adjointed: the unknown is `E*F₁` and the equation changes sign accordingly.

### Source declaration excerpts

`DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomain.lean` — `HasCommonDomain` (exact declaration header; body omitted):

```lean
def HasCommonDomain
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (X : F →L[𝕜] E) : Prop :=
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/ScalarGeneric.lean` — `sinTheta_unbounded_formGap_idealFamily_block_rclike` (exact declaration header; body omitted):

```lean
theorem sinTheta_unbounded_formGap_idealFamily_block_rclike
    (N : TauCeti.SymmetricOperatorIdealFamily 𝕜)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
```

**Mapping.** The Lean `UnboundedSinThetaData` packages trial and complementary maps, their self-adjoint coefficient operators, and a bounded residual extending the common-domain identity. The `unbounded_adjoint_residual_block_identity` theorem supplies the legal complementary equation in the adjointed orientation. `ScalarGeneric.sinTheta_unbounded_formGap_idealFamily_block_rclike` then applies the domain-aware Sylvester estimate and ideal contraction.
