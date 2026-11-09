# 003000 — Trial subspaces, Ritz values, and residuals

**Track:** G3 audio paper track. **Draft:** adapted from G2 lecture 107000. **Section:** foundation. **Audience:** prior linear algebra and basic analysis.

<!-- BEGIN SPOKEN LECTURE -->

# Trial spaces, exact subspaces and residuals

Suppose a self-adjoint operator has an invariant eigenspace that we cannot compute exactly. A numerical method produces a trial subspace instead. To estimate the angle between them, we first need a quantity that measures how far the trial subspace fails to be invariant under the original operator.

The exact subspace is invariant under the operator we want to understand. The trial subspace is the space produced by an algorithm, approximation, measurement, or a nearby operator. The residual will record what the target operator does to trial vectors that the trial space cannot explain internally.

## Choose orthonormal coordinates for the trial space

Let A be a self-adjoint operator on an ambient finite-dimensional Hilbert space H. Let F be a lower-dimensional coordinate space. Choose an isometric linear map E from F into H. Its columns are orthonormal trial vectors, and the range of E is the trial subspace V.

The equation E adjoint E equals the identity says that E preserves the lengths and inner products of trial-coordinate vectors. The ambient projection onto V is P equals E E adjoint.

For any ambient vector z, E adjoint z contains the trial coordinates of its projection. Applying E again returns the component of z inside V. Thus P z equals E E adjoint z. The complementary projection is the identity minus P.

The trial basis can change without changing V. If W is unitary on F, the map E W is another orthonormal frame for exactly the same subspace. A valid subspace-angle theorem should be insensitive to that replacement.

## Compress A to obtain the Ritz operator

Define the compressed or Ritz operator M as E adjoint A E. This is an operator on F. Because A is self-adjoint, M is self-adjoint too.

The compression answers a limited question: if we start with a trial vector E x, apply A, then retain only the component in V, which trial coordinates do we obtain? The answer is M x.

We should not confuse this compression with the whole action of A. The vector A E x can have a component outside V. Exactly that missing component is the residual.

Define R to be A E minus E M. Its input is a trial-coordinate vector x and its output is an ambient vector. In a matrix representation, its columns are the eigen-equation defects of the chosen trial basis.

Take E adjoint of the residual. We find E adjoint R equals E adjoint A E minus E adjoint E M. By the definitions of M and isometry, these terms are equal. Therefore E adjoint R is zero.

Every residual vector is orthogonal to the trial subspace. This is the Galerkin orthogonality principle. It is not an assumption in this construction; it follows from choosing the Ritz compression.

## Derive the residual's projection formula

Since M equals E adjoint A E, substitute it into the definition of R. The result is A E minus E E adjoint A E. Factor out A E on the right. We get R equals the identity minus P, composed with A E.

Thus the residual is simply the part of A E that escapes V. In particular, R vanishes exactly when A maps every vector in V back into V. For a self-adjoint operator, that means V is reducing: its orthogonal complement is invariant as well.

This gives a concrete diagnostic for approximate invariant subspaces. Instead of inspecting every vector in V, compute the norm of the residual map. The operator norm of R is the largest escape length among unit trial-coordinate inputs.

The Frobenius or Hilbert–Schmidt norm measures the total squared escape over an orthonormal trial basis. Those two norms quantify different aspects of the same map.

## A worked two-dimensional example

Consider the real symmetric matrix with first row zero, one, and second row one, three. Choose the horizontal axis as our one-dimensional trial space. E sends a scalar t to t times the first basis vector.

The Ritz operator is multiplication by the upper-left matrix entry, which is zero. But A applied to the horizontal unit vector is the vertical unit vector. Therefore R sends one to the vertical unit vector. Its norm is one.

The trial space is not invariant. Importantly, the residual is orthogonal to the trial line as Galerkin orthogonality predicts.

If we instead choose a normalized eigenvector of A as our trial vector, the compressed scalar equals its exact eigenvalue and R becomes zero. The residual detects exact invariance regardless of which orthonormal coordinates we use for the resulting one-dimensional space.

## A residual depends on the chosen trial operator

The Ritz operator is natural, but sometimes the numerical method supplies a separate self-adjoint trial operator A zero. Then we may define a more general residual R zero equals A E minus E A zero.

Insert and subtract E M. We obtain a decomposition into two terms: the perpendicular escape R, and the trial-space discrepancy E times M minus A zero.

The two terms are orthogonal on every trial vector. The first lies in V perpendicular, while the second lies in V. Pythagoras therefore gives a sum-of-squares formula for the residual's output length.

If A zero equals M, the internal discrepancy disappears. But in perturbation arguments we sometimes choose A zero from an unperturbed operator or a simpler model, and retaining the general residual is advantageous.

Take the example where A is diagonal with entries zero and five. Let the trial unit vector make an angle theta with the horizontal axis. If A zero is multiplication by zero, the general residual has length five times the sine of theta. If instead A zero is the Ritz value five sine squared theta, the residual length is five times the absolute value of sine theta times cosine theta.

These are two different residuals for the same trial line. Both are mathematically valid. Their associated spectral gaps to the exact complement differ, so a theorem must pair each residual with its own specified trial operator.

## Make the exact subspace explicit

Now let U be the exact target subspace. Its orthogonal projection is Q. Because A is self-adjoint and U is reducing, we may choose orthonormal coordinate maps F zero for U and F one for its orthogonal complement.

These satisfy F zero F zero adjoint plus F one F one adjoint equals the identity. They give the two exact blocks of A.

The residual R, by contrast, is computed from E and A zero. It does not need to lie in the exact complement U perpendicular. Galerkin orthogonality places the Ritz residual in the complement of V, which is usually a different subspace.

This distinction is essential. That component is the right-hand side of a Sylvester equation.

## What remains true in infinite dimensions

The formulas for projections and compressions remain valid for bounded self-adjoint operators on Hilbert spaces. If A is unbounded, writing A E requires that E send the trial operator's domain into the domain of A. We also need a bounded residual extending the algebraic difference on that common domain.

For the unbounded case, domain inclusion only makes the difference A E minus E A zero meaningful on the trial-operator domain. We must separately verify that the difference extends boundedly and, when applying a closed-operator Sylvester estimate, that the complementary overlap respects the domain of the unwanted exact block.

For now the finite-dimensional computation is enough to fix the geometry. Trial coordinates E, compressed operator M, residual R, exact coordinates F zero and F one. We have separated these roles, proved Galerkin orthogonality, and identified the residual as an escape from the trial space.

Projection of the residual onto the exact complementary subspace produces a Sylvester equation. Its solution measures the trial vectors that leak out of the selected spectral subspace, and the spectral gap controls their size.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For a finite-dimensional isometry `E : F → H`, define `P=EE*`, `M=E*AE`, and `R=AE−EM`. Then `E*R=0` and `R=(I−P)AE`. For an arbitrary trial operator `A₀`, `R₀=AE−EA₀=R+E(M−A₀)`; the two summands have orthogonal ranges. With unbounded `A`, use common-domain hypotheses before asserting a bounded extension.

### Source declaration excerpts

`DavisKahan/BoundedOperator/TrialResidual.lean` — `trialResidualCore` (exact declaration header; body omitted):

```lean
@[expose] noncomputable def trialResidualCore
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] : Z →L[ℂ] H :=
```

`DavisKahan/BoundedOperator/TrialResidual.lean` — `trialResidualCore_eq_ritzDifference` (exact declaration header; body omitted):

```lean
theorem trialResidualCore_eq_ritzDifference
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] [CompleteSpace Z] :
    trialResidualCore T Z =
      T ∘L Z.subtypeL - Z.subtypeL ∘L compressOperator Z T := by
```

`DavisKahan/BoundedOperator/TrialResidual.lean` — `trialResidualCore_apply_mem_orthogonal` (exact declaration header; body omitted):

```lean
theorem trialResidualCore_apply_mem_orthogonal
    (T : H →L[ℂ] H) (Z : Submodule ℂ H)
    [Z.HasOrthogonalProjection] (z : Z) :
    trialResidualCore T Z z ∈ Zᗮ := by
```

**Mapping.** In `TrialResidual.lean`, `Z.subtypeL` is the isometric inclusion of the trial subspace; `compressOperator Z T` is its Ritz compression; `trialResidualCore` takes values in `Zᗮ`. In the source's general `residual A X M`, `X` corresponds to the trial map `E`, and `M` to the chosen trial operator. The source code explicitly distinguishes projected Ritz residuals from arbitrary trial residuals.
