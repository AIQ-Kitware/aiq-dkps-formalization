# 104000 — Real versions of unbounded Sylvester bounds

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `090000` form gaps, `093000` domain-aware Sylvester equations, `094000` unbounded Sylvester estimates, `096000` approximation numbers, `102000–103000` real complexification and spectral descent. **Next:** `105000` proof-readiness assembly.

<!-- BEGIN SPOKEN LECTURE -->

# Transferring the unbounded Sylvester theorem back to real space

Our target today is a real Hilbert-space version of the unbounded Sylvester estimate. We have two possibly unbounded self-adjoint operators, a bounded unknown X between their spaces, and a bounded right-hand side C. Under a suitable spectral-gap hypothesis and a domain-aware equation, we want to control X by C in every symmetric ideal covered by Ky Fan dominance.

The complex Hilbert-space Sylvester theorem gives the needed estimate for a domain-aware equation under the prescribed spectral-gap condition. To transfer that estimate, we must complexify the domain as well as the operator formula. We must also show that every finite Ky Fan gauge returns to the original real space with no change in the constant.

The proof will have four stages: complexify the domains, complexify the equation, preserve the spectral gap, and descend finite Ky Fan estimates to the desired real ideal.

## State the real problem precisely

Let A be self-adjoint on a real Hilbert space E, and B self-adjoint on another real Hilbert space F. Either may be unbounded.

Let X and C be bounded real-linear maps from F into E. The Sylvester equation is A X minus X B equals C.

For bounded matrices, this is an identity on every vector. For unbounded operators it must be interpreted on the domain of B. We require X to send every vector in the domain of B into the domain of A. Only then is A X x defined for such an input x. On that domain, the equation asserts that A X x minus X B x equals C x.

We also assume a positive gap delta, expressed through the prescribed form-bounded Sylvester gap condition. That condition allows an interval-versus-exterior configuration or either orientation of ordered half-line separation, depending on the branch.

Merely requiring the spectra to be different sets is insufficient. An ordered gap, an interval-versus-exterior gap, and arbitrary pairwise separation support different Sylvester norm estimates, so the gap configuration must be stated before applying a bound.

## Complexify the domain, not merely the formula

A real unbounded operator A has a domain D of A, a linear subspace of E. Construct the complexification of that domain by taking all x plus i y such that both x and y belong to D of A.

Define the complexified operator by applying A coordinatewise. It sends x plus i y to A x plus i A y.

Why do we need both coordinate conditions? Because an arbitrary complex scalar mixes real and imaginary components. If we allowed only the real component to lie in the domain, multiplication by i would send a legal vector to one with an illegal real component. Requiring both coordinates restores a complex-linear domain.

The graph of the complexified operator consists of pairs of complex vectors whose real-coordinate graph point and imaginary-coordinate graph point both lie in the graph of A.

If the original graph is closed, its product with itself is closed, and the coordinate homeomorphism preserves closedness. Therefore the complexified graph is closed.

If the original domain is dense, the product of two dense domains is dense, so the complexified domain is dense as well.

These two facts give the analytic prerequisites for working with closed operators in complex Hilbert space.

## Transfer self-adjointness and the equation

To transport the adjoint relation, we evaluate the complex inner product coordinatewise. The real and imaginary pairings reduce to the original real adjoint pairings, just as they did for bounded operators.

An unbounded adjoint has its own domain. To commute complexification with adjoints, prove that the complexified adjoint domain consists exactly of pairs whose real coordinates lie in the original adjoint domain. This domain equality then carries self-adjointness to the complexified operator.

Now consider the Sylvester equation. If x and y both lie in the domain of B, then X x and X y lie in the domain of A by assumption. Hence the complexified X maps the complexified domain of B into that of A.

Apply the real Sylvester identity separately to x and y. Combining those two real equalities gives the complex equation on x plus i y. The right-hand side is the complexification of C.

This is the exact point where domain discipline pays off. We do not multiply two unbounded symbols as if they were ordinary bounded matrices. We establish a legal identity on a specified domain and transport that identity coordinate by coordinate.

## Preserve the gap hypothesis

Consider ordered separation first. Suppose the quadratic form of A is bounded below by a real threshold, while the quadratic form of B is bounded above by a lower threshold, leaving a positive gap.

The quadratic form of the complexified A at x plus i y is the sum of the real quadratic forms at x and y. The squared norm of the complex vector is likewise the sum of the two squared real norms. Therefore the same lower form bound holds on the complexified operator. The upper bound for B transfers by the same argument.

The reversed ordering is symmetric.

For the interval-versus-exterior branch, we use preservation of the real spectral information and the required resolvent properties. The domain, graph, and real resolvent set have already been transported, so the interval-exterior gap condition survives with the same delta.

Thus the complexified operators satisfy the exact gap hypothesis required by the complex unbounded Sylvester theorem. The numerical gap and its orientation are preserved under complexification.

## Apply the complex theorem to one finite prefix

Fix a positive integer k. Consider the sum of the first k approximation singular values of a bounded operator. This is its k-th Ky Fan gauge.

The complex unbounded Sylvester theorem applies to this finite Ky Fan ideal. It gives delta times the k-th Ky Fan gauge of complexified X at most the k-th Ky Fan gauge of complexified C.

Our task is to remove the word complexified from both sides.

For finite-dimensional matrices this is immediate from their singular values. In arbitrary Hilbert spaces, it requires an actual theorem about approximation numbers.

One direction is straightforward. A real rank-at-most-k approximant can be complexified without changing its rank bound or approximation error. Thus the complex approximation number is no larger than the real one.

For the reverse direction, use the singular-value min–max characterization. A sufficiently good real lower-bound witness consists of an appropriate collection of independent real vectors on which the operator has a uniform lower norm bound. Complexify that independent family. Its complex span has the same number of independent directions, and the lower bound extends from real vectors to arbitrary complex combinations because the squared norm splits into real and imaginary contributions.

This gives the reverse approximation-number inequality. The two approximation numbers are equal at every index. Summing the first k of them gives exact preservation of every finite Ky Fan prefix.

Therefore the complex estimate descends unchanged to the real estimate: delta times the k-th Ky Fan gauge of X is at most the k-th Ky Fan gauge of C.

## Why finite prefixes are not the final conclusion

We now have a family of inequalities, one for every finite k. But the desired conclusion concerns an arbitrary real symmetric ideal family, and such an ideal may not contain every bounded operator.

We assume the ideal has the Ky Fan dominance property. We also assume C belongs to that ideal.

Apply the dominance principle to the scaled prefix inequality. Since delta is positive, the prefixes of X are bounded by those of C divided by delta. The dominance principle then proves both that X belongs to the ideal and that its real gauge is at most the real gauge of C divided by delta.

Equivalently, delta times the real gauge of X is at most the real gauge of C.

Membership is a necessary part of the conclusion. If we tried to write the ideal norm of X before proving it belongs, we could be applying a finite-valued norm outside its legal domain.

Equality of real and complex ideal gauges is not automatic. The argument first establishes equality of every finite Ky Fan prefix, then applies the particular dominance theorem required by the real ideal.

## A diagonal example to test the constants

Take E and F to be real two-dimensional spaces. Let A have diagonal entries three and five, while B has entries minus one and minus two. The smallest difference between an A eigenvalue and a B eigenvalue is four, so the ordered gap delta may be taken as four.

The Sylvester equation says that each entry of X equals the corresponding entry of C divided by the difference between the chosen diagonal eigenvalues. The smallest denominator is four. For example, if C has a single one in the upper-left corner, X has one quarter in that corner and zeros elsewhere. The bound is attained in operator norm, Hilbert–Schmidt norm, and trace norm.

In an unbounded example the coordinates may run over an infinite sequence instead, and the domain restrictions become essential. The same ordered separation is what makes the uniform constant possible.

## The completed real theorem

We have transferred a domain-aware, self-adjoint, form-gap Sylvester equation to complex space, obtained all finite Ky Fan inequalities there, and descended them exactly. With real Ky Fan dominance and membership of C, we conclude membership of X and the sharp scaled gauge inequality.

The argument shows why complexification is useful: it lets us reuse a proved complex theorem while keeping the real mathematical statement, its gap constant, and its membership requirements intact.

That final exercise will reconstruct the full chain from an unbounded residual identity to a symmetric-ideal sine-angle estimate.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

The domain-aware real equation has `A : E →ₗ.[ℝ] E`, `B : F →ₗ.[ℝ] F`, `X C : F →L[ℝ] E`, `X(B.domain) ⊆ A.domain`, and `(AX−XB)x=Cx` on `B.domain`. Partial-map complexification transports closed domains, self-adjointness, resolvents, form bounds, and the Sylvester equation. Approximation numbers and all finite Ky Fan prefixes are exactly preserved. A real `SymmetricOperatorIdealFamily` needs `IsKyFanDominant` and `N.Mem C` to derive `N.Mem X` together with `δ N.gaugeReal X ≤ N.gaugeReal C`.

### Actual Lean source declarations

`DavisKahan/SpectralTheory/PartialMap/Complexification.lean` — `mem_domain_iff` (exact declaration header; proof omitted):

```lean
@[simp] theorem mem_domain_iff
    (A : E →ₗ.[ℝ] E)
    (z : Eℂ) :
    z ∈ domain A ↔ re z ∈ A.domain ∧ im z ∈ A.domain := by
```

`DavisKahan/SpectralTheory/PartialMap/Complexification.lean` — `closedSylvesterEquation_complexify` (exact declaration header; proof omitted):

```lean
theorem closedSylvesterEquation_complexify
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    {X C : F →L[ℝ] E}
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C) :
    _root_.LinearPMap.SylvesterEquation (complexify A) (complexify B)
      (RealComplexification.complexify X)
      (RealComplexification.complexify C) := by
```

`DavisKahan/SpectralTheory/PartialMap/Complexification.lean` — `isSelfAdjoint_complexify` (exact declaration header; proof omitted):

```lean
theorem isSelfAdjoint_complexify
    {A : E →ₗ.[ℝ] E}
    (hA : IsSelfAdjoint A) :
    _root_.IsSelfAdjoint (complexify A) := by
```

`DavisKahan/OperatorIdeal/ComplexificationApproximation.lean` — `kyFanApproximationGauge_complexify` (exact declaration header; proof omitted):

```lean
theorem kyFanApproximationGauge_complexify
    (T : E →L[ℝ] F) (k : ℕ) :
    ((RealComplexification.complexify T).kyFanGauge k : ℝ) =
      (T.kyFanGauge k : ℝ) := by
```

`DavisKahan/Sylvester/RealUnbounded.lean` — `davisKahan1970_sylvester_real` (exact declaration header; proof omitted):

```lean
theorem davisKahan1970_sylvester_real
    (N : TauCeti.SymmetricOperatorIdealFamily ℝ)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℝ] E} {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hEq : _root_.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧
      δ * N.gaugeReal X ≤
        N.gaugeReal C := by
```

**Type and hypothesis map.** The complex partial-map domain has real and imaginary coordinates in the original domain. `closedSylvesterEquation_complexify` transports an equation with legal domain compositions; self-adjointness and the form-gap conditions are transported separately. Finite Ky Fan gauges are preserved exactly for real bounded maps. The real Sylvester conclusion assumes a `SymmetricOperatorIdealFamily ℝ`, its `IsKyFanDominant` instance, positive `δ`, a `FormBoundedSylvesterGap`, the domain-aware equation, and `N.Mem C`; it returns both `N.Mem X` and the scaled real gauge bound.

These Lean snippets are copied exactly from the supplied DKPS repository snapshot. The narration is an independent mathematical derivation; this appendix does not claim that the narrated text was compiled in Lean. Foundational results currently in `ForTauCeti` may have been developed in DKPS before upstreaming.
