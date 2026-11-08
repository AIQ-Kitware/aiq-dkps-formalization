# 105000 — A full proof-readiness assembly

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `011000` orthogonal projections, `021000` compressions, `042000–046000` principal-angle geometry, `093000–094000` unbounded Sylvester estimates, `098000–101000` operator ideals, `102000–104000` real complexification and transfer. **Next:** `106000` the perturbation question.

<!-- BEGIN SPOKEN LECTURE -->

# Reconstructing the route from residual to sine-angle estimate

This is the final lecture in the advanced foundations sequence. Rather than introduce another isolated theorem, we will assemble a complete perturbation argument using the mathematical tools we have built.

Our target is a symmetric-ideal sine-angle bound for possibly unbounded self-adjoint operators. We will start with a trial map and its residual, pass to coordinates in an exact spectral complement, solve a Sylvester equation, and recover the sine of the angle between the trial space and the exact space.

Every step will have an explicit hypothesis. We will also work through a two-dimensional example in which the final bound is an equality. That example will let us check the gap factor and the normalization factor independently.

## Name the spaces and operators

Let H be the ambient Hilbert space. Let A be a possibly unbounded self-adjoint operator on H.

Suppose A has an exact reducing decomposition into two orthogonal parts. We represent the first part using an isometric coordinate map F zero from one coordinate Hilbert space into H. We represent the complementary part using an isometric coordinate map F one from another coordinate Hilbert space into H.

Their ranges are orthogonal and together span the ambient space. Because the decomposition reduces A, the action of A on the complement is represented by a self-adjoint operator Lambda one. In particular, applying A to F one y agrees with F one applied to Lambda one y for vectors in the appropriate operator domain.

Now introduce a trial coordinate Hilbert space and a bounded trial map E zero from that space into H. E zero need not be an isometry. We will require a lower frame bound: its output length is at least epsilon times its input length, with epsilon positive.

This ensures that E zero is injective, its range is closed, and it has a bounded inverse from that range back to its coordinate space.

Finally choose a self-adjoint trial operator A zero on the trial coordinate space. It might be a compression or a separate reference operator. Define the residual by comparing A E zero against E zero A zero.

The residual records the failure of the trial map to intertwine the two operators exactly.

## Do not skip the common-domain hypothesis

For bounded matrices, the residual is simply A E zero minus E zero A zero. For unbounded A, the expression A E zero x is defined only when E zero x belongs to the domain of A.

The source-paper common-domain condition identifies the set of trial coordinates x for which E zero x belongs to the domain of A with the domain of A zero itself.

So the two sides of the residual identity are defined on exactly the same dense subspace. We require the residual to agree there with a bounded operator R defined on the entire trial coordinate Hilbert space.

We also require the complementary coordinate map F one to carry the domain of Lambda one into the domain of A, and to intertwine their actions there.

Without these conditions, the next calculation might look correct as symbolic matrix multiplication while being meaningless on an actual vector. We will use the domain information at each stage.

## Compress the residual into the complementary space

Define X to be F one adjoint composed with E zero. This map measures how much the trial vectors lie in the exact complementary subspace.

It is bounded because both factors are bounded. And on the domain of A zero, the definition of the residual gives A E zero x minus E zero A zero x equals R x.

Apply F one adjoint to both sides. The second term becomes X A zero x. The right-hand side becomes F one adjoint R x.

For the first term, use the reducing decomposition. Because F one intertwines the complementary operator with A, its adjoint converts the action of A on a legal domain vector into Lambda one applied to that vector's complementary coordinate. In particular, F one adjoint A E zero x becomes Lambda one X x.

We have derived the complementary Sylvester equation: Lambda one X minus X A zero equals F one adjoint R, on the domain of A zero.

This is a proof, not a choice of notation. The equation follows from the residual identity and the exact reducing property. The domain assumptions ensure that every term exists.

## Apply the right kind of spectral separation

Assume a positive gap delta between the trial operator A zero and the complementary operator Lambda one, in one of the configurations covered by the unbounded Sylvester theorem.

These configurations include an ordered half-line separation and the stated interval-versus-exterior condition. A mere assertion that the two spectra are unequal would not suffice for the same uniform ideal estimate.

The unbounded Sylvester theorem controls X by its right-hand side. In a symmetric ideal family with the needed Ky Fan dominance property, membership of F one adjoint R implies membership of X, and delta times the gauge of X is at most the gauge of F one adjoint R.

Now F one adjoint is a contraction, because F one is an isometry. Therefore the ideal-composition law bounds the gauge of F one adjoint R by the gauge of R.

Combining the inequalities gives delta times the gauge of X at most the gauge of R.

This is already a residual-to-complementary-block estimate. But X still contains the arbitrary normalization of the trial map E zero. An angle between subspaces should not change when we multiply the entire trial map by two.

## Remove the trial-frame normalization

Use the polar decomposition of E zero. Because E zero has a positive lower frame bound epsilon, its modulus has spectrum bounded below by epsilon. It is therefore invertible, and the inverse has norm at most one divided by epsilon.

Write E zero as U times its modulus. Here U is an isometry from the trial coordinate space onto the closed range of E zero.

The map U gives orthonormal coordinates for the trial subspace. It is the right object for defining its principal angles with the exact space.

Recall X equals F one adjoint E zero. Substitute E zero equals U times its modulus. Then X equals F one adjoint U times the modulus of E zero.

Multiply on the right by the inverse modulus. We obtain F one adjoint U equals X times that inverse.

The ideal-composition inequality now bounds the gauge of F one adjoint U by one divided by epsilon times the gauge of X. Multiply by delta epsilon and combine with the preceding Sylvester estimate. We get delta times epsilon times the gauge of F one adjoint U at most the gauge of R.

That epsilon factor is essential. If the trial map is rescaled, its residual rescales in the same way, while its subspace and sine angles do not. The lower frame bound keeps the inequality consistent under this rescaling.

## Identify the sine of the angle

Let P be the orthogonal projection onto the range of the exact first coordinate map F zero. Because F zero and F one give a complete orthogonal decomposition, one minus P equals F one F one adjoint.

The part of U that escapes the exact first subspace is one minus P applied to U. Its norm measures the largest directed sine of the angle between the trial range and the exact range.

Compute its Gram operator. The adjoint of one minus P times U, followed by one minus P times U, equals U adjoint F one F one adjoint U.

The Gram operator of F one adjoint U is exactly the same: U adjoint F one F one adjoint U.

Therefore the two maps have the same modulus and the same nonzero singular-value information. They represent the same directed sine geometry, although their targets are different coordinate spaces.

By polar and rectangular ideal invariance, any legitimate symmetric gauge comparison can use either representative. We obtain the sine-angle estimate: delta times epsilon times the ideal gauge of the directed sine is at most the ideal gauge of the residual.

This statement includes membership of the sine representative in the ideal, provided the residual belongs to it and the ideal satisfies the required dominance assumptions.

## Verify the constants in the plane

Take the ambient plane with standard basis vectors e one and e two. Let A be diagonal, with eigenvalues zero and five.

Choose the exact target subspace to be the first coordinate axis. Its complement is the second axis, and Lambda one is multiplication by five.

Choose the trial unit vector u to make an angle of thirty degrees with the first axis. Its first coordinate is the square root of three divided by two, and its second coordinate is one half.

Define E zero to send a scalar t to two t times u. The lower frame bound is epsilon equals two. Let A zero be multiplication by zero.

The residual is A E zero minus E zero A zero. Since A zero vanishes and the second coordinate of E zero applied to one is exactly one, the residual sends one to five times e two. Its operator norm is five.

The gap between Lambda one, which is five, and A zero, which is zero, is delta equals five.

The complementary block X equals F one adjoint E zero. Applied to one it gives one. Thus the Sylvester estimate reads five times one is at most five, with equality.

After normalizing E zero, we recover U applied to one equals u. The complementary coordinate F one adjoint U is one half, precisely the sine of thirty degrees.

The final estimate reads gap five times lower frame bound two times sine one half is at most residual norm five. Both sides equal five.

This calculation checks all three factors. If we accidentally omitted epsilon, the inequality would remain true here but fail to record the scaling correctly. If we accidentally used the sine of the complementary angle, the numerical result would change. And if we used the spectral gap to the exact first eigenvalue instead of the complementary eigenvalue, we would have solved the wrong Sylvester equation.

## What the assembly does and does not prove

We have reconstructed the entire route: legal unbounded residual, exact complementary compression, self-adjoint Sylvester gap, membership and gauge estimate, lower-frame normalization, and identification with a directed sine modulus.

The construction works in real or complex Hilbert spaces when the corresponding ideal and Sylvester hypotheses are available. In real Hilbert spaces, the complexification and Ky Fan descent from the previous lecture supply the real estimate.

We have not asserted that arbitrary disjoint spectra yield this sharp bound, nor that every bounded residual belongs to every proper ideal. Those would change the theorem's hypotheses.

The mathematical toolkit is now assembled. Next we can begin perturbation theory proper: choose exact and approximate spectral subspaces, calculate their residuals, and determine which spectral separation conditions allow quantitative angle bounds.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let `A` be self-adjoint on ambient `H`, let `F₀,F₁` define an exact reducing orthogonal decomposition, and let `E₀` have lower bound `‖E₀x‖ ≥ ε‖x‖` for `ε>0`. Require `HasCommonDomain A A₀ E₀`, the complement-domain intertwining property for `F₁` and `Λ₁`, and a bounded residual `R` agreeing with `A E₀−E₀ A₀` on the common domain. Then `X=F₁*E₀` satisfies the domain-aware Sylvester equation `Λ₁ X−X A₀=F₁*R`. A compatible unbounded gap `δ>0`, a symmetric ideal with Ky Fan dominance, and `Mem R` give `Mem X` and `δ gauge(X) ≤ gauge(R)`. The polar normalization `E₀=U|E₀|` with `‖|E₀|⁻¹‖≤1/ε` yields `δε gauge(F₁*U) ≤ gauge(R)`. Since `(F₁*U)* (F₁*U)=U* (I−P) U`, its modulus is the directed sine operator of the trial range relative to `P=F₀F₀*`.

### Actual Lean source declarations

`DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomain.lean` — `HasCommonDomain` (exact declaration header; proof omitted):

```lean
def HasCommonDomain
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (X : F →L[𝕜] E) : Prop :=
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainTheorems.lean` — `toUnboundedSinThetaData` (exact declaration header; proof omitted):

```lean
noncomputable def toUnboundedSinThetaData
    {𝕜 : Type u} [RCLike 𝕜]
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P : CommonDomainSinThetaData 𝕜 E F G H) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) :=
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/CommonDomainTheorems.lean` — `result_every_unitarilyInvariantNorm` (exact declaration header; proof omitted):

```lean
theorem result_every_unitarilyInvariantNorm
    (P : RealCommonDomainTheorem61Data
      (E := E) (F := F) (G := G) (H := H))
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/ScalarGeneric.lean` — `sinTheta_unbounded_formGap_idealFamily_rclike` (exact declaration header; proof omitted):

```lean
theorem sinTheta_unbounded_formGap_idealFamily_rclike
    (N : TauCeti.SymmetricOperatorIdealFamily 𝕜)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
```

**Type and hypothesis map.** The exact common-domain predicate identifies the pullback of the ambient operator domain under the trial map with `A₀.domain`. The conversion to `UnboundedSinThetaData` preserves the source residual. The real common-domain Theorem 6.1 conclusion requires a lower trial-frame bound `ε`, a form-bounded gap `δ`, self-adjoint and exact-decomposition data, a sine representative and residual membership in a symmetric norm family. The scalar-generic internal theorem is written for an isometric trial map, before the paper-facing lower-frame normalization. It must not be read as dropping the `ε` hypothesis from the external theorem.

These Lean snippets are copied exactly from the supplied DKPS repository snapshot. The narration is an independent mathematical derivation; this appendix does not claim that the narrated text was compiled in Lean. Foundational results currently in `ForTauCeti` may have been developed in DKPS before upstreaming.
