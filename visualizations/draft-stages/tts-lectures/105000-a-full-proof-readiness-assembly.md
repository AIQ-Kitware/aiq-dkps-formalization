# 105000 — A full proof-readiness assembly

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `011000` orthogonal projections, `021000` compressions, `042000–046000` principal-angle geometry, `093000–094000` unbounded Sylvester estimates, `098000–101000` operator ideals, `102000–104000` real complexification and transfer. **Next:** `106000` the perturbation question.

<!-- BEGIN SPOKEN LECTURE -->

# How a residual becomes a bound on the angle between subspaces

Suppose the plane has two distinguished directions: horizontal and vertical. An operator A kills the horizontal component and multiplies the vertical component by five.

The horizontal line is an exact invariant subspace. We want to approximate it with a line tilted upward by thirty degrees.

Choose a unit vector u along that tilted line. Its horizontal coordinate is the square root of three divided by two. Its vertical coordinate is one half.

Apply A to u. The result is a vertical vector of length two and a half. If we propose zero as the trial eigenvalue, this output is exactly the residual: the error in the proposed eigenvalue equation.

Now notice something. The vertical component of u has length one half. That is the sine of its angle with the horizontal axis. And the residual has length five times one half.

The factor five is the spectral separation between the trial eigenvalue zero and the unwanted vertical eigenvalue five.

In this example, the relationship is exact: gap times sine of the angle equals residual norm.

We want to understand how that elementary calculation extends to Hilbert spaces, possibly unbounded self-adjoint operators, nonorthonormal trial coordinates, and symmetric operator ideals.

The proof has three main ideas. Project the residual into the unwanted spectral directions. Use a Sylvester equation and spectral separation to control that projection. Then remove any artificial scaling of the trial coordinates to recover an actual subspace angle.

## See the complementary equation in the plane

In our example, let the exact target line be the horizontal axis and its orthogonal complement be the vertical axis.

If we keep only the vertical coordinate of u, we get one half. Call that the complementary coordinate X.

The operator A acts on the vertical axis as multiplication by five. Our proposed trial eigenvalue is zero. So the complementary-coordinate equation is simply five times X minus X times zero equals the vertical component of the residual.

The right-hand side is two and a half. The left-hand side is five times one half, also two and a half.

That's a one-dimensional Sylvester equation.

We can already see the structure. The gap lets us divide the complementary residual by five. What we recover is the amount of the trial vector that lies outside the target space.

But before generalizing, there's one complication that a geometric angle shouldn't have: dependence on how we scale our coordinates.

## A trial map may not be normalized

Instead of sending the scalar one to u, suppose our trial map sends it to two u. The trial subspace is still exactly the same tilted line.

The complementary coordinate is now two times one half, which is one. The residual is also twice as large, with length five.

The Sylvester equation still reads five times X equals the complementary residual, and the resulting inequality is still sharp. But X is now one, while the sine of the geometric angle remains one half.

We need a separate normalization step.

In this scaled example, the trial map stretches every scalar by two. Its lower frame bound is two. Dividing X by that stretch recovers the sine of the angle.

This is why a general theorem involving a trial map needs a lower frame bound as well as a spectral gap.

## Identify the spaces one at a time

Now let H be a real or complex Hilbert space, and let A be a self-adjoint operator on H. It may be unbounded.

Choose an exact reducing subspace for A. Call its orthogonal projection P. Reducing means both that subspace and its orthogonal complement are preserved by the operator in the domain-aware sense.

Represent the exact target subspace by an isometric coordinate map F zero. Represent its orthogonal complement by another isometric coordinate map F one. The ranges of these maps are orthogonal and together fill H.

On the complement, the action of A is represented by a self-adjoint operator Lambda one. Think of Lambda one as multiplication by five in our plane example.

Now introduce a trial coordinate space and a bounded map E zero from that coordinate space into H. Its range is the trial subspace. We assume a positive lower frame bound epsilon: the length of E zero x is at least epsilon times the length of x.

This condition keeps the trial map from collapsing nonzero coordinates. It also ensures that its range is closed and its positive modulus is invertible on the trial coordinate space.

Finally, choose a self-adjoint trial operator A zero on the trial coordinate space. In a Rayleigh–Ritz setting, it may come from compression; the abstract argument also allows other choices.

Our residual compares applying the ambient operator after E zero with applying the trial operator before E zero. In the plane example, the trial operator was simply multiplication by zero.

## Make the residual legal when A is unbounded

If A is unbounded, it cannot be applied to every vector in H. So an expression like A applied to E zero x needs a domain hypothesis.

The common-domain condition says that E zero x belongs to the domain of A exactly when x belongs to the domain of A zero.

On that common domain, define the residual by A E zero x minus E zero A zero x. We require this expression to agree with a bounded map R from the trial coordinate space into H.

This bounded extension is what allows us to measure a residual in operator or ideal norms. The domain equality ensures that we haven't written down an expression that is undefined on half of its terms.

Because the exact complement reduces A, its coordinate map also respects the operator domain: applying A in H and then taking the complementary coordinate agrees with applying Lambda one to that coordinate.

That is the second domain fact we'll need.

## Compress the residual and find the Sylvester equation

Define X by first applying E zero and then taking the F one adjoint coordinate. In words, X reports how much each trial vector lies in the exact complementary subspace.

This map runs from the trial coordinate space into the complementary coordinate space. It is bounded.

Take an input x in the domain of the trial operator A zero. The residual identity says that A E zero x minus E zero A zero x equals R x.

Apply F one adjoint. The second term becomes X A zero x. The first becomes Lambda one X x, because the complement is reducing and the domain condition makes that composition legal.

The right-hand side becomes F one adjoint R x.

Thus Lambda one X minus X A zero equals F one adjoint R, as an equation on the domain of A zero.

This is exactly the scalar equation from the plane, now with operators between Hilbert spaces.

## Use the spectral gap to control X

Suppose the trial operator A zero and the complementary operator Lambda one satisfy a positive form-bounded Sylvester gap condition with parameter delta.

The allowed configurations include ordered half-line separation and the specified interval-versus-exterior case. Mere disjointness of two spectra is not enough for this particular constant-one symmetric-ideal estimate.

Also assume we're using a symmetric ideal family with Ky Fan dominance and that the bounded residual R belongs to this ideal.

The unbounded Sylvester theorem now says that X belongs to the ideal and that delta times its gauge is at most the gauge of F one adjoint R.

But F one is an isometry. Its adjoint is a contraction. Composing the residual with it cannot increase an ideal gauge.

Therefore delta times the gauge of X is at most the gauge of R.

That is the abstract version of five times the complementary coordinate being bounded by the vertical residual.

We still need to convert the possibly scaled trial coordinates into actual angle geometry.

## Remove the coordinate scaling

Take the polar decomposition of E zero. It factors as an isometry U followed by the positive modulus of E zero.

Because the trial map has lower bound epsilon, its modulus has a bounded inverse with norm at most one divided by epsilon.

U is the normalized coordinate map onto the trial subspace. Scaling E zero by two may change its modulus, but U still represents the same geometric line or subspace.

Recall that X equals F one adjoint E zero. Substitute the polar decomposition of E zero. Then X equals F one adjoint U followed by the modulus.

Multiply on the right by the inverse modulus. We obtain F one adjoint U as X followed by that bounded inverse.

The ideal-composition inequality gives: the gauge of F one adjoint U is at most one divided by epsilon times the gauge of X.

Combine this with the Sylvester bound. The conclusion is that delta times epsilon times the gauge of F one adjoint U is at most the gauge of R.

In our scaled plane example, delta is five, epsilon is two, and F one adjoint U is one half. The left-hand side is five. The residual norm is five. Equality is restored, and the angle no longer depends on the chosen coordinate scale.

## Recognize the directed sine

Let P project onto the exact target subspace. The component of the normalized trial map U outside that space is the complementary projection, one minus P, applied to U.

For a unit vector along a trial line, the length of that component is exactly the sine of the angle to the exact line.

In more dimensions, the corresponding positive modulus records the directed sine geometry of the trial subspace relative to the exact subspace.

Why can we use F one adjoint U to measure the same thing? Because F one provides isometric coordinates on the exact complement. Taking the Gram operator of F one adjoint U gives U adjoint times one minus P times U. The Gram operator of the ambient complementary map, one minus P applied to U, is exactly the same.

So both maps have the same modulus. The symmetric ideal gauge does not change when a map is replaced by its modulus, even if its source and target spaces differ.

Thus the estimate for F one adjoint U is precisely an estimate for the directed sine representative.

## What the theorem really says

The full statement is now visible.

We begin with a self-adjoint ambient operator, an exact reducing decomposition, a trial map with a positive lower frame bound, a self-adjoint trial operator, and a bounded residual satisfying the common-domain identity.

We assume a positive allowed gap between the trial operator and the exact complementary operator. In a symmetric ideal family with Ky Fan dominance, if the residual belongs to that ideal, then the directed sine belongs as well.

Its gauge, multiplied by the gap and by the lower frame bound, is at most the gauge of the residual.

The plane example shows why each factor is present: the gap converts complementary error into displacement, and the frame bound converts coordinates into geometry.

The proof's main operation is also simple to describe. Take only the part of the residual pointing into the wrong spectral subspace, solve a domain-aware Sylvester equation for that component, and normalize the trial map to measure a true angle.

A small residual alone does not identify which spectral subspace the trial map approximates. The gap hypothesis must separate the trial spectrum from the exact complement. With that separation and the domain conditions in place, the sine estimate follows.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let `A` be self-adjoint on ambient `H`, let `F₀,F₁` define an exact reducing orthogonal decomposition, and let `E₀` have lower bound `‖E₀x‖ ≥ ε‖x‖` for `ε>0`. Require `HasCommonDomain A A₀ E₀`, the complement-domain intertwining property for `F₁` and `Λ₁`, and a bounded residual `R` agreeing with `A E₀−E₀ A₀` on the common domain. Then `X=F₁*E₀` satisfies the domain-aware Sylvester equation `Λ₁ X−X A₀=F₁*R`. A compatible unbounded gap `δ>0`, a symmetric ideal with Ky Fan dominance, and `Mem R` give `Mem X` and `δ gauge(X) ≤ gauge(R)`. The polar normalization `E₀=U|E₀|` with `‖|E₀|⁻¹‖≤1/ε` yields `δε gauge(F₁*U) ≤ gauge(R)`. Since `(F₁*U)* (F₁*U)=U* (I−P) U`, its modulus is the directed sine operator of the trial range relative to `P=F₀F₀*`.

### Worked example: gap, normalization, and directed sine

On \(H=\mathbb R^2\), let \(A=\operatorname{diag}(0,5)\) and target \(P=\operatorname{diag}(1,0)\). Define \(u=(\sqrt3/2,1/2)\), \(E_0t=2tu\), and \(A_0=0\). With \(F_1t=(0,t)\), the complementary operator is \(\Lambda_1=5I\), the form gap is \(\delta=5\), and the lower trial-frame bound is \(\varepsilon=2\).

The residual is \(Rt=A E_0t=(0,5t)\), so \(\|R\|=5\). The complementary block is \(X=F_1^*E_0=I\), giving \(\Lambda_1X-XA_0=5I=F_1^*R\). The polar-normalized trial isometry is \(Ut=tu\), and \(F_1^*U=\tfrac12 I\). Thus \(\delta\varepsilon\|F_1^*U\|=5\cdot2\cdot\tfrac12=5=\|R\|\). The directed sine is \(\sin(30^\circ)=1/2\).

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
