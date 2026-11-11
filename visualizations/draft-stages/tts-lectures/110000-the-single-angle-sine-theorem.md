# 110000 — The single-angle sine theorem

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `071000` compressed Sylvester identity; `094000` unbounded Sylvester estimates; `098000–101000` ideal membership; `105000` proof assembly; `108000–109000` residual and directed sine. **Next:** `111000` graph subspaces and tangent geometry.

<!-- BEGIN SPOKEN LECTURE -->

# The single-angle sine theorem

Suppose a self-adjoint operator has an invariant subspace that we want to identify. We have calculated another subspace that appears to approximate it. How can we estimate the angle between the two without knowing the exact subspace's basis vectors in advance?

A natural test is to apply the operator to our trial vectors and measure how badly they fail to satisfy the operator equation we expect. That failure is a residual.

The Davis–Kahan sine theorem says that a residual can control the angle to a chosen exact subspace, provided the trial operator is spectrally separated from the action of the original operator on the exact subspace's unwanted complement.

The separation is indispensable. An exactly invariant trial space can be the wrong invariant space, so a zero residual alone is not enough to identify the target.

Let's discover the inequality in the plane. Then we'll state its precise hypotheses and explain why an operator equation called the Sylvester equation gives the general result.

## The whole calculation in two dimensions

Take the real plane. Let A be diagonal, with eigenvalue zero along the horizontal axis and eigenvalue five along the vertical axis.

Suppose the exact subspace we want is the horizontal axis. Call it U. Its orthogonal complement is the vertical axis, where A acts by multiplication by five.

Now choose a trial line V making an angle theta with the horizontal, where theta lies between zero and ninety degrees. A unit vector along the trial line has horizontal coordinate cosine theta and vertical coordinate sine theta.

We also need a trial operator, which prescribes how we think A acts on our trial coefficients. For this first example, choose the trial operator to be multiplication by zero. We're trying to model the horizontal eigenvalue.

Apply A to our trial vector. The horizontal coordinate becomes zero and the vertical coordinate becomes five times sine theta. The trial operator predicts zero, so that entire output is the residual. Its length is five times sine theta.

What is the geometric error? The component of our trial vector outside U is its vertical coordinate, sine theta. Its length is exactly the sine of the angle from V to U.

And what spectral separation do we have? The trial operator is zero, while A acts by five on U's complement. Those two actions differ by five.

So the residual length equals the spectral separation, five, multiplied by the sine of the angle.

In symbols spoken aloud: five times sine theta equals the residual length.

This is the basic form of the sine theorem. In the general setting the equality becomes a bound. But this example shows that the coefficient one in front of residual divided by gap can be attained exactly.

## Why the residual needs a gap

Change the example. Keep A and the exact horizontal target, but choose the trial line to be the vertical axis. This line is itself invariant under A.

If we choose the trial operator to be multiplication by five, the residual is zero. The equation is satisfied perfectly.

Yet the trial line is perpendicular to the target line. Its sine of angle is one, as large as possible.

The missing assumption is visible immediately. On the unwanted vertical complement, A also acts by five. The trial operator and the unwanted complementary operator have no spectral gap at all.

This example establishes the role of the gap before we introduce any abstraction. The residual says how accurately a trial space satisfies its own operator equation. The gap tells us whether that equation distinguishes the intended subspace from competing invariant subspaces.

## State the isometric theorem

Now work in a real or complex Hilbert space H. Let A be self-adjoint, the Hilbert-space analogue of a symmetric real matrix, with the operator agreeing with its adjoint. For the initial argument, assume A is bounded, so there are no domain complications.

Choose an exact closed subspace U that is reducing for A. Reducing means both U and its orthogonal complement are invariant under A. Let P be the orthogonal projection onto U.

Choose a trial coordinate Hilbert space F and an isometric map E from F into H. Isometric means E preserves lengths. The range of E is the trial subspace V.

Choose a self-adjoint trial operator A zero on F. It is the operator whose action E A zero predicts in ambient space. Define the residual R as A E minus E A zero. Thus R takes trial coefficients and returns ambient vectors.

On the unwanted orthogonal complement of U, let Lambda one denote A's self-adjoint action, expressed in coordinates of that complement.

Assume a positive number delta supplies an admissible spectral separation between A zero and Lambda one, strong enough to give a Sylvester estimate with constant one. A concrete sufficient configuration is an ordered gap: every spectral value of A zero is at most some real threshold a, and every spectral value of Lambda one is at least a plus delta. The reverse ordering also works. A specified interval-and-exterior separation is another admissible configuration.

Under such a gap hypothesis, the operator-norm conclusion is this: delta multiplied by the norm of the component of E outside U is no greater than the norm of R.

Since E is isometric, the norm of that escaping component is the sine of the largest directed angle from the trial subspace toward U, or the supremum of those sines in infinite dimensions.

So the largest directed sine is at most residual norm divided by delta.

The word directed is deliberate. We measure how much trial vectors fall outside U. If the dimensions differ, reversing the roles of U and V need not produce the same angle information.

There is also an operator-ideal version. An operator ideal is a family of operators equipped with norms that can distinguish, for example, a largest singular value from the sum of many singular values. The trace norm and Hilbert–Schmidt norm are familiar examples in finite dimensions. For a suitable symmetric ideal satisfying the required Ky Fan dominance property, and with R belonging to that ideal, the directed sine representative belongs to the ideal too and obeys the same gap-times-sine bound. Ky Fan dominance is the condition that lets inequalities about accumulated singular values control the chosen ideal norm.

That's the target. Now let's explain where it comes from.

## First bridge: isolate the unwanted component

Choose isometric coordinate maps for the exact subspace U and for its orthogonal complement. Call them F zero and F one.

Think of F one as taking coordinates of an unwanted direction and placing that vector in H. Its adjoint, F one star, extracts the unwanted coordinates from an ambient vector.

Apply F one star to the trial embedding E. The result is an operator X from trial coefficients into complementary coordinates. X tells us exactly how much each trial vector points outside the desired subspace.

Our two-dimensional example had just one trial coordinate and one complementary coordinate. There, X was the number sine theta.

Now apply F one star to the residual equation. The residual was A E minus E A zero.

Because U reduces A, the action of A on complementary coordinates is Lambda one. Therefore the complementary part of the residual is Lambda one X minus X A zero.

This is a Sylvester equation. Its unknown is X. The two coefficient operators are Lambda one and A zero. Its right-hand side is the complementary part of the residual.

In the plane, the equation reduces to five times sine theta minus zero times sine theta equals five times sine theta. Nothing has changed except notation.

In a larger Hilbert space, the same equation encodes all the complementary directions simultaneously.

## Second bridge: use spectral separation

A Sylvester equation has the form: one operator applied to X, minus X followed by another operator, equals a known right-hand side.

If the two coefficient operators have an admissible spectral gap, the Sylvester estimate bounds X in terms of that right-hand side. For the constant-one gap conditions stated here, delta times the operator norm of X is at most the norm of the complementary residual.

Why does the gap appear in the denominator? In the scalar case, an equation such as five times x equals r is solved by dividing r by five. If the two spectral actions get closer, the corresponding difference becomes harder to invert. The Sylvester theorem is the operator-level version of that calculation.

Extracting complementary coordinates cannot increase a vector's length. F one star is a contraction. Therefore the norm of the complementary residual is no greater than the norm of the full residual R.

Combining the two estimates gives delta times the norm of X no greater than the norm of R.

For a suitable symmetric operator ideal, the same reasoning uses the ideal's singular-value dominance and composition properties. Membership of R in that ideal must be included: boundedness alone does not imply that R is trace class or belongs to another specified ideal.

A positive distance between arbitrary interlaced spectral sets is not, by itself, a guarantee of the same sharp operator-norm Sylvester estimate. The constant-one conclusion uses the stated stronger gap configuration.

## Third bridge: turn X into an angle

We have estimated X, but the geometric theorem is about the trial subspace's angle to U. We need to identify those quantities.

Let S take a trial coefficient, embed it with E, and remove its orthogonal projection onto U. Thus S is the composition of identity minus P with E.

The output of S is an ambient vector perpendicular to U. The output of X gives the coordinates of that same vector in the complementary subspace.

Since F one is an isometry and its range is the entire complement, S equals F one applied to X. For every trial coefficient, S and X have outputs of the same length.

Equivalently, their Gram operators are equal: S star S equals X star X.

So S and X have the same positive modulus, the same relevant singular values, and the same operator norm. The positive modulus of S is the directed sine operator. In one dimension it is simply the scalar sine theta.

We can now replace X in the Sylvester bound with S. We obtain the desired inequality: delta times the directed sine norm is at most the residual norm.

The proof consists of three exact connections: extract the complementary residual to get a Sylvester equation, use the admissible gap to bound its solution, and identify that solution's size with the directed sine.

## Why the coefficient one is sharp

Return to the diagonal plane operator with eigenvalues zero and five. Use the horizontal target, an arbitrary trial line at angle theta, and the trial operator equal to zero.

The complementary spectrum is five. The gap is five. The complementary coordinate X is sine theta. The residual length is five sine theta.

Every inequality in the proof is an equality in this example. So a universal estimate with any smaller coefficient multiplying the residual on the right would fail for this family.

There is one detail worth preserving. The trial operator zero is not the Rayleigh–Ritz compression of A onto the tilted trial line, except when theta is zero.

The Ritz compression would instead be multiplication by five times sine theta squared. Its residual would have length five times sine theta times cosine theta, and its gap from the unwanted eigenvalue five would be five times cosine theta squared.

Both the residual and the gap change. We cannot use the smaller Ritz residual together with the old gap of five. The theorem compares a residual and a gap built from the same chosen trial operator.

## What changes with a nonisometric trial frame?

So far E preserves lengths. A general trial map may stretch or shrink its coefficient vectors. Suppose E is bounded below: every output has length at least epsilon times the input length, for some positive epsilon.

This lower frame bound guarantees that E has a closed range and a stable normalization to an isometric embedding. Normalization changes the coordinates used to measure the angle, but not the trial subspace itself.

The inverse normalization can amplify a coefficient vector by at most one divided by epsilon. Consequently the general inequality gains an epsilon factor on the left: delta times epsilon times the directed sine gauge is no greater than the residual gauge, under the corresponding general-frame hypotheses.

The scaling is necessary. If we multiply E by a positive constant, its residual scales by that constant while the angle of its range stays fixed. The frame lower bound scales by the same constant and restores the correct balance.

## What changes for unbounded operators?

For an unbounded self-adjoint A, the formula A E requires a domain condition. An arbitrary vector in the range of E need not lie in the domain of A.

We require the trial map to send the domain of A zero into the domain of A. On that legal domain, A E minus E A zero must agree with a residual that extends to a bounded operator. The complementary coordinate maps and Lambda one must also respect the relevant domains and intertwining identities.

With those assumptions and an admissible unbounded Sylvester gap, the same three bridges work. The complementary equation is first interpreted on its allowed domain; the Sylvester theorem supplies the bounded estimate; and the isometric geometry identifies the directed sine. The real case can be treated directly or through the appropriate complexification and descent arguments.

## What the theorem actually says

The residual alone measures how well a trial space satisfies its proposed equation. A gap between the trial operator and the unwanted complementary action identifies which exact subspace that equation can approximate.

With the correct gap, the escape of trial vectors from the target is bounded by residual divided by gap. The diagonal plane example gives equality, while the wrong-invariant-line example shows why the separation condition cannot be omitted.

A useful final check is to compare those two examples. In the first, the residual and gap are both tied to the trial operator zero, and the sine bound is sharp. In the second, the trial operator is five, the residual is zero, the angle is ninety degrees, and the complementary gap has vanished. Being able to explain that contrast is the core intuition behind the single-angle sine theorem.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Given a self-adjoint ambient `A`, a reducing exact decomposition `F₀,F₁`, an isometric trial `E`, self-adjoint `A₀,Λ₁`, a bounded residual `R` extending `AE−EA₀` on its common domain, an admissible `δ>0` `FormBoundedSylvesterGap A₀ Λ₁ δ`, and a Ky-Fan-dominant symmetric ideal `N` with `N.Mem R`, the isometric theorem gives `N.Mem((I−F₀F₀*)E)` and `δ N.gaugeReal((I−F₀F₀*)E) ≤ N.gaugeReal R`. Nonisometric trial maps with lower frame bound `ε>0` give `δε` on the left. For `A=diag(0,δ)`, `A₀=0`, `E=(cosθ,sinθ)`, equality holds. The gap must support the constant-one Sylvester estimate, such as an ordered form gap or a supported interval/exterior configuration; mere pairwise spectral distance need not do so in operator norm. In the plane example with \(A=\operatorname{diag}(0,5)\), the Ritz choice instead is \(A_0=5\sin^2\theta\), with \(\|R\|=5\sin\theta\cos\theta\) and complementary gap \(5\cos^2\theta\).

### Source declaration excerpts

`DavisKahan/Sources/DavisKahan1970/SineTheta/ScalarGeneric.lean` — `sinTheta_unbounded_formGap_idealFamily_rclike` (exact declaration header; body omitted):

```lean
theorem sinTheta_unbounded_formGap_idealFamily_rclike
    (N : TauCeti.SymmetricOperatorIdealFamily 𝕜)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    (D : UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G))
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/Theorem61.lean` — `result` (exact declaration header; body omitted):

```lean
theorem result
    (N : TauCeti.SymmetricOperatorIdealFamily ℂ)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    (P : GeneralSinThetaRepresentativeProblem (E := E) (F := F)
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/Theorem61.lean` — `result` (exact declaration header; body omitted):

```lean
theorem result
    (N : TauCeti.SymmetricOperatorIdealFamily ℂ)
    [N.toOperatorIdealFamily.IsKyFanDominant]
    (P : IsometricSinThetaRepresentativeProblem (E := E) (F := F)
```

**Mapping.** `ScalarGeneric.sinTheta_unbounded_formGap_idealFamily_rclike` states the canonical isometric result for `UnboundedSinThetaData` and a `SymmetricOperatorIdealFamily` with `IsKyFanDominant`. `Theorem61.GeneralSinThetaRepresentativeProblem.result` carries the nonisometric `frameLowerBound` and `gap` factors, and transfers to a paper-facing representative with matching singular-value data. The general paper-facing theorem's gap and domain hypotheses are contained in its `problem` data; one cannot infer them from the displayed result type alone.
