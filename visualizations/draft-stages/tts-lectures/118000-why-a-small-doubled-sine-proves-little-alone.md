# 118000 — Why a small doubled sine proves little alone

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `115000–117000` double-angle geometry and estimates. **Next:** `119000` spectral selection and repulsion.

<!-- BEGIN SPOKEN LECTURE -->

# Why a small doubled sine proves little alone

The sine-two-theta theorem bounds the sine of twice an angle. It is tempting to conclude that a sufficiently small perturbation forces the two subspaces to be close. That conclusion requires another argument. Sine of twice an angle is small when the angle is near zero, but also when the angle is near ninety degrees.

A bound on the sine of twice an angle leaves two possible angular branches. Matrix examples exhibit the ambiguity; continuity combined with spectral selection, or a direct small-angle theorem, supplies the additional information needed to select one branch.

## Begin with the scalar graph

Imagine an angle between zero and ninety degrees. Double it, then take its sine. The graph starts at zero, reaches one at forty-five degrees, and returns to zero at ninety degrees. Reflection about forty-five degrees leaves its value unchanged. Thus an angle of ten degrees and one of eighty degrees give the same doubled sine.

Suppose we know only that sine of twice theta is at most eta, with eta strictly between zero and one. Let gamma be half of arcsine eta. Since arcsine eta lies between zero and ninety degrees, gamma lies between zero and forty-five degrees.

The inequality now admits two possibilities: theta is at most gamma, or theta is at least ninety degrees minus gamma. The middle interval is excluded. This is not an informal drawing argument. On the interval from zero to forty-five degrees, sine twice theta is increasing; on the interval from forty-five to ninety degrees it is decreasing. Inverting on each interval proves the disjunction.

For eta equal to one half, gamma is fifteen degrees. An angle consistent with the estimate is at most fifteen degrees, or at least seventy-five degrees. It does not have to be small.

## The most decisive counterexample

Take the plane and let P project onto the horizontal axis. Let Q project onto the vertical axis. Their unique principal angle is ninety degrees. Their projection difference has operator norm one, so the subspaces are maximally separated by that metric.

Nevertheless, sine of twice their principal angle is zero. Both endpoints of the angle interval are annihilated by the doubled sine.

We can make this example fit the basic framework of a two-block perturbation statement without using any perturbation at all. Let T be diagonal with a low eigenvalue on the horizontal axis and a high eigenvalue on the vertical axis. Set S equal to T. Then the perturbation is zero. If we choose U to be the low eigenspace and choose V to be the high eigenspace of S, both are reducing subspaces, and the double-angle sine is zero. The theorem's numerical inequality is satisfied exactly. Yet V is the wrong spectral branch.

The absent ingredient is not a stronger numerical estimate; it is a rule that identifies which reducing subspace of S is intended. We could select the low eigenspace of S and obtain zero angle, or the high eigenspace and obtain ninety degrees, with the same zero perturbation.

## Extend the ambiguity to more than one angle

For two subspaces of equal finite dimension, there is a list of principal angles. A unitarily invariant norm of the doubled sine is a symmetric function of the values sine twice theta one, sine twice theta two, and so on. Replacing any individual theta by ninety degrees minus theta preserves the corresponding value.

Consequently, even knowing the complete singular-value list of sine twice the angle operator need not recover the original angle list. The loss occurs before a norm is applied. An operator norm loses the individual coordinates again by taking their maximum. A Frobenius norm sums their squares. Neither operation restores a branch choice that the scalar sine already discarded.

Take a direct sum of two independent planes. In the first plane rotate a line by five degrees; in the second rotate a line by eighty-five degrees. Both contribute the same doubled sine. The aggregate norm can be small even though one principal angle is close to ninety degrees.

This example also warns us not to replace a statement about a directed angle operator by an ambient one without checking dimensions. The directed list can omit defect directions that the ambient projection difference sees as a right angle.

## What a small bound does prove

Although it does not prove closeness alone, the inequality is useful. It establishes a forbidden interval of intermediate angles. If the doubled sine is below eta, every angle stays outside the band between gamma and ninety degrees minus gamma.

That is a meaningful dichotomy. For instance, if eta is one tenth, gamma is just under three degrees. Every angle is then near zero or near ninety degrees. What remains is to show that the actual subspaces follow the near-zero option.

One additional bit of information can suffice: every angle is strictly less than forty-five degrees. On that branch, the doubled sine is increasing. The same estimate then implies theta at most gamma. Conversely, if all angles are above forty-five degrees, it controls their distance from ninety degrees, which is a different geometric assertion.

The operator tangent-two-theta theorem under the ordered-gap off-diagonal assumptions proves the relevant branch under strong off-diagonal and ordered-gap hypotheses. It does not obtain the branch by merely inverting a doubled sine inequality.

## Can we use the perturbation continuously?

Often the operator is varied along a path, from T at time zero to T plus H at time one. At time zero the intended spectral projection equals the reference projection, so all principal angles are zero.

If the selected spectral projection varies continuously and a uniform double-angle estimate keeps its angles away from forty-five degrees, the angles cannot jump from the near-zero component to the near-ninety component. Any continuous path of angles between those regions would have to pass through forty-five degrees, where the doubled sine equals one.

This gives a branch-selection proof: establish a continuous family of *the same spectral cluster*, establish a barrier excluding the midpoint, and use the initial condition to stay on the desired side. Continuity alone is insufficient if the spectral cluster can collide with another cluster and lose its identity. And a bound only at the final time is insufficient if no intermediate barrier has been proved.

The mathematical responsibilities are separate. The gap protects the spectral labeling; the continuation argument transports the projection; and the angle barrier stops branch switching.

## Spectral labels instead of paths

There is another route. If the perturbed operator has a spectral gap, define V as its spectral subspace below a specified threshold. That construction removes the freedom to pick the high subspace as V. Spectral repulsion may then show that the threshold stays in the resolvent set, making the selected subspace canonical.

For a self-adjoint operator this means taking the range of a spectral indicator, not choosing an arbitrary reducing subspace. In finite dimensions, select every eigenvector whose eigenvalue lies below the threshold, with its entire eigenspace when multiplicities occur. This avoids basis dependence.

Even after spectral selection, an angle bound still requires work. Spectral labeling tells us which subspace to measure, whereas a perturbation theorem tells us how far it moves. Theorem eight point one will provide a particularly strong combination of labeling, repulsion, and an acute-angle conclusion under off-diagonal perturbations.

## A two-by-two diagnostic

Take T diagonal with entries negative one and one, and perturb it by a symmetric off-diagonal coupling h. The low spectral branch of the perturbed matrix rotates from the horizontal axis through an angle theta satisfying tangent of twice theta equals the absolute value of h.

At every finite h this selected angle lies below forty-five degrees. As h grows, it approaches forty-five from below. The other perturbed eigenspace remains perpendicular to the selected low eigenspace; measured against the original low axis, its angle is ninety degrees minus theta.

Both these choices have the same sine of twice their angle. The spectral label distinguishes them: one belongs to the low eigenvalue and the other to the high eigenvalue. The angle estimate can then be interpreted correctly.

For h equal to one, the two angles are twenty-two point five and sixty-seven point five degrees. Their doubled sines are equal to the square root of two divided by two. An estimate expressed only through that number cannot decide which eigenvector we selected.

## Why the issue persists in infinite dimensions

In Hilbert space, a right-angle component may arise from a crossed defect: vectors lying in one subspace and perpendicular to the other. Even if a directed overlap map behaves well, the opposite directed map can still detect an unmatched defect unless additional dimension or defect-matching conditions are imposed.

This is why the formal source distinguishes directed quarter-angle estimates, the full source angle operator, equal-rank hypotheses in finite dimensions, and equivalence of crossed defects in general Hilbert spaces. Treating all of these as interchangeable would produce incorrect conclusions.

## The conclusion

A bound on sine twice theta creates two allowed branches. It does not choose between them. To obtain a perturbation error certificate for a specific spectral subspace, we must supply spectral identification, continuity with a no-crossing guarantee, or a structural theorem proving acuteness.


<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For `0 ≤ θ ≤ π/2` and `0 ≤ η < 1`,

\[\sin(2\theta)\le\eta\iff \theta\in[0,\tfrac12\arcsin\eta]\cup[\tfrac\pi2-\tfrac12\arcsin\eta,\tfrac\pi2].\]

The example `T=diag(-1,1)`, `S=T`, `U=span(e₁)`, `V=span(e₂)` demonstrates why a reducing-subspace hypothesis without spectral selection cannot make a doubled-sine estimate into a small-angle estimate. Theorem 8.2's source-full-angle reading additionally relies on the original paper's standing subspace conventions; its dimension-free directed conclusion and its symmetric conclusion have different hypotheses.

### Exact Lean declaration excerpts

`DavisKahan/Sources/DavisKahan1970/Section8/Theorem81.lean` — `maximalAngle_lt_pi_div_four_iff` (exact declaration header; proof body omitted):

```lean
theorem maximalAngle_lt_pi_div_four_iff {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    maximalAngle U V < Real.pi / 4 ↔ IsQuarterAcute U V := by
```

`DavisKahan/Sources/DavisKahan1970/Section8/Theorem82.lean` — `subspaceGap_eq_directedGap_of_crossedDefects` (exact declaration header; proof body omitted):

```lean
theorem subspaceGap_eq_directedGap_of_crossedDefects {𝕜 : Type*} [RCLike 𝕜]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (P Q : Submodule 𝕜 G) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (h : CrossedDefectsEquivalent P Q) :
    P.projectionGap Q = P.directedProjectionGap Q :=
```

**Mapping.** The first declaration relates the strict quarter-turn angle to a projection gap smaller than `√2/2`; the second identifies directed and ambient gaps only after the crossed-defect matching premise is supplied. Neither declaration converts a doubled sine inequality into a branch selection on its own.

