# 135000 — Corrected scopes and surviving results

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `130000–134000`. **Next:** `136000`.

<!-- BEGIN SPOKEN LECTURE -->

# Corrected scopes and surviving results

We have completed a direct examination of Davis and Kahan's Section Four extremal claims. One of the printed universal conclusions fails, but several other optimization statements are correct and stronger than they may first appear. In this lecture we will reorganize the theory by the exact object being minimized, the norm being used, and the field over which the transport acts. The goal is a reliable set of conclusions that we can use without accidentally importing the false proposition.

## Four distinct quantities

Fix subspaces U and V, and consider orthogonal or unitary transporters W satisfying W U equals V. Let D denote a source-defined direct rotation, when one exists.

The first quantity is the restricted displacement: identity minus W, applied only to U. The second is the sum of squared sine-angle errors of an orthonormal basis of U. The third is the positive squared full displacement: identity minus W adjoint multiplied by identity minus W. The fourth is the unsquared full displacement identity minus W, measured by some unitarily invariant norm.

The first three have source-backed theorems with precisely stated hypotheses. The fourth is a separate optimization problem. Understanding the first three does not automatically solve it for every norm.

## Restricted displacement remains universally minimal

Proposition four point one proves that the restricted displacement of D has singular values no larger than those of any competitor, pointwise by index. Corollary four point one then says D minimizes every unitarily invariant norm of the restricted displacement.

This is a particularly strong theorem because it requires no arbitrary choice of norm in the proof. The principal-chord values, two sine of half the principal angles, serve as a common lower bound for all the singular values.

The source treats compact-angle sequences in an arbitrary Hilbert space and accounts for matched crossed defects when right-angle components occur. In that setting we need to use approximation numbers and keep the hypotheses that make the source's direct rotation well-defined.

If a competitor belongs to a relevant symmetric operator ideal, ideal membership of the direct displacement is a conclusion obtained through approximation-number domination. We must not write an infinite-dimensional finite-norm inequality without first establishing that membership.

## Orthonormal-frame angular energy remains bounded below

Proposition four point two concerns sine squared of the angle between each basis vector and its transported image. Every such error dominates the squared escape norm into V perpendicular. Summing over an orthonormal basis gives the sum of squared principal sines.

This result does not select a particular unsquared displacement norm, and it does not compare every vector's Euclidean displacement with its direct-rotation displacement. It is an energy inequality derived from the Gram operator of the projection escape map.

The infinite-dimensional theorem interprets the sum as an extended nonnegative value. This makes the statement meaningful even without a trace-class hypothesis.

## Squared ambient displacement remains universally minimal

Proposition four point three compares the positive displacement squares. The direct rotation minimizes all Ky Fan prefix sums of the squared displacement, and therefore every unitarily invariant norm of that positive operator.

The proof combines the restricted result on U and U perpendicular, squares the singular values, and uses pinching to control the full competitor. The critical conclusion is **prefix dominance**, not pointwise dominance of every individual squared singular value.

The result also gives optimality of the unsquared full displacement in the operator norm and in Hilbert–Schmidt norm. More generally, it gives optimality for Q-norms: those whose squares are invariant norms of the positive Gram operator. Every Schatten p norm with p at least two is in this class.

Importantly, none of these Q-norm conclusions needs a universal sixty-degree angle restriction. The norm class supplies the correct hypothesis.

## What fails and why angle restrictions do not fix it

The printed Proposition four point four claimed that, in real spaces with maximal principal angle at most sixty degrees, the direct rotation minimizes **every** invariant norm of unsquared ambient displacement. The four-dimensional witness from the preceding lecture refutes it in trace norm at forty-five degrees. A continuous equal-angle family refutes any proposed positive universal angle threshold.

The failure is compatible with every preceding theorem. Restricted displacement can be optimal while a competitor's action on the complement changes the total trace cost. Squared displacement can be Ky Fan minimal even if the unsquared trace sum is larger. The objective determines which inequalities are valid.

A modest correct replacement is therefore: the direct rotation minimizes all Q-norms of full displacement under its usual existence hypotheses. For arbitrary invariant norms, one can still use the projection-difference lower bound, but the direct rotation need not attain it.

## A quantitative comparison when the norm is arbitrary

There is also a useful approximation guarantee. The projection difference is a lower bound for every competitor's full displacement in any unitarily invariant norm.

For a direct rotation with maximal principal angle theta-max, the singular values of its full displacement are the principal chords, repeated on both directions of each principal plane. Those of the projection difference are the corresponding principal sines, also repeated. Their ratio on a nonzero principal angle theta is one divided by cosine theta over two.

Therefore the full displacement of the canonical D has invariant norm at most secant of theta-max over two times the norm of P minus Q. Combining this with the universal lower bound gives an approximation factor relative to **every** competing transporter.

For theta-max at most sixty degrees, cosine theta-max over two is at least square root of three over two. The approximation factor is at most two divided by square root of three, about one point one five five. It is not a claim of exact minimization. The source formalizes the factor, and exhibits sharpness at fixed angles.

This distinction is useful in applications: a canonical choice can have provably controlled cost without being an optimizer for a given norm.

## The complex field has additional flexibility

Complex unitaries have phase degrees of freedom absent from real orthogonal matrices. On a single complex principal plane with angle theta, a phase-corrected transporter can have displacement singular values two sine theta and zero, instead of two copies of two sine theta over two.

Its trace cost is two sine theta, exactly the trace norm of the difference of the two rank-one projections. As a result it attains the universal projection-difference lower bound.

For many principal planes, choose these phase-corrected transporters independently and take their orthogonal direct sum. The total trace cost is twice the sum of the principal sines, which equals the trace norm of the projection difference. The repository has a finite-dimensional complex theorem asserting existence of a global trace minimizer with this principal-angle cost.

This does not mean the **canonical direct rotation** is trace optimal in complex space. The phase-corrected map is generally a different transporter. The field changes the feasible family, so claims about real and complex optimizers must be kept separate.

## What the real low-dimensional analysis adds

For a real line, or a real hyperplane, the ambient transport problem has an exact conventional solution for every invariant norm. The determinant-positive component has the direct-plane rotation as a minimizer. The determinant-negative component has a Householder reflection as a minimizer. The global optimum is the smaller of the two costs, given by singular-value lists consisting of two principal chords or a single two.

Thus the sixty-degree all-gauge threshold really does hold for real lines and hyperplanes. Every proper nonzero equal-dimensional pair in real ambient dimension at most three is of one of those forms. A research note in the supplied repository gives a complete conventional proof of that dimension statement, but explicitly says it is not yet a compiled Lean generalization. We should retain that evidence distinction.

The project's source-verified four-dimensional example then shows why the first failing real ambient dimension is four at the level of the mathematical analysis. The formal counterexample itself is Lean-backed; the general dimension-minimality classification should not be presented as a separate compiled theorem unless that formalization is added.

## A disciplined theorem-selection checklist

When presented with a new two-subspace optimization problem, first identify whether the input is restricted to U or ranges over the whole ambient space. Next decide whether the objective measures an angular sine, a squared Gram displacement, or an unsquared chord. Then identify the norm: operator, Frobenius, a Q-norm, trace norm, or a general invariant gauge. Finally check real versus complex scalars, compactness and defect matching, and ideal membership in infinite dimension.

These checks identify the correct theorem. They also reveal when the question is a new optimization problem rather than an immediate consequence of a known extremal principle.

## Conclusion

The source's restricted and squared-displacement extremal theorems remain valid. The unsquared full-displacement statement of Proposition four point four is false as printed; the real four-dimensional counterexample proves it directly. Q-norm optimality, projection-distance lower bounds, quantitative approximation factors, and separate complex trace optimizers provide precise replacements.

In the next lecture we will return to the classification of direct rotations themselves, including right-angle defect matching and compact principal-angle data. With the optimization scopes now settled, we can distinguish the geometry of constructing a direct rotation from the separate problem of minimizing a chosen transport cost.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For \(WU=V\), the source-supported inequalities include:
\[
\begin{aligned}
s_k((I-D)|_U)&\le s_k((I-W)|_U),\\
\| (I-D)^*(I-D)\|_{\mathcal I}&\le\|(I-W)^*(I-W)\|_{\mathcal I},\\
\|I-D\|_{Q}&\le\|I-W\|_{Q},\\
\|P_U-P_V\|_N&\le\|I-W\|_N.
\end{aligned}
\]
The second inequality requires a suitable invariant norm/ideal and its membership assumptions; the third requires the Q-norm property. The first is restricted displacement, the final two concern full displacement.

For finite-dimensional complex spaces, a **phase-corrected** transporter attains \(\min_{WU=V}\|I-W\|_1=2\sum_j\sin\theta_j=\|P_U-P_V\|_1\), but need not be the canonical direct rotation. The conventional real line/hyperplane result appears in `REAL_TRANSPORT_MINIMIZATION_NOTES.md` and is explicitly **not** certified there as a compiled Lean theorem. The `ℝ⁴` counterexample and Q-norm repair are compiled source results.

## Exact Lean declaration excerpts

**`directRotation_fullDisplacement_qnorm`.** The Q-norm repair applies to **unsquared full** displacement; without `IsQNorm`, the implication from squared-displacement optimality is unjustified.

`DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean` — `directRotation_fullDisplacement_qnorm` (exact declaration header; proof body omitted):

```lean
theorem directRotation_fullDisplacement_qnorm
    (N : UnitarilyInvariantSeminorm 𝕜 E E) (hN : IsQNorm N)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : Submodule.IsAcute U V) (W : E ≃ₗᵢ[𝕜] E)
    (hmap : U.map W.toLinearMap = V) :
    N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (LinearMap.id - W.toLinearMap) :=
```

**`uiNorm_directRotation_le_two_div_sqrt_three_mul_displacement`.** This is an approximation-factor bound under a short-angle hypothesis, not a minimizer theorem.

`DavisKahan/FiniteDimensional/DirectRotation/SharpDisplacement.lean` — `uiNorm_directRotation_le_two_div_sqrt_three_mul_displacement` (exact declaration header; proof body omitted):

```lean
theorem uiNorm_directRotation_le_two_div_sqrt_three_mul_displacement
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : Submodule.IsAcute U V)
    (hgap : U.projectionGap V ≤ Real.sin (Real.pi / 3))
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      (2 / Real.sqrt 3) * N (LinearMap.id - W.toLinearMap) :=
```

**`exists_global_complex_trace_minimizer_with_principalAngles`.** Finite-dimensional **complex** spaces with equal-rank subspaces admit a phase-corrected trace-norm minimizer whose cost equals twice the sum of principal sines. It need not be the canonical direct rotation.

`DavisKahan/FiniteDimensional/DirectRotation/ComplexTracePrincipalAngles.lean` — `exists_global_complex_trace_minimizer_with_principalAngles` (exact declaration header; proof body omitted):

```lean
theorem exists_global_complex_trace_minimizer_with_principalAngles
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (hUV : finrank ℂ U = finrank ℂ V) :
    ∃ W : H ≃ₗᵢ[ℂ] H,
      U.map W.toLinearMap = V ∧
      (LinearMap.id - W.toLinearMap).kyFanSum (finrank ℂ H) =
        (U.starProjection.toLinearMap - V.starProjection.toLinearMap).kyFanSum (finrank ℂ H) ∧
      (LinearMap.id - W.toLinearMap).kyFanSum (finrank ℂ H) =
        2 * ∑ j : Fin (finrank ℂ U), Real.sin (Submodule.principalAngles U V (j : ℕ)) ∧
      ∀ Z : H ≃ₗᵢ[ℂ] H, U.map Z.toLinearMap = V →
        (LinearMap.id - W.toLinearMap).kyFanSum (finrank ℂ H) ≤
          (LinearMap.id - Z.toLinearMap).kyFanSum (finrank ℂ H) :=
```

**`proposition4_3_directRotation_sourceExact_complex`.** The source-facing squared-displacement theorem explicitly takes `IsSourceDirectRotation`, preserving the paper’s definition rather than weakening it to an arbitrary rotation predicate.

`DavisKahan/Sources/DavisKahan1970/Section4DirectRotationSource.lean` — `proposition4_3_directRotation_sourceExact_complex` (exact declaration header; proof body omitted):

```lean
theorem proposition4_3_directRotation_sourceExact_complex
    [TopologicalSpace.SeparableSpace H]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (D : H →L[ℂ] H) (hD : DavisKahan.IsSourceDirectRotation U V D)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * U.starProjection = V.starProjection * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star D) * (1 - D)) ∧
      N.gauge ((1 - star D) * (1 - D)) ≤ N.gauge ((1 - star W) * (1 - W)) :=
```

