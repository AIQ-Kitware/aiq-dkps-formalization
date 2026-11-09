# 121000 — A comparative theorem decision procedure

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `106000–120000` perturbation and angle theorems. **Next:** `122000` direct-sum norm comparison.

<!-- BEGIN SPOKEN LECTURE -->

# A comparative theorem decision procedure

Four classical spectral-subspace estimates involve the sine of an angle, the tangent of an angle, the sine of twice an angle, and the tangent of twice an angle. Their formulas look similar, but they answer different questions about trial residuals, changes of self-adjoint operators, and selected spectral subspaces. Using one theorem with another theorem’s hypotheses can invalidate a proof. The assumptions are different enough that such a substitution can invalidate a proof.

Selecting an angle theorem begins with the available spectral information and the norm to be controlled. We will apply it to three spectral-gap regimes, identify the object whose norm appears on the right side, and use examples to distinguish directed and ambient angles.

## Start with the question, not the bound

Ask what is being compared. Do we have a trial subspace and a true spectral subspace? Are we comparing spectral subspaces of two different self-adjoint operators? Or do we have a graph represented by a small slope over a reference subspace?

These questions fix the geometry. A trial subspace typically produces a residual, the component of the operator action escaping the trial subspace. A comparison of two spectral operators more naturally produces a full perturbation difference. A graph calculation produces tangent angles because the graph slope equals the tangent of the principal angle.

Next identify the angle itself. If the dimensions differ, a map from one subspace into the perpendicular of the other is directed. Its singular values need not coincide with those in the opposite direction. The ambient projector difference records all the directions represented by both subspaces and their complements.

Finally identify the norm. An operator-norm theorem is not automatically a theorem for every symmetric ideal. A Frobenius norm can support an estimate under pairwise spectral separation that fails with the same constant for operator norm.

## Regime one: ordered separation

Suppose the unwanted spectrum lies entirely above the trial compression, or entirely below it, with gap delta. This ordered-gap hypothesis is strong enough to apply the Sylvester inverse with a constant-one estimate for the operator norm and appropriate unitarily invariant norms.

If the trial map is isometric and R is its residual, the sine theorem gives delta times a directed sine norm at most the residual norm, subject to the stated operator-ideal assumptions. When the trial frame is not isometric, its lower frame bound introduces an additional normalization factor.

If the graph coordinate is well-defined and we have the stronger Ritz or invariant-subspace structure, a tangent theorem may give a stronger angular quantity under its own hypotheses. Since tangent theta is at least sine theta on the interval below ninety degrees, a tangent bound conveys more information for the same constant, but it is not free.

For a one-dimensional trial space and an exact unwanted eigenvalue, both cases reduce to familiar scalar equations. The sine estimate measures the perpendicular component of a normalized trial vector; the tangent estimate additionally divides by its aligned component. If the aligned component tends to zero, the tangent blows up, correctly warning that the graph parametrization is failing.

## Regime two: spectra separated but interlaced

Now suppose two spectral sets are disjoint but neither sits entirely above the other. They may be interlaced. We still have a positive minimum pairwise distance delta in finite dimensions, and the Sylvester equation still has a unique solution.

The entrywise spectral calculation immediately gives a Frobenius estimate: squared coefficient magnitudes are divided by spectral differences of magnitude at least delta. Summing squares proves delta times the Frobenius norm of the solution is at most the Frobenius norm of the right side.

However, the same argument does not yield the constant-one operator-norm inequality. Operator norm is not obtained by summing the squares of matrix entries; the spectral multiplier need not be a contraction in that norm.

The general disjoint-spectrum theory may give operator-norm bounds with a larger constant or under additional geometric assumptions. Before claiming a constant-one estimate, ask whether the gap is ordered or merely pairwise.

This distinction applies before any angle theorem is invoked. Choosing the wrong Sylvester bound corrupts every subsequent subspace estimate.

## Regime three: two-block gap and a full perturbation

Let T have a reducing decomposition into a low and high block separated by an ordered gap. Let S equal T plus H, with V any reducing subspace of S.

In this setting a sine-two-theta theorem bounds the ambient doubled sine by twice the perturbation norm divided by the original gap, under its precise norm hypotheses. The bound is robust to the choice of V because the function sine twice theta treats near-zero and near-right-angle choices alike.

Therefore, if the goal is an actual small angle, we must add branch information. We might know V is selected by a spectral projection and the perturbation is small enough to keep its branch connected to the original one. Or we might have off-diagonality, allowing a stronger tangent-two-theta theorem that itself proves a strict quarter-angle bound.

The sine-two-theta theorem accommodates a general self-adjoint perturbation. The tangent-two-theta theorem discussed earlier uses a stronger off-diagonal setting and matched spectral placement; its sharp operator-norm estimate should not be applied to an arbitrary H.

## A numerical comparison

Take T diagonal with entries negative one and one. Let H have zero diagonal and off-diagonal entries h. Set delta equal two. The selected low eigenspace of S has an angle theta satisfying tangent twice theta equal to h in magnitude.

For h equal to one, theta is twenty-two point five degrees. Sine theta is approximately zero point three eight three, tangent theta approximately zero point four one four, sine twice theta about zero point seven zero seven, and tangent twice theta equals one.

All four quantities measure different aspects of the same rotation. An estimate controlling sine theta by residual requires the chosen trial and exact spectral complement. An estimate controlling tangent theta uses graph or Ritz structure. The doubled sine follows from reflecting the operator. The doubled tangent uses off-diagonal repulsion and the small branch.

It would be a mistake to compare their numerical right sides alone while ignoring their different inputs.

## Diagnose a tempting false inference

Imagine that an argument establishes sine twice theta at most one tenth. Someone immediately writes theta at most half arcsine one tenth. We can test the inference with theta equal to eighty-eight degrees: sine of one hundred seventy-six degrees is about seven hundredths, so the bound is compatible with a nearly perpendicular subspace.

The inference becomes valid if we independently know theta below forty-five degrees. More generally, a selected spectral continuation can serve as the branch certificate when its hypotheses have been checked.

The problem is not an inaccurate numerical constant. It is the failure to identify the relevant inverse branch.

## Norm-class audit

Suppose our final statement uses a Schatten norm. Does the theorem give an estimate in that norm? Check whether its source is stated for the operator norm only, a particular Hilbert–Schmidt norm, finite-dimensional unitarily invariant norms, or an infinite-dimensional symmetric ideal with membership hypotheses.

A finite Ky Fan inequality is often a flexible intermediate object. If every Ky Fan prefix of the left-side singular values is bounded by the corresponding right-side prefix, then weak majorization allows descent to symmetric norming functions. The passage may also need proof that the target belongs to the ideal whenever the right-hand side does.

For a bound on a direct sum of two cross-blocks, one must compare their complete singular-value lists, not simply add the two operator norms and declare an ideal estimate.

## Direction and dimension audit

A directed sine map from P into Q perpendicular can be small even if Q contains a large extra perpendicular part not represented in P. In finite dimensions, if P and Q have equal rank, the two lists of nonzero principal sines coincide. Without that rank equality, a bound for one direction does not automatically control the ambient projection difference.

In infinite dimensions, equality of Hilbert-space dimensions is weaker than matching the crossed defects. A theorem about the full angle uses its stipulated subspace-matching assumptions; a directed-angle estimate controls only the specified direction.

## A practical decision pass

For every new problem, record the operator pair and their domains, the trial or selected subspace, the exact spectral sets, the gap type, the residual or perturbation, the angle orientation, and the norm class.

Then ask the sequence of proof questions. Is the Sylvester equation even well-defined on the required domain? Is its inverse bound valid for this gap and norm? Does the operator projection represent the stated sine or tangent? Are both directed components controlled? If a doubled angle appears, what chooses its branch?

Each condition excludes a concrete failure mode: a wrong spectral gap, an unmatched defect space, an invalid norm comparison, or an ambiguous angular branch.

## Close the comparison

The single-angle theorems use a residual and a separated unwanted spectrum. The doubled-angle theorems use reflection of a two-block spectral decomposition and a full perturbation. The tangent versions rely on additional graph or spectral-branch information. The available norm bound depends on the gap geometry and on whether all needed singular-value comparisons have been proved.

For a full ambient sine estimate, two crossed residual equations may be needed rather than one. Their singular-value lists can be combined using the Ky Fan direct-sum inequality, while pinching controls the corresponding perturbation blocks by one ambient norm. These steps explain why keeping track of direction, spectral gaps, and norm class is indispensable.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Selection checklist: `(1)` order-gap versus pairwise gap; `(2)` `R=AE-EA₀` versus `H=S-T`; `(3)` directed sine, graph tangent, or ambient doubled angle; `(4)` source and target dimensions/crossed defects; `(5)` operator norm, finite Ky Fan, symmetric gauge or infinite-dimensional ideal; `(6)` branch selection and any nontrivial domain conditions.

The two-level model `T=diag(-1,1)`, `H=[[0,h],[h,0]]` gives `tan(2θ)=|h|` for the selected low branch. The same doubled-sine value is attained by the complementary eigenspace, showing that the explicit branch must be retained.

### Exact Lean declaration excerpts

`DavisKahan/FiniteDimensional/DoubleAngle/SinTheta.lean` — `sinTwoTheta_perturbation_le` (exact declaration header; proof body omitted):

```lean
theorem sinTwoTheta_perturbation_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A)) (hV : (V ∈
        Module.End.invtSubmodule B))
    {a b : ℝ} (_hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * N ((U.sinTwoAngleOperator V).toLinearMap) ≤ 2 * N (B - A) := by
```

`DavisKahan/FiniteDimensional/DoubleAngle/TanTheta.lean` — `tan_two_theta_norm_sub_le` (exact declaration header; proof body omitted):

```lean
theorem tan_two_theta_norm_sub_le (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b ε : ℝ} (hab : a < b) (hε0 : 0 ≤ ε)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hVb : ∀ x ∈ V, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪S x, x⟫_𝕜)
    (hVa : ∀ x ∈ Vᗮ, RCLike.re ⟪S x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hHU : ∀ x ∈ U, ∀ y ∈ U, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hHUperp : ∀ x ∈ Uᗮ, ∀ y ∈ Uᗮ, ⟪x, (S - T) y⟫_𝕜 = 0)
    (hε : ∀ x, ‖(S - T) x‖ ≤ ε * ‖x‖) :
    ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2 < 1 / 2 ∧
      (b - a) * (2 * ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖
          * Real.sqrt (1 - ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2))
        ≤ 2 * ε * (1 - 2 * ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ ^ 2) := by
```

**Mapping.** `sinTwoTheta_perturbation_le` is a finite-dimensional, full-perturbation double-angle statement using a unitarily invariant seminorm. `tan_two_theta_norm_sub_le` is an operator-norm theorem with self-adjointness, both reducing subspace placements, off-diagonal perturbation blocks, and a norm bound. The second proves a strict quarter-angle condition before delivering the tangent inequality. They are not interchangeable with the residual-based single-angle theorems.

