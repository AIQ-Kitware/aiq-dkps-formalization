# 149000 — Proof practicum: reconstruct the 1970 theory

**Draft status:** audio-first final proof practicum. **Prerequisites:** `001000–148000`, particularly `049000–051000`, `064000–071000`, `083000–105000`, `108000–129000` and `130000–141000`. **Course endpoint.**

<!-- BEGIN SPOKEN LECTURE -->

# Proof practicum: reconstruct the 1970 theory

A rigorous Davis-Kahan perturbation argument begins with explicit self-adjointness, spectral-gap, residual, and norm hypotheses. The goal is to reconstruct the bound from those assumptions, then identify how the same mechanism adapts to Hilbert spaces, norm ideals, and the other angle theorems.

Treat each stage as a proof task. Work through the missing calculation before hearing the verification. The final result is not a list of theorem names. It is an argument in which each hypothesis has a specific job.

## Stage one: identify the correct geometric data

Let H be a finite-dimensional real or complex inner product space. Let A be self-adjoint, and let U be an A-invariant subspace. Because A is self-adjoint, U's orthogonal complement is invariant as well. Write P for orthogonal projection onto U, and Q for projection onto a trial subspace V of dimension d.

Choose an orthonormal coordinate embedding E from d-dimensional coordinate space into H, with range V. Choose an orthonormal embedding F into the exact orthogonal complement of U. The columns of F need to span that complement. We can then write F times F adjoint for the projection onto U perpendicular.

Your first task is to express the directed sine-angle operator using E and F. The answer is to form X equal to F adjoint E. Compute its Gram operator: X adjoint X equals E adjoint times the projection onto U perpendicular, times E. The eigenvalues of this positive operator are the squared sines of the directed principal angles from V to U. Therefore the singular values of X are the principal sines.

This identity is the geometric bridge. A bound on X in an operator or unitarily invariant norm is a bound on the trial space's angular leakage. Notice that if V and U have unequal dimensions, the directed sine list can contain additional right-angle directions. One must then say which direction of comparison is intended.

## Stage two: derive the residual equation

Form the Rayleigh–Ritz compression A zero, equal to E adjoint A E. Define the residual R to be A E minus E A zero. Since E adjoint R equals zero, R is orthogonal to the trial space. That is Galerkin orthogonality. It does not mean R is orthogonal to the exact subspace.

Define Lambda one as F adjoint A F, the restriction of A to U perpendicular expressed in orthonormal coordinates. Calculate F adjoint R. First, F adjoint R equals F adjoint A E minus F adjoint E A zero.

Because U perpendicular reduces A, the first term equals Lambda one times F adjoint E. Put X in both places. You obtain the complementary Sylvester equation: Lambda one X minus X A zero equals F adjoint R.

This calculation is short, but it carries much of the theorem. We have converted the unknown geometric overlap X into the solution of a linear operator equation. The forcing term is a compression of the residual. The spectral gap will determine whether that equation has a controlled inverse.

## Stage three: choose and prove the gap estimate

Suppose the spectrum of A zero is entirely below a real number a, while the spectrum of Lambda one is at least delta above a. Here delta is strictly positive. This is an ordered spectral separation hypothesis, stronger than merely requiring every cross-pair of eigenvalues to have distance at least delta.

Can you derive a bound on X? For bounded self-adjoint matrices, write the Sylvester inverse as an integral. If Lambda one lies above and A zero below, then X equals the integral from zero to infinity of the exponential of negative t Lambda one, times F adjoint R, times the exponential of t A zero. To make decay explicit, insert the same scalar center a with opposite signs in the two exponentials. The product bound then decays at least as the exponential of negative delta t.

Integrating gives the operator-norm inequality: delta times the norm of X is at most the norm of F adjoint R. Since F adjoint is a contraction, the latter is at most the norm of R. And because the singular values of X are the directed principal sines, we have proved the single-angle sine theorem for this ordered-gap finite-dimensional setting.

If instead we assume only that every eigenvalue of Lambda one is separated from every eigenvalue of A zero by delta, diagonalize the blocks and solve the Sylvester equation entry by entry. Each entry of X is the corresponding entry of F adjoint R divided by an eigenvalue difference. Squaring and summing gives the same constant-one estimate in Frobenius norm.

Do not assert that this entrywise argument proves the constant-one operator-norm estimate. It does not. The distinction between ordered and pairwise gaps, and between operator and Frobenius norms, is part of the theorem's mathematical content.

## Stage four: test a sharp two-dimensional case

Take A diagonal with entries zero and delta. Let the exact subspace U be the first coordinate axis. Take the trial unit vector E to have coordinates cosine theta and sine theta, for an angle strictly between zero and ninety degrees.

The compressed Rayleigh quotient A zero is delta times sine squared theta. The exact complementary block Lambda one is delta. The difference between their spectral values is delta times cosine squared theta. The complementary overlap X equals sine theta.

Calculate the residual's component along the second coordinate. It is delta times sine theta times cosine squared theta. Therefore the Sylvester equation has equality: the compressed gap, which is delta cosine squared theta, times the sine theta overlap equals that residual component.

This example teaches two checks. First, never substitute the original eigenvalue gap delta for the actual gap between Lambda one and the Ritz value A zero without verifying the needed inequality. Second, the compressed residual is not automatically the whole residual. In this example the full residual also has a component in the original exact subspace.

The standard two-level example, with every admissibility hypothesis checked, attains equality for the sharp sine, tangent, and doubled-angle estimates. Equality under the actual hypotheses proves that their coefficient one cannot be reduced; a numerical coincidence without those checks does not.

## Stage five: pass from a single angle to norm generality

Suppose a theorem claims a bound in every unitarily invariant norm, wherever that norm is defined. What must we prove beyond the operator-norm case?

We need control of the entire singular-value sequence, not just its largest member. In finite dimensions, the useful language is Ky Fan sums: for each positive integer k, sum the largest k singular values. An all-prefix comparison yields weak majorization. Under the hypotheses of the symmetric-gauge theorem, weak majorization gives the desired unitarily invariant norm inequality.

For the ambient sine theorem of Section six, there is another issue. One directed residual equation only controls one crossed block. To control the full ambient sine operator, derive both crossed Sylvester equations. Compare their block singular values, combine the estimates using the direct-sum Ky Fan lemma, and use the reflection-averaging pinching lemma to contract the relevant perturbation blocks.

In infinite dimensions, an arbitrary ideal norm may be infinite on a bounded operator. Thus an honest theorem first establishes ideal membership, or assumes it for the perturbation and proves it for the angle operator, before comparing numerical ideal gauges. The phrase wherever defined is a mathematical condition, not a stylistic qualification.

## Stage six: reconstruct the other three angle families

Now explain how the proof changes for tangent theta. Represent the trial subspace as a graph over the exact subspace, provided the projection from the trial space to the exact space is invertible with bounded inverse. The graph map is the sine overlap divided by the cosine overlap. Its singular values are the tangents of the principal angles. An ordered Ritz gap and the appropriate residual equation then control the graph map. The invertibility assumption or a theorem deriving it cannot be omitted.

For sine of two theta, introduce the block reflection associated with one subspace. Reflecting the other subspace across it doubles the principal-plane angles, after the appropriate angular functional calculus. Off-diagonal perturbations anticommute with the reference reflection. This produces a doubled-angle residual with a factor of two. The sine-two-theta estimate may be valid without knowing that the original angle is small.

For tangent of two theta, small-angle branch information matters. Tangent of twice an angle changes sign or becomes singular at forty-five degrees. Under the required ordered-gap, off-diagonal, and spectral-selection conditions, the appropriate reducing subspace stays in the small-angle branch and one obtains the sharp tangent-two-theta inequality. Without that selection argument, a bound on sine of twice an angle could describe an angle near ninety degrees just as well as one near zero.

These are four theorem families, with different geometry and different gap requirements. A proof that establishes one does not automatically establish the others.

## Stage seven: restore the unbounded Hilbert-space machinery

In a Hilbert space, A may be self-adjoint and unbounded. Before writing A E, you must state that every trial vector lies in the domain of A. The exact reducing projection must preserve the domain, and the restricted operators have their own domains. For a Sylvester equation involving two unbounded blocks, the domain of X's input and the requirement that its image land in the other block's domain are essential.

Use bounded spectral cutoffs to make each intermediate calculation legal. Prove that cutoff vectors converge strongly, and that the operator images converge on vectors in the graph domain. Then pass through a closedness or resolvent argument to recover the original operator equation and norm estimate.

You will also need the spectral measure and Borel functional calculus to discuss reducing subspaces when the operator has continuous spectrum. In particular, a multiplication operator can have a substantial spectral projection even when it has no eigenvector for almost every individual spectral value. Finite eigenbasis calculations cannot be used as a substitute for that theory.

Finally, treat real and complex Hilbert spaces explicitly. The complex spectral calculus may be used after complexifying a real operator, but the operator norm, spectral restrictions, domains, and relevant ideal gauges must be transported back correctly. A theorem proved over complex scalars is not automatically a theorem over real scalars without that descent.

## Stage eight: close the original paper faithfully

The 1970 paper also develops direct rotation and an extremal claim about displacement. Reconstruct the polar intertwiner of two projections, state the crossed-defect matching criterion at right angles, and distinguish the canonical polar rotation from arbitrary unitary transports.

Then separate three objectives: displacement restricted to the source subspace, squared whole-space displacement, and unsquared whole-space displacement. The first two admit the valid optimality theorems studied in this course. The broad unsquared full-space claim of Proposition four point four is false; the explicit real four-dimensional example supplies the counterexample. Do not use the false proposition as a lemma.

The free-beam example is another endpoint test. To reproduce it, construct the fourth-order self-adjoint operator with its boundary conditions, compute the Ritz compression and residual matrices, verify the spectral separation, and apply the angle estimates. Its finite trial matrix does not erase the unbounded operator-domain obligations.

Finally, the original paper's Section ten asks questions that are broader than the results established in the main body. Report the proved cases, available counterexamples, and remaining hypotheses precisely. Do not turn an open question into a theorem by appealing to a plausible analogy.

## Your final proof certificate

A complete reconstruction should contain, in order: the ambient Hilbert-space and scalar-field assumptions; the domains of all operators; the exact and trial subspaces; the residual and compressed blocks; the correct spectral-gap predicate; the Sylvester inverse and its norm class; the Gram identity identifying the angle; and the ideal membership and cutoff arguments where needed.

You should be able to present the finite single-angle proof on a blank page, then explain which pieces must be replaced or strengthened for the ambient, doubled-angle, and infinite-dimensional theorems. You should also be able to point to the direct-rotation correction and the free-beam example without confusing them with the hypotheses of the sine theorem.

The resulting inequalities are meaningful only with their spectral and norm hypotheses. A complete reconstruction explains the residual equation, the gap estimate, the geometry of angles, and the exact scope of each norm and optimality claim.

<!-- END SPOKEN LECTURE -->

---

## Display-only proof certificate and Lean correspondence

### Finite directed sine derivation

Let \(A=A^*\) act on finite-dimensional \(H\). Let \(U\) be reducing for \(A\), \(E:\mathbb K^d\to H\) an isometry with trial range \(V\), and \(F:\mathbb K^m\to H\) an isometry onto \(U^\perp\). Define

\[
A_0=E^*AE,\quad R=AE-EA_0,\quad
\Lambda_1=F^*AF,\quad X=F^*E.
\]

Then

\[
E^*R=0,\qquad F^*R=\Lambda_1X-XA_0,\qquad
X^*X=E^*P_{U^\perp}E.
\]

The singular values of \(X\) are the *directed* principal sines from \(V\) to \(U\). If the spectra of \(\Lambda_1\) and \(A_0\) have a suitably ordered gap \(\delta>0\), the self-adjoint Sylvester inverse obeys

\[
\delta\|X\|\le\|F^*R\|\le\|R\|.
\]

For a merely pairwise cross-spectral gap, diagonal entry division gives \(\delta\|X\|_F\le\|F^*R\|_F\), not a general constant-one operator-norm conclusion.

### Two-dimensional consistency check

Take \(A=\mathrm{diag}(0,\delta)\), \(U=\mathrm{span}(e_1)\), and \(E=(\cos\theta,\sin\theta)^\top\), with \(0<\theta<\pi/2\). Then \(A_0=\delta\sin^2\theta\), \(\Lambda_1=\delta\), \(X=\sin\theta\), and \(F^*R=\delta\sin\theta\cos^2\theta\). The *actual* ordered separation between the two compressed scalars is \(\delta\cos^2\theta\).

### Infinite-dimensional obligations

Replace unrestricted matrix multiplication with explicit domain inclusions. Require reducing projections to preserve the closed operator's domain and use spectral cutoffs and strong/graph convergence as appropriate. For a unitarily invariant ideal, show membership of the angle operator and perturbation in the ideal before applying its gauge. In the ambient Section 6 theorem, require both crossed-gap conditions and use the all-prefix direct-sum lemma and reflection pinching.

### Practicum checkpoints

1. Derive \(F^*R=\Lambda_1X-XA_0\) without treating the Ritz frame as an exact invariant subspace.
2. State which gap controls operator norm and which controls Frobenius norm; construct a counterexample to an unjustified strengthening.
3. Identify the exact operator whose singular values are the directed principal sines.
4. Restore the second crossed block, Ky Fan comparison, pinching, and ideal membership for the ambient result.
5. State transversality for tangent bounds and spectral branch selection for double-angle bounds.
6. Explain where spectral cutoffs, graph domains, and real/complex transfer enter.
7. Distinguish the valid direct-rotation minima from the false printed Proposition 4.4, and verify the beam's boundary conditions before using its Ritz matrix.

## Exact Lean declaration excerpts

**`proposition6_1_printedGap_sourceExact_complex`** — `DavisKahan/Sources/DavisKahan1970/Section6SourceScope.lean` (exact declaration header; proof body omitted):

```lean
theorem proposition6_1_printedGap_sourceExact_complex
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A B : E →L[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule ℂ E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A) (hV : Submodule.IsReducing V B)
    {δ : ℝ} (hδ : 0 < δ)
    {β α β' α' : ℝ} (hβα : β ≤ α) (hβα' : β' ≤ α')
    (hgapUV : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap
      (DavisKahanExt.PartialMap.boundedReducingBlock A U hU)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl B V hV) β α δ)
    (hgapVU : DavisKahan.Sylvester.RealSpectrumIntervalExteriorGap
      (DavisKahanExt.PartialMap.boundedReducingBlock B V hV)
      (DavisKahanExt.PartialMap.boundedReducingBlockCompl A U hU) β' α' δ)
    (hMem : N.Mem (B - A)) :
    N.Mem (cfc Real.sin (DavisKahan.Angle.angleOperator U V)) ∧
      δ * N.gauge (cfc Real.sin (DavisKahan.Angle.angleOperator U V)) ≤ N.gauge (B - A) :=
```

**`lemma61_all_kyFan`** — `DavisKahan/Sources/DavisKahan1970/SineTheta/Lemma61.lean` (exact declaration header; proof body omitted):

```lean
theorem lemma61_all_kyFan
    (Ω Γ : Submodule 𝕜 E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[𝕜] E)
    (h₀ : ∀ k,
      ((projectionBlock Ω Γ K).kyFanGauge k : ℝ) ≤
        ((projectionBlock Ω Γ L).kyFanGauge k : ℝ))
    (h₁ : ∀ k,
      ((projectionBlock Ωᗮ Γᗮ Ktilde).kyFanGauge k : ℝ) ≤
        ((projectionBlock Ωᗮ Γᗮ Ltilde).kyFanGauge k : ℝ)) :
    ∀ k,
      ((projectionBlock Ω Γ K +
            projectionBlock Ωᗮ Γᗮ Ktilde).kyFanGauge k : ℝ) ≤
        ((projectionBlock Ω Γ L +
            projectionBlock Ωᗮ Γᗮ Ltilde).kyFanGauge k : ℝ) := by
```

**`lemma6_2_separable`** — `DavisKahan/Sources/DavisKahan1970/Section6SourceScope.lean` (exact declaration header; proof body omitted):

```lean
theorem lemma6_2_separable {𝕜 : Type} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (N : NormalizedUnitaryInvariantNorm.{0, v} 𝕜)
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {K : E →L[𝕜] E} (hK : N.Mem K) :
    N.Mem (diagonalPair U V K) ∧ N.gauge (diagonalPair U V K) ≤ N.gauge K :=
```

**`tanTheta_residual_le`** — `DavisKahan/FiniteDimensional/Residual/AngleEmbeddings.lean` (exact declaration header; proof body omitted):

```lean
theorem tanTheta_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A))
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (tanThetaEmbedding U X) ≤ N (residual A X M) :=
```

**`sinTwoTheta_residual_le`** — `DavisKahan/FiniteDimensional/DoubleAngle/SinTwoThetaResidual.lean` (exact declaration header; proof body omitted):

```lean
theorem sinTwoTheta_residual_le
    (N : UnitarilyInvariantSeminorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : (U ∈ Module.End.invtSubmodule A))
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hMspec : Module.End.PointSpectrumIn M ⊤ (Set.Icc a b))
    (hAspec : Module.End.PointSpectrumIn A Uᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
```

**`shortRotation_fullDisplacement_refuted`** — `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean` (exact declaration header; proof body omitted):

```lean
theorem shortRotation_fullDisplacement_refuted :
    ∃ (U V : Submodule ℝ (EuclideanSpace ℝ (Fin 4)))
      (hacute : Submodule.IsAcute U V)
      (W : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)),
      U.map W.toLinearMap = V ∧
      Submodule.principalAngles U V 0 ≤ Real.pi / 3 ∧
      (LinearMap.id - W.toLinearMap).kyFanSum 4 <
        (LinearMap.id - (directRotation U V hacute).toLinearMap).kyFanSum 4 :=
```

**`sinTheta_model_equality`** — `DavisKahan/FiniteDimensional/Sharpness.lean` (exact declaration header; proof body omitted):

```lean
theorem sinTheta_model_equality
    (N : UnitarilyInvariantSeminorm 𝕜 (Plane 𝕜) (Plane 𝕜))
    {a b θ : ℝ} (hab : a < b) (hθ0 : 0 ≤ θ) (hθ1 : θ < Real.pi / 2) :
    (b - a) * N ((Submodule.sinAngleOperator (modelSubspace (𝕜 := 𝕜)) (rotatedModelSubspace (𝕜 := 𝕜) θ)).toLinearMap) =
```

