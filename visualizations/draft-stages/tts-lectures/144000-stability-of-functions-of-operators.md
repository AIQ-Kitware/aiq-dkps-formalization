# 144000 — Stability of functions of operators

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `030000–033000`, `075000–081000`, `116000–120000`. **Next:** `145000`.

<!-- BEGIN SPOKEN LECTURE -->

# Stability of functions of operators

Many applications apply a function to an operator rather than asking for a particular eigenvector. They may take an operator square root, solve a resolvent equation, evolve a system by an exponential, or select a spectral cluster through a step function. Davis and Kahan ask which such operations admit useful perturbation bounds, and under what assumptions on the function and the operators.

## What a function of an operator means

For a self-adjoint finite matrix A, write its spectral decomposition as a sum of eigenvalues times orthogonal spectral projections. To define f of A, keep the projections and apply the scalar function f to the eigenvalues. If A has eigenvalue lambda on a subspace, f of A acts there by multiplication by f of lambda.

The definition is independent of which orthonormal basis we pick inside a repeated eigenspace. In infinite dimensions, bounded Borel functional calculus replaces the finite sum with a spectral integral. For a bounded self-adjoint operator, the Borel functional calculus integrates the chosen bounded measurable function against the projection-valued spectral measure. It therefore extends the finite eigenvalue formula without requiring an eigenvector basis.

Now perturb A to B, where B equals A plus H. We want to estimate the operator norm of f of B minus f of A, or perhaps a unitarily invariant norm. A naive guess would be: if f is Lipschitz as a scalar function, with constant L, then the operator difference should be at most L times the norm of H.

That guess is valid in several special cases, but not for every scalar Lipschitz function acting on arbitrary self-adjoint operators. The eigenvectors of A and B can be different, and scalar pointwise inequalities do not automatically control the resulting noncommuting matrix expressions.

Let us begin with classes where a proof is straightforward.

## Polynomials and the telescoping identity

For the function f of x equals x squared, compare B squared and A squared. Expand B as A plus H. The difference is A H plus H A plus H squared. Equivalently it is B H plus H A. These two expressions are exactly equal, whether or not A and H commute.

Using submultiplicativity, the difference norm is at most the sum of the norms of B and A times the norm of H. Thus if both operators have norm at most M, the square-function difference is at most two M times the perturbation norm.

For an integer power n, the difference B to the n minus A to the n is a sum of n terms, each with some powers of B to the left, exactly one H in the middle, and powers of A to the right. Multiplying out makes adjacent terms telescope. If both A and B have norms at most M, the result is bounded by n times M to the n minus one times the norm of H.

Every polynomial is a linear combination of these powers. We therefore get an explicit bound for every polynomial on a bounded operator ball. Polynomial approximation helps construct continuous functional calculus, but a uniform approximation of a scalar function does not by itself produce a uniform Lipschitz constant for its operator map. The constants in approximating polynomials might diverge.

## Resolvents are stable away from spectrum

Consider the resolvent function, the reciprocal of x minus z, where z is a complex number outside the spectra of A and B. Its operator value is the inverse of A minus z times the identity.

There is an exact resolvent identity. The resolvent of B minus the resolvent of A equals minus the resolvent of B, followed by H, followed by the resolvent of A. This is just the inverse-difference formula, and it requires no commutation.

Take norms. The resolvent difference is bounded by the product of the two resolvent norms times the perturbation norm. If A and B are self-adjoint and z stays at least distance d from both spectra, each resolvent norm is at most one over d. Hence the difference norm is at most the perturbation norm divided by d squared.

Notice what the denominator says. A resolvent can be sensitive when z approaches the spectrum. The distance to spectrum is part of the theorem, not an optional decoration.

In infinite dimensions the same identity works for closed self-adjoint operators if H is bounded and both resolvents exist. We must keep domain issues in mind when deriving the formula, but the final resolvents are bounded everywhere-defined operators.

## A step function becomes a spectral projection

Now consider a function that equals one below a specified spectral cut and zero above it. Suppose the spectra of both A and B avoid a neighborhood of that cut. Then the function of A is the spectral projection P onto eigenvalues below the cut. The function of B is the analogous projection Q.

Therefore the operator difference of the two functions is exactly Q minus P. Its operator norm measures the ambient sine of the maximal principal angle between the selected subspaces. The directed difference, applied to the original selected frame, measures the directed sine.

This is the concrete example inside Davis and Kahan's Question ten point four. The associated sine-theta and tangent-two-theta theorems become functional-calculus perturbation bounds for that step function.

Both the gap and the spectral selection defining Q are essential. A reducing projection need not be the projection selected by a given spectral cut; the functional-calculus identity uses the specified cut, not an arbitrary reducing subspace.

There is also a simple discontinuity example. Let A be a scalar matrix with a single eigenvalue exactly at the cut. Move that eigenvalue slightly from one side of the cut to the other. The operator norm of the perturbation can be arbitrarily small, while the step-function projection changes by the identity on that eigenspace. No uniform Lipschitz estimate can hold there without a gap.

## A worked rotation example

Take A to be the diagonal matrix with entries minus one and plus one. Rotate its eigenbasis by an angle theta to produce B. The eigenvalues of B have not changed at all. Yet the negative-eigenvalue projection has rotated. The norm of the difference of those projections is the absolute value of sine theta.

What about the perturbation? A direct two-by-two calculation gives the norm of B minus A equal to two times the absolute value of sine theta. In this example the step-projection change is exactly half the perturbation norm.

The ratio is not universal. It reflects the gap of two between the eigenvalues. If we shrink that gap, the same rotation can be produced by a smaller perturbation. A spectral-gap denominator is therefore expected in general.

The example also proves why comparing only eigenvalues cannot estimate the difference between functions of operators. The two operators have identical spectra, but their spectral projections are not identical.

## Why divided differences appear

For commuting diagonal matrices, the change in f acts coordinatewise. Each coordinate has scalar quotient: f of mu minus f of lambda, divided by mu minus lambda, when the denominator is nonzero. For noncommuting matrices, the same quotient appears between different eigenvectors.

One can write a matrix-level formula using the spectral projections of A and B. The contribution between an A eigenvalue lambda and a B eigenvalue mu is the scalar divided difference multiplied by the corresponding cross projection and by H. This follows from the identity that the cross projection of H equals the spectral difference times the cross projection of the identity.

A bound on each scalar quotient is necessary, but an operator-norm estimate of the resulting sum can be harder. It is a Schur-multiplier problem, closely related to the norm dependence we studied for Sylvester inverses. In Hilbert–Schmidt norm, orthogonality of the matrix entries often makes estimates easier. In operator norm, coherent interactions among entries can change the best constant.

This explains, at a structural level, why scalar Lipschitz continuity is not the complete answer to Question ten point four. Additional regularity of f, spectral assumptions, or a different norm can be required.

## Reading the question precisely

The original Davis-Kahan paper asks for useful classes of real functions f and estimates comparing f of A with f of a perturbed operator. The projection-valued step function provides one model: its projection identities are rigorous, while a broad perturbation theory for arbitrary function classes is a separate question.

The polynomial telescoping identity, the resolvent identity, and the identification of spectral projections as step functions give three concrete comparison tools. Their hypotheses differ, and the moving spectral-cut example shows why scalar Lipschitz regularity alone cannot control every operator function.

<!-- END SPOKEN LECTURE -->

---

## Display-only mathematical and Lean correspondence

`DK-10.4` is transcribed in `prose/distilled_literature/DavisKahan1970_part_III.tex`; the step-function specialization is developed in `DavisKahan/Sources/DavisKahan1970/Section10FunctionalCalculus.lean`. It explicitly requires the perturbed reducing projection to be the spectral projection at the same cut.

For `B=A+H`, the polynomial and resolvent identities used in the lecture are

\[B^n-A^n=\sum_{k=0}^{n-1}B^{n-1-k}HA^k,\]
\[(B-zI)^{-1}-(A-zI)^{-1}=-(B-zI)^{-1}H(A-zI)^{-1}.\]

The source formalizes the spectral step-function identities below; it does not claim a universal operator-Lipschitz inequality for arbitrary scalar-Lipschitz `f`.

## Exact Lean declaration excerpts

**`cfc_gapStep_eq_starProjection_complex`** — The self-adjoint operator and its reducing subspace must have compressed spectra on opposite sides of the positive gap. `hf1` and `hf0` make the Borel gap function constant on those spectral parts.

Source: `DavisKahan/Sources/DavisKahan1970/Section10FunctionalCalculus.lean`; exact declaration header (proof body omitted).

```lean
theorem cfc_gapStep_eq_starProjection_complex
    {A : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (hAU : ∀ x ∈ U, A x ∈ U)
    {α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Iic α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f A = U.starProjection := by
```

**`Question10_4_ambient_functionalChange_complex`** — The exact `f(A+H)-f(A)=Q-P` identity uses explicit block spectral hypotheses for BOTH operators. In particular, `Q` must be the projector selected by the same cut, not an arbitrary reducing projection.

Source: `DavisKahan/Sources/DavisKahan1970/Section10FunctionalCalculus.lean`; exact declaration header (proof body omitted).

```lean
theorem Question10_4_ambient_functionalChange_complex
    {A H : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    cfc f (A + H) - cfc f A = projectorDifference U V := by
```

**`Question10_4_directed_functionalChange_complex`** — The directed operator equality restricts functional-calculus change to the original trial subspace. It is stronger than a single norm inequality.

Source: `DavisKahan/Sources/DavisKahan1970/Section10FunctionalCalculus.lean`; exact declaration header (proof body omitted).

```lean
theorem Question10_4_directed_functionalChange_complex
    {A H : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U) (hAplusH_V : ∀ x ∈ V, (A + H) x ∈ V)
    {β α δ : ℝ} (hδ : 0 < δ)
    (hA0spec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc β α)
    (hA1spec : spectrum ℝ (compressOperator Uᗮ A) ⊆ Set.Ici (α + δ))
    (hL0spec : spectrum ℝ (compressOperator V (A + H)) ⊆ Set.Iic α)
    (hL1spec : spectrum ℝ (compressOperator Vᗮ (A + H)) ⊆ Set.Ici (α + δ))
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    {f : ℝ → ℝ} (hf1 : ∀ t ≤ α, f t = 1) (hf0 : ∀ t, α + δ ≤ t → f t = 0) :
    (cfc f (A + H) - cfc f A) ∘L U.subtypeL = -TauCeti.principalSineOperator U V := by
```

