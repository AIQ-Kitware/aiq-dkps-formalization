# 137000 — The free-beam operator and its domain

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `072000–094000`, `136000`. **Next:** `138000`.

<!-- BEGIN SPOKEN LECTURE -->

# The free-beam operator and its domain

A beam with free endpoints has vibration modes described by a fourth-order differential operator. Davis and Kahan use this model to illustrate perturbation bounds for low-frequency spectral subspaces. To make the estimates rigorous, we need the operator domain and its boundary conditions, not just a formal fourth derivative.

The word free refers to the boundary conditions. It does not mean that the operator acts on every square-integrable function, and it does not mean that its zero eigenspace is trivial. In fact, the free boundary conditions produce two independent zero modes, and that is exactly what makes the perturbation example interesting.

## Why a fourth derivative appears

Imagine a thin elastic beam occupying the interval from zero to one. In a simplified linear bending model, the energy associated with a displacement u is proportional to the integral of the square of its second derivative. The second derivative measures bending curvature in the small-deflection approximation. Oscillation modes are governed by the fourth derivative.

We choose the Hilbert space of real square-integrable functions on the unit interval. Its inner product is the integral of u times v. Define the formal differential expression A of u to be the fourth derivative of u.

But a formal expression is not yet an operator on a Hilbert space. Most square-integrable functions do not possess four ordinary derivatives. Even if a fourth weak derivative exists, we must specify boundary conditions to get the desired self-adjoint realization.

For a freely supported end, the bending moment and shear force vanish. In this normalized model those are the second and third derivatives. Therefore we require that the second and third derivatives vanish at both endpoints.

In total we have four scalar conditions: the second derivative at zero is zero, the third derivative at zero is zero, and the same two conditions hold at one. The operator's domain is the appropriate fourth-order Sobolev class satisfying those trace equations. One may also characterize the final operator as the self-adjoint closure of a suitable classical fourth-derivative realization.

Why insist on the domain? Consider a candidate displacement that is square-integrable but whose fourth derivative is not. Writing A of that displacement as if it were a vector in the same Hilbert space would invalidate the residual estimates we learned earlier. The domain will become part of the numerical argument, not a detail hidden behind notation.

## Green's identity explains symmetry

Take smooth functions u and v in the free-end domain. Start with the integral of the fourth derivative of u times v. Integrate by parts once. The boundary term involves the third derivative of u times v, and the integral now involves the third derivative of u times the first derivative of v, with a minus sign.

Integrate the remaining integral by parts again. The new boundary term involves the second derivative of u times the first derivative of v, and the interior integral becomes the integral of u double-prime times v double-prime.

At each endpoint, both boundary terms vanish because u's second and third derivatives vanish there. Therefore the inner product of A u with v equals the integral of u double-prime times v double-prime.

Interchange u and v. The same integral appears, so the operator is symmetric on the stated domain. Moreover, setting v equal to u gives the nonnegative quadratic form: inner product of A u with u equals the integral of the square of u double-prime.

Integration by parts gives the nonnegative beam energy form, the integral of the squared second derivative. This proves symmetry and nonnegativity on the specified domain, but not self-adjointness: equality with the adjoint also requires equality of domains. A rigorous realization uses a closed quadratic form or a proved graph-closure construction.

For an unbounded operator, specifying the domain is part of specifying the operator itself.

## Why there are exactly two zero modes

Suppose u belongs to the operator domain and A u equals zero. Then its bending energy is zero. The integral of the square of u double-prime vanishes, so u double-prime is zero almost everywhere.

Consequently u is affine: a constant plus a multiple of t. Both the second and third derivatives of every affine function vanish identically, so all affine functions satisfy the free boundary conditions and lie in the kernel.

Thus the kernel has dimension two. One direction translates the whole beam up or down without bending it. The other gives a uniform tilt, which also produces no curvature. There are two zero eigenvalues, counted with multiplicity, even though the beam is not physically locked in place.

This is the trial subspace Davis and Kahan will use: the two-dimensional affine plane inside the infinite-dimensional Hilbert space.

## Find the positive frequencies

Now look for a nonzero eigenvalue lambda. The eigenvalue equation says the fourth derivative of u equals lambda times u. Because A is nonnegative, any such lambda is positive. Write lambda as beta to the fourth power, with beta positive.

The general classical solution is a linear combination of cosine beta t, sine beta t, hyperbolic cosine beta t, and hyperbolic sine beta t. There are four coefficients because this is a fourth-order differential equation.

Apply the two free conditions at the left endpoint. They impose two linear relations among the coefficients. After those are used, only two free parameters remain. Apply the two free conditions at the right endpoint. That gives a homogeneous two-by-two system in those parameters.

A nonzero eigenfunction requires this system to have a nontrivial solution, so its determinant must vanish. The determinant simplifies to a constant multiple of one minus cosine beta times hyperbolic cosine beta. Thus the positive frequencies satisfy cosine beta times hyperbolic cosine beta equals one.

This characteristic equation is not an approximation. It follows from the differential equation and the four boundary conditions. The first positive root lies just above four point seven three, whose fourth power is already greater than five hundred. Hence every positive free-beam eigenvalue is greater than five hundred.

The zero eigenspace therefore sits across a substantial spectral gap from all the positive modes. We have two zero eigenvalues, followed by a third eigenvalue greater than five hundred, and then an increasing sequence of positive eigenvalues.

## Why the spectral picture is complete

We still need to know that no unexpected continuous spectrum lies between these eigenvalues. For a bounded interval, the relevant Sobolev embedding is compact. Roughly, a family of functions with uniformly controlled square-integrable displacement and bending derivatives cannot keep producing arbitrarily fine independent oscillations without a convergent subsequence in L two.

More formally, the graph or form-domain embedding underlying the free-beam realization is compact. A shifted inverse of the operator is then compact and self-adjoint. The compact spectral theorem gives an orthonormal eigenbasis and a discrete set of eigenvalues, with no finite accumulation of positive frequencies.

This is how the differential equation, the operator domain, and the abstract spectral theorem fit together. The characteristic equation identifies possible positive eigenvalues. Compactness and the realization theorem show these are all the nonzero spectral values.

## Turn on a bounded perturbation

Introduce a positive parameter epsilon, smaller than one hundred. Let H multiply a function by epsilon times t. This is a bounded self-adjoint operator on L two, because t lies between zero and one. Its operator norm is at most epsilon, and its quadratic form is nonnegative.

Our perturbed operator is A plus H on the same domain as A. Being a bounded self-adjoint perturbation, H does not require us to shrink the domain. The new eigenvalue problem reads: fourth derivative of u plus epsilon t times u equals lambda times u, under the same four free-end boundary conditions.

Since H is nonnegative, the third eigenvalue of the perturbed system cannot lie below the third eigenvalue of the original system. The high-frequency sector remains above five hundred. The two zero modes are pushed into a small low-frequency cluster, while the large gap protects that cluster's subspace from large rotation.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

On real \(L^2(0,1)\), the free realization acts by \(Au=u^{(4)}\) on a domain supporting traces \(u''(0)=u'''(0)=u''(1)=u'''(1)=0\). Smooth integration by parts yields
\[\langle Au,v\rangle=\int_0^1u''(t)v''(t)\,dt=\langle u,Av\rangle.\]
The genuine self-adjoint operator uses domain and graph closure, beyond the formal Green identity. Its zero eigenspace is \(\operatorname{span}\{1,t\}\); nonzero eigenvalues satisfy \(\lambda=\beta^4\), \(\cos\beta\cosh\beta=1\). The source proves the positive spectral values exceed 500 for this model.

## Exact Lean declaration excerpts


**`FreeBoundary`.** The four free-end traces on classical modal solutions are second and third derivatives at both endpoints.

`DavisKahan/Sources/DavisKahan1970/Section9/FreeBeamCharacteristic.lean` — `FreeBoundary` (exact declaration header; proof body omitted):

```lean
@[expose]
def FreeBoundary (beta a b c d : ℝ) : Prop :=
```


**`characteristic_eq_zero_of_freeBoundary`.** A nontrivial positive-frequency classical eigenmode obeying free-end conditions satisfies the characteristic equation. The converse requires a separate modal construction.

`DavisKahan/Sources/DavisKahan1970/Section9/FreeBeamCharacteristic.lean` — `characteristic_eq_zero_of_freeBoundary` (exact declaration header; proof body omitted):

```lean
theorem characteristic_eq_zero_of_freeBoundary
    {beta a b c d : ℝ} (hbeta : beta ≠ 0)
    (hboundary : FreeBoundary beta a b c d)
    (hnonzero : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    characteristic beta = 0 :=
```


**`beamOperator_is_closure_of_classical_freeBeam_fourthDerivative`.** The concrete **real** beam realization is identified as the closure of the classical fourth-derivative graph; formal Green symmetry by itself is not enough.

`DavisKahan/Specialized/FreeBeam/BeamClassicalReal.lean` — `beamOperator_is_closure_of_classical_freeBeam_fourthDerivative` (exact declaration header; proof body omitted):

```lean
theorem beamOperator_is_closure_of_classical_freeBeam_fourthDerivative :
    _root_.IsSelfAdjoint beamOperator ∧
      closure classicalFreeBeamGraph =
        (beamOperator.graph : Set (BeamL2 × BeamL2)) :=
```


**`real_freeBeam_zero_eigenspace_eq_beamTrial`.** The zero eigenspace is precisely the two-dimensional affine trial plane, with the domain condition retained explicitly.

`DavisKahan/Sources/DavisKahan1970/Section9/RealModel.lean` — `real_freeBeam_zero_eigenspace_eq_beamTrial` (exact declaration header; proof body omitted):

```lean
theorem real_freeBeam_zero_eigenspace_eq_beamTrial :
    Module.finrank ℝ
        DavisKahan.FreeBeam.Model.Real.beamTrial = 2 ∧
      ∀ (x : RealBeamL2) (h : x ∈ realBeamOperator.domain),
        realBeamOperator ⟨x, h⟩ = 0 ↔
          x ∈ DavisKahan.FreeBeam.Model.Real.beamTrial :=
```
