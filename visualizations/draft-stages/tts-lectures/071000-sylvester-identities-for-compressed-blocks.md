# 071000 — Sylvester identities for compressed blocks

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `021000` Rayleigh–Ritz compression; `030000` spectral projections; `043000` directed sines; `062000–070000` Sylvester equations. **Next:** `072000` infinite-dimensional Hilbert examples.

<!-- BEGIN SPOKEN LECTURE -->

# Finding the Sylvester equation inside a subspace problem

A Sylvester estimate can turn a bound on an operator C into a bound on the unknown X. But a subspace perturbation problem is given in a different form. We have two self-adjoint operators and want to compare two subspaces that they preserve. Where is the Sylvester equation hiding?

Multiplication by the relevant spectral projections produces an exact identity before any gap condition is imposed. The gap enters only when we try to estimate its solution. Keeping those steps separate makes clear which claims are purely algebraic and which depend on spectral separation.

## Two operators and two invariant subspaces

Let T be a bounded self-adjoint operator on a Hilbert space. Let S equal T plus a perturbation E, also self-adjoint. Choose an orthogonal projection P whose range is invariant under T. Choose another orthogonal projection Q whose range is invariant under S. For spectral projections, invariance is automatic and the orthogonal complements are invariant as well.

We want to measure how much of a vector in the P subspace falls outside the Q subspace. The relevant map first includes a vector from the P subspace into the ambient Hilbert space, then applies I minus Q. Call this map X.

Its norm is the largest possible length outside Q of a unit vector from P. This is the directed sine of the principal angles from the first subspace to the second: projecting a unit vector into the complementary target space measures the sine of its escape angle. Thus our unknown Sylvester operator will have a direct geometric meaning.

Now restrict S to the orthogonal complement of Q; call this restricted operator A. Restrict T to the range of P; call that operator B. Because both original subspaces reduce their respective self-adjoint operators, A and B are self-adjoint on their smaller Hilbert spaces.

The desired equation will be A times X minus X times B equals a projected piece of E.

## Derivation one line at a time

Take a vector p in the range of P. The value X of p is the component of p orthogonal to the range of Q.

Apply A to X of p. Since S preserves the complement of Q, the result is I minus Q applied to S of p. We used commutation of S with Q to remove an unnecessary second projection.

Next apply X to B of p. Since B is simply T restricted to the P subspace, and T preserves that subspace, the result is I minus Q applied to T of p.

Subtract. We get I minus Q applied to S of p minus T of p. Since S minus T equals E, the answer is I minus Q applied to E of p.

We have proved the exact identity: A X minus X B equals the perturbation E, restricted to the P subspace on the input side and projected outside Q on the output side.

Nothing in this computation used an estimate. Nothing required the two subspaces to be close. We used only the reducing properties and the equality S equals T plus E.

This order of work is important. First prove an identity with the correct spaces and projections. Only afterward ask what spectral separation is available for A and B.

## A two-dimensional calculation

Let T be diagonal with entries zero and two. Its zero eigenspace is the horizontal coordinate axis, and P projects onto that axis.

Let S be the matrix with every entry equal to one. It has eigenvalue zero on the line spanned by the vector one, negative one, and eigenvalue two on the line spanned by one, one. Let Q project onto the zero eigenspace of S.

The perturbation E is S minus T. Its first column is one, one, while its second column is one, negative one.

The Q complement is the line spanned by the normalized vector one, one. The vector e-one, which generates the P subspace, has projection onto that line of length one over the square root of two. Therefore the norm of X is one over the square root of two.

A is multiplication by two on that Q-complement line. B is multiplication by zero on the P line. So A X minus X B is simply twice X, whose norm is the square root of two.

Meanwhile E sends e-one to one, one, which already lies in the Q complement. Its norm is the square root of two. The right-hand side agrees exactly, not just approximately.

The spectral gap between A and B is two. The constant-one Sylvester inequality becomes two times one over the square root of two at most the square root of two. Here equality holds.

## What the gap does and does not compare

Notice which spectra appear: the selected spectral part of T, and the complementary spectral part of S. In this example they were the eigenvalues zero and two.

A gap between the entire spectra of T and S would be irrelevant and often impossible to assume. Both operators may have eigenvalues in the same region. The useful condition separates the target cluster of one operator from the exterior cluster of the other.

The identity alone gives no angle bound if those two restricted spectra meet. When A and B share a value, the Sylvester operator may have a kernel, so a small residual need not imply a small cross-projection block.

If A and B are separated by a positive ordered gap, the semigroup theorem gives the operator-norm estimate. Under merely pairwise separation, the Hilbert–Schmidt theorem gives its square-norm bound, with the corresponding operator-norm bounds needing their own hypotheses.

This explains why exact spectral-gap wording is essential in any sine-theta theorem.

## The companion directed block

There is a second directed error, obtained by starting with a vector in Q and measuring how much lies outside P. Its operator maps the Q subspace to the complement of P.

Run the same construction with S and T exchanged. The right-hand side is now the corresponding projection of negative E. Its norm obeys the same elementary estimate because replacing E by negative E does not change norm.

For equal-dimensional finite subspaces, the nontrivial principal angles agree in the two directions. In different dimensions or infinite dimensions, the directed blocks carry different information about defects and right-angle directions. We cannot discard one solely because the other is small unless the geometry supplies an additional identification.

The two crossed blocks encode escape in opposite directions. When dimensions differ, one direction can have a right-angle defect that the other does not; the ambient difference between the two projections records both.

## The Rayleigh–Ritz version

The same algebra works when the P subspace is only a trial subspace and need not be invariant. Let V be an isometric embedding of the trial coordinate space. Form the compressed matrix M by applying V adjoint, then T, then V. Its residual R is T V minus V M.

Let Q now be a genuine reducing spectral projection of T. The cross map X is I minus Q applied to V. Let A be T restricted to the Q complement. Multiply X by A, subtract X M, and use commutation of Q with T.

The result is I minus Q applied to R. The proof takes the same three lines as before. We obtain a Sylvester equation whose right-hand side is the portion of the Rayleigh–Ritz residual outside the exact spectral subspace.

This version explains the appearance of residual norms in eigenvector and invariant-subspace approximation theory. One does not need to first construct a perturbed operator S. The trial subspace itself supplies the compression and the residual.

## Domains in the unbounded setting

The extension requires an additional hypothesis. If T or S is unbounded, its action is defined only on its domain. The expression T applied to a vector in the P subspace is meaningful only if that vector belongs to the domain. The apparent matrix multiplication may be illegal otherwise.

The infinite-dimensional source develops bounded spectral cut operators and proves block identities first on dense domains. It then extends the resulting bounded expressions using continuity. Spectral projections commute with the self-adjoint operator in a domain-aware sense, and bounded spectral windows control the terms individually.

The exact bounded-operator residual identity identifies the unknown cross-projection block, both compressed generators, and the residual. The Hilbert-space extension requires spectral projections with the right measurability properties; for unbounded generators it additionally requires domain compatibility.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

With bounded self-adjoint \(T,S=T+E\), reducing orthogonal projections \(P\) for \(T\) and \(Q\) for \(S\), let \(H_P=\operatorname{ran}P\) and \(H_{Q^\perp}=\operatorname{ran}(I-Q)\). Define
\[
X=(I-Q)|_{H_P}:H_P\to H_{Q^\perp},\quad
A=S|_{H_{Q^\perp}},\quad B=T|_{H_P}.
\]
Then
\[
AX-XB=(I-Q)E|_{H_P},\qquad
\|X\|=\|(I-Q)P\|.
\]
This also has a Rayleigh–Ritz variant: if \(V^*V=I\), \(M=V^*TV\), \(R=TV-VM\), and \(Q\) reduces \(T\), then
\[
(T|_{Q^\perp})[(I-Q)V]-[(I-Q)V]M=(I-Q)R.
\]
The infinite-dimensional Lean source uses domain-aware spectral cuts, and its block identity is more general than the bounded-algebra proof narrated here.

**Lean bridge (verified source excerpts).**

`DavisKahan/InfiniteDimensional/SinTheta/Restriction.lean` — `directedPerturbation_sylvesterEquation` (exact source declaration header):

```lean
theorem directedPerturbation_sylvesterEquation
    {A B : E →L[𝕜] E}
    (_hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A) (hV : Submodule.IsReducing V B) :
    ContinuousLinearMap.sylvester (B.restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
      _).mp hV.orthogonal_mem_invtSubmodule))
      (A.restrict hU.mem_invtSubmodule)
      (((Vᗮ.starProjection ∘L U.subtypeL)).codRestrict Vᗮ
        (fun _x => Vᗮ.starProjection_apply_mem _)) =
      ((Vᗮ.starProjection ∘L (B - A) ∘L U.subtypeL)).codRestrict Vᗮ
        (fun _x => Vᗮ.starProjection_apply_mem _) := by
```

The formal conclusion is the exact compressed perturbation equation; `U` reduces the old `A`, `V` reduces the new `B`, and the projected difference `B - A` is the Sylvester defect.

`DavisKahan/InfiniteDimensional/SinTheta/Restriction.lean` — `directedResidual_sylvesterEquation` (exact source declaration header):

```lean
theorem directedResidual_sylvesterEquation
    {A : E →L[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Submodule.IsReducing U A)
    {X : F →L[𝕜] E} {M : F →L[𝕜] F} :
    ContinuousLinearMap.sylvester (A.restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
      _).mp hU.orthogonal_mem_invtSubmodule)) M
      (((Uᗮ.starProjection ∘L X)).codRestrict Uᗮ (fun _x => Uᗮ.starProjection_apply_mem _)) =
      ((Uᗮ.starProjection ∘L DavisKahan.residual A X M)).codRestrict Uᗮ
        (fun _x => Uᗮ.starProjection_apply_mem _) := by
```

This version uses a trial map `X` and its `DavisKahan.residual` with a trial compression `M`; the exact spectral complement supplies the left restricted operator.
