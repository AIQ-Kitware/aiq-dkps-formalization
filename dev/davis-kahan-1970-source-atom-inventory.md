# Davis--Kahan 1970 source atom inventory

This is the source-side completeness denominator. It says **what the paper asserts**, not whether Lean has proved it.

- Source blocks: **49**
- Atomic source items: **266**
- Numbered equation atoms: **64/64**
- Formal-disposition obligations: **259**
- Non-completion source-state atoms: **7** (5 actual open questions; 2 historical knowledge/deferred-proof statements)

The audit was performed against the public 46-page PDF identified by DOI `10.1137/0707001`; the modernized transcription was used only as a readability aid and is not required by the repository.

## Source-spec repairs made by this audit

- `S1-ui-norms.cosine-law` — Restored the unnumbered cosine-law identity immediately after (1.14).
- `DK-3.3-prop.eq-3-7` — Restored equation (3.7), the block formula for Q=UPU^{-1}.
- `DK-4.1-prop.eq-4-1` — Restored equation (4.1), the minimax characterization of the singular displacement values.
- `DK-4.1-prop.eq-4-2` — Restored equation (4.2), the pointwise angle comparison used in Proposition 4.1.
- `DK-9-model.unperturbed-strict-eigenvalue-order` — Restored the source ordering alpha1=0=alpha2<alpha3<alpha4<... rather than weakening it to positivity of the later roots.
- `DK-9.8.lower-bound-asymptotic` — Restored the source lower-bound comparison and O(epsilon^4) asymptotic preceding (9.8).

## Atoms in source order

### `S1-block-residual`

- `S1-block-residual.setup-hilbert-scope` — **scope** — Separable real or complex Hilbert space; bounded main setting with stated unbounded extension.
- `S1-block-residual.reducing-projector-setup` — **construction** — P reduces A and E0,E1 are isometries onto the two reducing summands.
- `S1-block-residual.q-reduces-perturbed` — **construction** — Q reduces A+H and F0,F1 give its reducing decomposition.
- `S1-block-residual.no-spectral-projector-assumption` — **scope** — P and Q need not be spectral projectors and the diagonal spectral sets may overlap.
- `S1-block-residual.unitary-intertwiner-dimension-criterion` — **assertion** — A unitary carrying P-space to Q-space exists precisely with the two matching dimension conditions.
- `S1-block-residual.within-subspace-coordinate-freedom` — **assertion** — Changing the intertwining unitary changes only the within-subspace unitary coordinates W0,W1.
- `S1-block-residual.residual-inherited-block` — **identity** — When A0 is inherited from A, R=H E0 and is the first block column of H.
- `S1-block-residual.rayleigh-ritz-h0-zero` — **identity** — The Rayleigh--Ritz choice A0=E0*(A+H)E0 is equivalent here to H0=0.
- `S1-block-residual.residual-gram-split` — **identity** — R*R=H0^2+B*B.
- `S1-block-residual.rayleigh-ritz-minimizes-residual` — **extremal** — The Rayleigh--Ritz choice minimizes residual size among the block choices under discussion.
- `S1-block-residual.one-sided-vs-strong-offdiagonal` — **scope** — H0=0 is distinguished from the stronger H0=H1=0 condition.
- `S1-block-residual.residual-eigenvalue-sum` — **consequence** — There is an ordering of m exact eigenvalues with sum_j (alpha_j-lambda_j)^2 <= ||R||_sq^2.
- `S1-block-residual.residual-eigenvalue-pointwise` — **consequence** — The same ordering satisfies |alpha_j-lambda_j| <= ||R||_1.
- `S1-block-residual.eq-1-1` — **numbered-equation** — Exact mathematical content of source equation (1.1) as reconstructed in the distributable TeX.
- `S1-block-residual.eq-1-2` — **numbered-equation** — Exact mathematical content of source equation (1.2) as reconstructed in the distributable TeX.
- `S1-block-residual.eq-1-3` — **numbered-equation** — Exact mathematical content of source equation (1.3) as reconstructed in the distributable TeX.
- `S1-block-residual.eq-1-4` — **numbered-equation** — Exact mathematical content of source equation (1.4) as reconstructed in the distributable TeX.
- `S1-block-residual.eq-1-5` — **numbered-equation** — Exact mathematical content of source equation (1.5) as reconstructed in the distributable TeX.
- `S1-block-residual.eq-1-6` — **numbered-equation** — Exact mathematical content of source equation (1.6) as reconstructed in the distributable TeX.
- `S1-block-residual.eq-1-7` — **numbered-equation** — Exact mathematical content of source equation (1.7) as reconstructed in the distributable TeX.
- `S1-block-residual.eq-1-8` — **numbered-equation** — Exact mathematical content of source equation (1.8) as reconstructed in the distributable TeX.
### `S1-ui-norms`

- `S1-ui-norms.ui-rank-one-normalization` — **definition** — Rank-one operators satisfy the normalized unitary-invariant norm convention.
- `S1-ui-norms.ui-contraction-monotonicity` — **assertion** — Left and right multiplication by contractions cannot increase a unitary-invariant norm.
- `S1-ui-norms.singular-minimax-noncompact-scope` — **scope** — The singular-value minimax expression extends to bounded noncompact operators, with spectral-multiplicity cautions.
- `S1-ui-norms.hilbert-schmidt-identity` — **definition** — The Hilbert--Schmidt norm is the square root of the sum of squared singular values and trace K*K.
- `S1-ui-norms.fan-dominance` — **theorem** — All-unitary-invariant-norm comparison is equivalent to comparison in every Ky Fan norm.
- `S1-ui-norms.eq1-13-variational` — **variational** — The Ky Fan norm also equals the supremum of the real sum of y_k* K x_k over orthonormal tuples.
- `S1-ui-norms.cosine-law` — **identity** — The vector-angle convention satisfies ||x+y||^2=||x||^2+||y||^2+2||x||||y||cos angle(x,y). **[restored in PDF re-audit]**
- `S1-ui-norms.s0-singular-values` — **assertion** — The singular values of S0 are sin(theta_k) for the principal-angle data.
- `S1-ui-norms.ambient-angle-doubling` — **assertion** — Nonzero angle data of the ambient angle operator occur twice, once from each side.
- `S1-ui-norms.directed-sine-norm` — **identity** — ||Q^perp P||=||Q^perp E0||=||sin Theta0|| for every UI norm.
- `S1-ui-norms.ambient-sine-norm` — **identity** — ||P-Q||=||sin Theta|| for every UI norm.
- `S1-ui-norms.operator-largest-one-sided-distance` — **identity** — In operator norm the largest one-sided distance is ||sin Theta||_1.
- `S1-ui-norms.closest-unit-vector-distance` — **identity** — The closest-unit-vector distance is 2||sin(Theta/2)||_1.
- `S1-ui-norms.j-block-form` — **construction** — Section 3 constructs the skew block partial isometry J from J0.
- `S1-ui-norms.direct-rotation-exponential` — **identity** — The distinguished direct rotation satisfies U=exp(J Theta)=cos Theta+J sin Theta with the displayed block form.
- `S1-ui-norms.eq-1-9` — **numbered-equation** — Exact mathematical content of source equation (1.9) as reconstructed in the distributable TeX.
- `S1-ui-norms.eq-1-10` — **numbered-equation** — Exact mathematical content of source equation (1.10) as reconstructed in the distributable TeX.
- `S1-ui-norms.eq-1-11` — **numbered-equation** — Exact mathematical content of source equation (1.11) as reconstructed in the distributable TeX.
- `S1-ui-norms.eq-1-12` — **numbered-equation** — Exact mathematical content of source equation (1.12) as reconstructed in the distributable TeX.
- `S1-ui-norms.eq-1-13` — **numbered-equation** — Exact mathematical content of source equation (1.13) as reconstructed in the distributable TeX.
- `S1-ui-norms.eq-1-14` — **numbered-equation** — Exact mathematical content of source equation (1.14) as reconstructed in the distributable TeX.
- `S1-ui-norms.eq-1-15` — **numbered-equation** — Exact mathematical content of source equation (1.15) as reconstructed in the distributable TeX.
- `S1-ui-norms.eq-1-16` — **numbered-equation** — Exact mathematical content of source equation (1.16) as reconstructed in the distributable TeX.
- `S1-ui-norms.eq-1-17` — **numbered-equation** — Exact mathematical content of source equation (1.17) as reconstructed in the distributable TeX.
- `S1-ui-norms.eq-1-18` — **numbered-equation** — Exact mathematical content of source equation (1.18) as reconstructed in the distributable TeX.
### `S2-sin-theta`

- `S2-sin-theta.family-distinctness` — **scope** — The four Section 2 theorem families are distinct rather than mere restatements.
- `S2-sin-theta.ui-norm-scope` — **scope** — Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm.
- `S2-sin-theta.gap-hypothesis` — **hypothesis** — The sine theorem uses interval/exterior separation, allowing the A0 and Lambda1 roles to be interchanged.
- `S2-sin-theta.directed-conclusion` — **theorem** — delta ||sin Theta0|| <= ||R||.
### `S2-tan-theta`

- `S2-tan-theta.ordered-gap-hypothesis` — **hypothesis** — The tangent theorem assumes A0 below Lambda1 by delta.
- `S2-tan-theta.rayleigh-ritz-hypothesis` — **hypothesis** — The tangent theorem assumes H0=0, equivalently the Rayleigh--Ritz block choice.
- `S2-tan-theta.directed-conclusion` — **theorem** — delta ||tan Theta0|| <= ||R||.
- `S2-tan-theta.ambient-conclusion` — **theorem** — delta ||tan Theta|| <= ||H||.
### `S2-sin-two-theta`

- `S2-sin-two-theta.gap-hypothesis` — **hypothesis** — The double-sine theorem separates Lambda0 from Lambda1 by an interval/exterior gap.
- `S2-sin-two-theta.directed-conclusion` — **theorem** — delta ||sin(2 Theta0)|| <= 2||R||.
- `S2-sin-two-theta.ambient-conclusion` — **theorem** — delta ||sin(2 Theta)|| <= 2||H||.
### `S2-tan-two-theta`

- `S2-tan-two-theta.ordered-gap-hypothesis` — **hypothesis** — The double-tangent theorem assumes A0 below A1 by delta.
- `S2-tan-two-theta.strong-offdiagonal-hypothesis` — **hypothesis** — The double-tangent theorem assumes H0=H1=0.
- `S2-tan-two-theta.no-extra-pole-hypothesis` — **scope** — The printed theorem has no independent tan-pole exclusion or perturbed-block spectral-placement hypothesis.
- `S2-tan-two-theta.directed-conclusion` — **theorem** — delta ||tan(2 Theta0)|| <= 2||R||.
- `S2-tan-two-theta.ambient-conclusion` — **theorem** — delta ||tan(2 Theta)|| <= 2||H||.
- `S2-tan-two-theta.pole-exclusion-derived` — **proof-claim** — Section 7 derives the needed nonvanishing cosine factors from the printed hypotheses.
### `S2-sharpness`

- `S2-sharpness.constants-best-possible` — **sharpness** — The constants in all four theorem families are best possible.
- `S2-sharpness.two-dimensional-equality` — **sharpness** — Two-dimensional examples attain the constants.
- `S2-sharpness.direct-sum-simultaneous-equality` — **sharpness** — Orthogonal sums give simultaneous equality for all UI norms.
- `S2-sharpness.first-order-asymptotic` — **sharpness** — All four estimates share the stated first-order epsilon asymptotics.
### `S2-unbounded-scope`

- `S2-unbounded-scope.infinite-dimensional-scope` — **scope** — All four main results apply in infinite as well as finite dimension.
- `S2-unbounded-scope.arbitrary-ui-scope` — **scope** — All four main results apply to arbitrary UI norms.
- `S2-unbounded-scope.unbounded-selfadjoint-scope` — **scope** — The results extend to unbounded self-adjoint A under the stated domain condition.
- `S2-unbounded-scope.bounded-residual-needed` — **scope** — Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.
- `S2-unbounded-scope.half-infinite-gap-intervals` — **scope** — Gap intervals may be half-infinite and the remaining spectra unbounded.
### `DK-3.1-def`

- `DK-3.1-def.s0-s1-singular-values` — **assertion** — S0 and S1 have the same nonzero singular values, with the stated possible initial unit singular values from unequal C0 nullities.
- `DK-3.1-def.direct-rotation-definition` — **definition** — A direct rotation is a unitary intertwiner with C0,C1 positive and S1=S0*.
- `DK-3.1-def.u-notation` — **definition** — The paper reserves U for direct rotations.
- `DK-3.1-def.eq-3-1` — **numbered-equation** — Exact mathematical content of source equation (3.1) as reconstructed in the distributable TeX.
- `DK-3.1-def.eq-3-2` — **numbered-equation** — Exact mathematical content of source equation (3.2) as reconstructed in the distributable TeX.
- `DK-3.1-def.eq-3-3` — **numbered-equation** — Exact mathematical content of source equation (3.3) as reconstructed in the distributable TeX.
- `DK-3.1-def.eq-3-4` — **numbered-equation** — Exact mathematical content of source equation (3.4) as reconstructed in the distributable TeX.
### `DK-3.2-def`

- `DK-3.2-def.acute-case-definition` — **definition** — The acute case is exactly the vanishing of the two crossing intersections.
### `DK-3.1-prop`

- `DK-3.1-prop.existence` — **theorem** — In the acute case a direct rotation exists.
- `DK-3.1-prop.uniqueness` — **theorem** — In the acute case the direct rotation is unique.
- `DK-3.1-prop.positive-diagonal-characterization` — **theorem** — Positivity of C0,C1 characterizes the direct rotation among unitary intertwiners in the acute case.
### `DK-3.2-prop`

- `DK-3.2-prop.existence-iff-crossing-dimensions` — **theorem** — Outside the acute case, direct rotation existence is equivalent to equality of the crossing dimensions.
- `DK-3.2-prop.nonuniqueness` — **theorem** — When it exists outside the acute case it need not be unique.
- `DK-3.2-prop.crossing-square-minus-one` — **theorem** — On the crossing subspaces U^2 x=-x.
- `DK-3.2-prop.bilateral-shift-counterexample` — **counterexample** — The bilateral-shift example shows the basic P/Q dimension conditions do not imply the crossing-dimension condition.
- `DK-3.2-prop.eq-3-5` — **numbered-equation** — Exact mathematical content of source equation (3.5) as reconstructed in the distributable TeX.
### `DK-3.3-prop`

- `DK-3.3-prop.reflection-conjugacy` — **identity** — With X=P-Pperp and Q_-=XQX, U^{-1}=XUX.
- `DK-3.3-prop.principal-square-root` — **theorem** — Every direct rotation is the principal unitary square root of the product of the two reflections.
- `DK-3.3-prop.square-root-converse` — **theorem** — A principal square root is a direct rotation when it maps the two crossing subspaces appropriately.
- `DK-3.3-prop.eq-3-6` — **numbered-equation** — Exact mathematical content of source equation (3.6) as reconstructed in the distributable TeX.
- `DK-3.3-prop.eq-3-7` — **numbered-equation** — Exact mathematical content of source equation (3.7) as reconstructed in the distributable TeX. **[restored in PDF re-audit]**
- `DK-3.3-prop.eq-3-8` — **numbered-equation** — Exact mathematical content of source equation (3.8) as reconstructed in the distributable TeX.
### `DK-3.4-prop`

- `DK-3.4-prop.u-square-direct-rotation` — **theorem** — If C0^2>=1/2, then U^2 is the direct rotation from Q_- to Q.
### `DK-3.1-thm`

- `DK-3.1-thm.complete-invariant` — **theorem** — Spectral multiplicity functions of Theta0,Theta1 completely classify the pair under the stated dimension hypotheses.
- `DK-3.1-thm.converse-angle-data` — **theorem** — Conversely the angle operators may be arbitrary positive contractions in [0,pi/2] with matching spectral multiplicities away from zero and the stated dimensions.
- `DK-3.1-thm.reconstruction` — **construction** — The pair is reconstructed from the angle data and J0.
### `DK-3.1-cor`

- `DK-3.1-cor.compact-complete-invariants` — **theorem** — If PQperpP is compact, the eigenvalues of Theta0,Theta1 counted with multiplicity are complete invariants.
- `DK-3.1-cor.allowed-angle-sequence` — **theorem** — Theta0 eigenvalues may be any decreasing sequence in [0,pi/2] tending to zero plus possible zero eigenspace.
- `DK-3.1-cor.theta1-match` — **theorem** — Theta1 has the same nonzero eigenvalues and may differ only in zero multiplicity.
### `DK-3.5-prop`

- `DK-3.5-prop.commutation` — **theorem** — Theta commutes with P,Q,J,U.
- `DK-3.5-prop.direct-rotation-exponential` — **identity** — U=exp(J Theta).
- `DK-3.5-prop.cos-square-projector` — **identity** — cos^2 Theta=PQP+Pperp Qperp Pperp.
- `DK-3.5-prop.eigenvector-rotation-angle` — **theorem** — If Theta x=theta x then angle(x,Ux)=theta.
- `DK-3.5-prop.acute-maximal-characterization` — **theorem** — In the acute case each theta-eigenspace is the unique maximal P/Q-reducing subspace with the stated constant-angle properties.
### `DK-3.2-cor`

- `DK-3.2-cor.swap-invariance` — **theorem** — Swapping P and Q leaves Theta unchanged and sends J to -J.
### `DK-4.1-prop`

- `DK-4.1-prop.vz-factorization` — **construction** — Every unitary V carrying P to Q is written V=UZ with Z block diagonal in the Section 4 setup.
- `DK-4.1-prop.orthonormal-angle-lower-bounds` — **theorem** — For every such V there are orthonormal v_k in P with angle(v_k,Vv_k)>=theta_k.
- `DK-4.1-prop.singular-value-minimality` — **theorem** — Each singular value of (1-V)|P is minimized at V=U with value 2 sin(theta_k/2).
- `DK-4.1-prop.closest-q-vector-proof-step` — **proof-claim** — The pointwise comparison uses Qx/||Qx|| as the closest unit vector in Q-space.
- `DK-4.1-prop.eq-4-1` — **numbered-equation** — Exact mathematical content of source equation (4.1) as reconstructed in the distributable TeX. **[restored in PDF re-audit]**
- `DK-4.1-prop.eq-4-2` — **numbered-equation** — Exact mathematical content of source equation (4.2) as reconstructed in the distributable TeX. **[restored in PDF re-audit]**
### `DK-4.1-cor`

- `DK-4.1-cor.ui-minimality-on-p` — **theorem** — For every UI norm, ||(1-V)P|| is minimized at V=U.
### `DK-4.2-prop`

- `DK-4.2-prop.basis-sine-square-lower-bound` — **theorem** — For every orthonormal basis of P, sum sin^2 angle(v_k,Vv_k) >= sum sin^2 theta_k, including infinite RHS.
- `DK-4.2-prop.trace-identification` — **proof-claim** — The lower bound is identified with tr(S0* S0).
### `DK-4.3-prop`

- `DK-4.3-prop.plane-parameterization` — **construction** — On each principal two-plane V has the displayed a_j,b_j parameterization.
- `DK-4.3-prop.squared-displacement-global-minimum` — **theorem** — ||(1-V*)(1-V)|| is minimized by U for every UI norm.
- `DK-4.3-prop.operator-norm-displacement-minimum` — **consequence** — The operator norm of 1-V is minimized by U.
- `DK-4.3-prop.hilbert-schmidt-displacement-minimum` — **consequence** — The Hilbert--Schmidt norm of 1-V is minimized by U.
- `DK-4.3-prop.arbitrary-ui-displacement-warning` — **counterclaim** — Arbitrary UI norms of 1-V need not be minimized by U.
- `DK-4.3-prop.eq-4-3` — **numbered-equation** — Exact mathematical content of source equation (4.3) as reconstructed in the distributable TeX.
- `DK-4.3-prop.eq-4-4` — **numbered-equation** — Exact mathematical content of source equation (4.4) as reconstructed in the distributable TeX.
- `DK-4.3-prop.eq-4-5` — **numbered-equation** — Exact mathematical content of source equation (4.5) as reconstructed in the distributable TeX.
- `DK-4.3-prop.eq-4-6` — **numbered-equation** — Exact mathematical content of source equation (4.6) as reconstructed in the distributable TeX.
### `DK-4.4-prop`

- `DK-4.4-prop.example4-1-real-reflection` — **counterexample** — Example 4.1 gives a real reflection with singular values 2,0 versus two equal direct-rotation singular values and defeats the Ky Fan 2 norm for theta>pi/3.
- `DK-4.4-prop.example4-2-complex-phase` — **counterexample** — Example 4.2 uses V=e^{i delta}U and shows the full-displacement UI minimum can fail in complex space.
- `DK-4.4-prop.printed-proposition4-4` — **source-assertion** — The paper asserts that in real space with Theta<=pi/3, U minimizes ||1-V|| for every UI norm.
- `DK-4.4-prop.printed-sharp-threshold` — **source-assertion** — The paper asserts the pi/3 threshold is sharp in view of the examples.
### `DK-5.1-thm`

- `DK-5.1-thm.banach-hypotheses` — **hypothesis** — Banach-space theorem with ||B||<=alpha and ||A^{-1}||<=(alpha+delta)^{-1}, compatible cross norm.
- `DK-5.1-thm.sylvester-lower-bound` — **theorem** — AX-XB=C implies ||C||>=delta||X||.
- `DK-5.1-thm.roles-interchange` — **scope** — A and B roles/hypotheses may be interchanged.
- `DK-5.1-thm.one-sided-unbounded-extension` — **scope** — The proof covers densely-defined unbounded A with bounded inverse hypothesis while B,X remain bounded.
### `DK-5-hermitian-inequalities`

- `DK-5-hermitian-inequalities.pairwise-gap-hypothesis` — **hypothesis** — Hermitian A,B have pairwise spectral distance at least delta.
- `DK-5-hermitian-inequalities.operator-norm-constant-one-fails` — **counterclaim** — The operator-norm analogue with constant 1 can fail.
- `DK-5-hermitian-inequalities.rank-factor-not-best` — **sharpness** — Equation (5.2) is not best possible unless rank C<=1.
- `DK-5-hermitian-inequalities.universal-constant-question` — **open-question** — The source asks whether the rank factor can be replaced by a universal constant. **[non-completion source state]**
- `DK-5-hermitian-inequalities.constant-one-explicit-counterexample` — **counterexample** — The displayed 2x2 A,B,X example rules out universal constant 1.
- `DK-5-hermitian-inequalities.eq-5-1` — **numbered-equation** — Exact mathematical content of source equation (5.1) as reconstructed in the distributable TeX.
- `DK-5-hermitian-inequalities.eq-5-2` — **numbered-equation** — Exact mathematical content of source equation (5.2) as reconstructed in the distributable TeX.
### `DK-5.2-thm`

- `DK-5.2-thm.hilbert-unbounded-hypotheses` — **hypothesis** — Theorem 5.2 gives the Hilbert-space unbounded Sylvester setup with separated spectra and domain/core hypotheses.
- `DK-5.2-thm.hilbert-unbounded-conclusion` — **theorem** — The corresponding delta||X|| lower bound holds in the stated UI/ideal norm scope.
### `DK-5.1-lem`

- `DK-5.1-lem.strong-cutoff-convergence` — **lemma** — The spectral-cutoff approximants converge strongly in the manner stated and support the unbounded proof.
### `DK-6.1-lem`

- `DK-6.1-lem.ordered-sylvester-forward` — **lemma** — The ordered spectral separation implies the stated Sylvester/UI-norm lower bound.
- `DK-6.1-lem.ordered-sylvester-converse` — **lemma** — The source includes the converse characterization used in the single-angle proof.
### `DK-6.2-lem`

- `DK-6.2-lem.pinching-contraction` — **lemma** — The reflection/pinching operation contracts every unitary-invariant norm in the stated setup.
### `DK-6.1-prop`

- `DK-6.1-prop.sine-proof-residual-identity` — **identity** — The symmetric sine proof rewrites the relevant off-diagonal block as the Sylvester residual identity.
- `DK-6.1-prop.symmetric-sine-theorem` — **theorem** — Proposition 6.1 gives the symmetric sine-theta conclusion under two-sided spectral placement.
- `DK-6.1-prop.source-counterexample-need-two-sided` — **counterexample** — The source exhibits the failure of the ambient/symmetric conclusion when the needed two-sided placement is dropped.
- `DK-6.1-prop.eq-6-1` — **numbered-equation** — Exact mathematical content of source equation (6.1) as reconstructed in the distributable TeX.
### `DK-6.1-thm`

- `DK-6.1-thm.generalized-sine-hypotheses` — **hypothesis** — The generalized sine theorem allows nonisometric E0 with E0*E0 >= epsilon^2 and the stated spectral separation.
- `DK-6.1-thm.generalized-sine-conclusion` — **theorem** — delta epsilon ||sin Theta0|| <= ||R||.
- `DK-6.1-thm.unequal-dimension-scope` — **scope** — The generalized theorem allows unequal-dimensional comparison subspaces as stated.
### `DK-6.2-thm`

- `DK-6.2-thm.second-generalized-sine` — **theorem** — The second generalized sine theorem gives the Hilbert--Schmidt estimate under pairwise spectral separation.
- `DK-6.2-thm.rank-corrected-operator-consequence` — **consequence** — The stated rank-corrected operator-norm consequence follows.
### `DK-6.3-thm`

- `DK-6.3-thm.tangent-setup-identities` — **proof-claim** — Equations (6.2)--(6.6) provide the block identities used in the generalized tangent proof.
- `DK-6.3-thm.example6-1` — **counterexample** — Example 6.1 gives the explicit 2x2 counterexample showing one-sided placement is essential for the tangent conclusion.
- `DK-6.3-thm.generalized-tangent-theorem` — **theorem** — Theorem 6.3 gives the generalized tangent residual bound with its exact source hypotheses.
- `DK-6.3-thm.eq-6-2` — **numbered-equation** — Exact mathematical content of source equation (6.2) as reconstructed in the distributable TeX.
- `DK-6.3-thm.eq-6-3` — **numbered-equation** — Exact mathematical content of source equation (6.3) as reconstructed in the distributable TeX.
- `DK-6.3-thm.eq-6-4` — **numbered-equation** — Exact mathematical content of source equation (6.4) as reconstructed in the distributable TeX.
- `DK-6.3-thm.eq-6-5` — **numbered-equation** — Exact mathematical content of source equation (6.5) as reconstructed in the distributable TeX.
- `DK-6.3-thm.eq-6-6` — **numbered-equation** — Exact mathematical content of source equation (6.6) as reconstructed in the distributable TeX.
### `DK-6-appendix`

- `DK-6-appendix.unbounded-sine-extension` — **scope** — The sine theorem extends to unbounded operators via bounded residual/common-domain hypotheses.
- `DK-6-appendix.unbounded-tangent-extension` — **scope** — The tangent theorem requires the stronger approximation argument recorded in the Appendix.
- `DK-6-appendix.appendix-approximation-chain` — **proof-claim** — Equations (6.7)--(6.11) form the approximation chain controlling singular directions and passing to all UI norms.
- `DK-6-appendix.appendix-all-ui-limit` — **proof-claim** — The epsilon-to-zero argument completes the bound-norm case and then all UI norms.
- `DK-6-appendix.eq-6-7` — **numbered-equation** — Exact mathematical content of source equation (6.7) as reconstructed in the distributable TeX.
- `DK-6-appendix.eq-6-8` — **numbered-equation** — Exact mathematical content of source equation (6.8) as reconstructed in the distributable TeX.
- `DK-6-appendix.eq-6-9` — **numbered-equation** — Exact mathematical content of source equation (6.9) as reconstructed in the distributable TeX.
- `DK-6-appendix.eq-6-10` — **numbered-equation** — Exact mathematical content of source equation (6.10) as reconstructed in the distributable TeX.
- `DK-6-appendix.eq-6-11` — **numbered-equation** — Exact mathematical content of source equation (6.11) as reconstructed in the distributable TeX.
### `DK-6.3-lem`

- `DK-6.3-lem.approximation-number-leakage` — **lemma** — Lemma 6.3 controls the approximation/singular-number leakage used in the Appendix, including the stated finite and real forms.
### `DK-7-sin2-proof`

- `DK-7-sin2-proof.reflection-setup` — **proof-claim** — The reflection construction converts the double-angle geometry into a single-angle comparison.
- `DK-7-sin2-proof.ambient-sin2` — **theorem** — The Section 7 proof derives the ambient sin2Theta perturbation estimate.
- `DK-7-sin2-proof.directed-sin2` — **theorem** — It separately derives the directed sin2Theta0 residual estimate.
- `DK-7-sin2-proof.factor-one-directed-residual-refinement` — **proof-claim** — The directed block residual estimate has the source factor-one intermediate bound before the headline factor 2 form.
- `DK-7-sin2-proof.swap-asymmetry` — **scope** — The source records the asymmetry involved in swapping the two operators/subspaces in the residual form.
- `DK-7-sin2-proof.eq-7-1` — **numbered-equation** — Exact mathematical content of source equation (7.1) as reconstructed in the distributable TeX.
- `DK-7-sin2-proof.eq-7-2` — **numbered-equation** — Exact mathematical content of source equation (7.2) as reconstructed in the distributable TeX.
- `DK-7-sin2-proof.eq-7-3` — **numbered-equation** — Exact mathematical content of source equation (7.3) as reconstructed in the distributable TeX.
- `DK-7-sin2-proof.eq-7-4` — **numbered-equation** — Exact mathematical content of source equation (7.4) as reconstructed in the distributable TeX.
- `DK-7-sin2-proof.eq-7-5` — **numbered-equation** — Exact mathematical content of source equation (7.5) as reconstructed in the distributable TeX.
### `DK-7-tan2-proof`

- `DK-7-tan2-proof.tan2-block-identity` — **proof-claim** — Equation (7.6) gives the decisive tangent double-angle block identity.
- `DK-7-tan2-proof.cos2-pole-exclusion` — **proof-claim** — The singular-vector argument proves the relevant cos(2 theta_j) factors do not vanish from the source hypotheses.
- `DK-7-tan2-proof.ambient-tan2` — **theorem** — The proof yields the ambient tan2Theta perturbation estimate.
- `DK-7-tan2-proof.directed-tan2` — **theorem** — The proof yields the directed tan2Theta0 residual estimate.
- `DK-7-tan2-proof.eq-7-6` — **numbered-equation** — Exact mathematical content of source equation (7.6) as reconstructed in the distributable TeX.
### `DK-8.1-thm`

- `DK-8.1-thm.branch-problem` — **scope** — Small double-angle trigonometric quantities alone do not select angles near zero; the chosen reducing subspace matters.
- `DK-8.1-thm.acute-iff-spectral-placement` — **theorem** — Theta<=pi/4 iff the chosen perturbed reducing blocks lie on the corresponding sides of the gap.
- `DK-8.1-thm.existence-correct-q` — **theorem** — A reducing spectral projector Q with the required placement exists and is unique in the stated sense.
- `DK-8.1-thm.part-i-compression` — **theorem** — The upper/lower block compression inequalities of part (i).
- `DK-8.1-thm.part-ii-eigenvalue` — **theorem** — The finite-dimensional eigenvalue displacement inequalities of part (ii), with natural infinite-dimensional extensions.
- `DK-8.1-thm.part-iii-gauge` — **theorem** — The symmetric-gauge majorization inequalities of part (iii).
- `DK-8.1-thm.exclude-pi-over-four` — **proof-claim** — Equations (8.1)--(8.2) exclude theta=pi/4 and then theta>pi/4 under the selected placement.
- `DK-8.1-thm.spectral-repulsion-interpretation` — **consequence** — Strong off-diagonal eigenvector rotation forces definite eigenvalue displacement as described.
- `DK-8.1-thm.eq-8-1` — **numbered-equation** — Exact mathematical content of source equation (8.1) as reconstructed in the distributable TeX.
- `DK-8.1-thm.eq-8-2` — **numbered-equation** — Exact mathematical content of source equation (8.2) as reconstructed in the distributable TeX.
### `DK-8.2-thm`

- `DK-8.2-thm.smallness-alternative` — **hypothesis** — The theorem assumes either ||H||_1<delta/2 or ||R||_1<delta/2 plus the stated A0 interval.
- `DK-8.2-thm.double-angle-bound-retained` — **theorem** — The corresponding sin2 double-angle estimate remains valid.
- `DK-8.2-thm.acute-branch-conclusion` — **theorem** — Theta<pi/4.
- `DK-8.2-thm.homotopy-proof` — **proof-claim** — The perturbation proof uses the continuous spectral-projector homotopy and the displayed arcsine bound.
- `DK-8.2-thm.residual-reduction` — **proof-claim** — The residual form is reduced by changing the complementary perturbation block while preserving the residual/spectral data.
- `DK-8.2-thm.sin2-unequal-dimension-extension` — **scope** — The source states a sin2 extension to unequal comparison dimensions.
- `DK-8.2-thm.no-tan2-unequal-dimension-extension-known` — **knowledge-state** — No analogous tan2 extension was known. **[non-completion source state]**
### `DK-9-model`

- `DK-9-model.real-l2-model` — **definition** — The numerical model is real L2(0,1) with the free-end fourth-derivative self-adjoint closure and multiplication perturbation epsilon t.
- `DK-9-model.perturbed-eigenproblem` — **definition** — The displayed fourth-order perturbed boundary-value eigenproblem.
- `DK-9-model.unperturbed-strict-eigenvalue-order` — **assertion** — The source orders alpha1=0=alpha2<alpha3<alpha4<... with multiplicity. **[restored in PDF re-audit]**
- `DK-9-model.positive-root-equation` — **assertion** — For k>2, alpha_k are the positive roots of cos(alpha_k^(1/4)) cosh(alpha_k^(1/4))=1.
- `DK-9-model.positive-spectrum-over-500` — **assertion** — All positive alpha_k exceed 500.
- `DK-9-model.zero-eigenfunctions` — **construction** — The displayed w1,w2 are orthonormal linear eigenfunctions for the zero eigenvalue.
- `DK-9-model.lambda3-lower-bound` — **assertion** — H>=0 implies lambda3>=alpha3>500.
- `DK-9-model.initial-residual-formula` — **identity** — For A0=0, R=HE0 with the displayed residual functions r_k.
- `DK-9-model.residual-gram` — **identity** — The displayed 2x2 R*R matrix.
- `DK-9-model.residual-gram-eigenvalues` — **assertion** — R*R has eigenvalues epsilon^2(11+-sqrt76)/30.
### `DK-9.1-9.4`

- `DK-9.1-9.4.sin-bound-comparison` — **consequence** — The paper notes (9.1) is sharper than the easy sin2 bound (9.2).
- `DK-9.1-9.4.kyfan-two-term-scope` — **scope** — Equations (9.3)--(9.4) use the two-term Ky Fan norm to estimate both principal angles simultaneously.
- `DK-9.1-9.4.eq-9-1` — **numbered-equation** — Exact mathematical content of source equation (9.1) as reconstructed in the distributable TeX.
- `DK-9.1-9.4.eq-9-2` — **numbered-equation** — Exact mathematical content of source equation (9.2) as reconstructed in the distributable TeX.
- `DK-9.1-9.4.eq-9-3` — **numbered-equation** — Exact mathematical content of source equation (9.3) as reconstructed in the distributable TeX.
- `DK-9.1-9.4.eq-9-4` — **numbered-equation** — Exact mathematical content of source equation (9.4) as reconstructed in the distributable TeX.
### `DK-9.5-9.7`

- `DK-9.5-9.7.rayleigh-ritz-matrix` — **identity** — The displayed Rayleigh--Ritz matrix is E0*(A+H)E0.
- `DK-9.5-9.7.refined-residual-gram` — **identity** — The displayed refined residual Gram matrix and its one/two-term norm equal epsilon/sqrt15.
- `DK-9.5-9.7.tangent-gap` — **assertion** — The tangent gap may be taken as 500-0.7887 epsilon.
- `DK-9.5-9.7.kyfan-tan-bound` — **consequence** — The same RHS as (9.6) bounds tan theta1+tan theta2 in the two-term Ky Fan norm.
- `DK-9.5-9.7.offdiagonal-complement-choice` — **construction** — For tan2 the complementary block is chosen as E1*(A+H)E1>500 to obtain an off-diagonal comparison.
- `DK-9.5-9.7.kyfan-tan2-bound` — **consequence** — The same RHS as (9.7) bounds tan2theta1+tan2theta2 in the two-term Ky Fan norm.
- `DK-9.5-9.7.eq-9-5` — **numbered-equation** — Exact mathematical content of source equation (9.5) as reconstructed in the distributable TeX.
- `DK-9.5-9.7.eq-9-6` — **numbered-equation** — Exact mathematical content of source equation (9.6) as reconstructed in the distributable TeX.
- `DK-9.5-9.7.eq-9-7` — **numbered-equation** — Exact mathematical content of source equation (9.7) as reconstructed in the distributable TeX.
### `DK-9.8`

- `DK-9.8.weinberger-sine-square` — **external-result** — Weinberger method gives the displayed sine-square estimate from Ritz upper/lower bounds and the 500 separation.
- `DK-9.8.lehmann-best-lower-bounds` — **external-result** — The best lower bounds deducible from the stated 2+1 data are the two lower eigenvalues of the displayed 3x3 matrix.
- `DK-9.8.lower-bound-asymptotic` — **external-result** — The source records the strict inequality and O(epsilon^4) asymptotic for alpha_hat-alpha_check. **[restored in PDF re-audit]**
- `DK-9.8.angle-meaning-distinction` — **assertion** — phi_k are individual trial-vector-to-subspace angles whereas theta1 is the largest subspace angle.
- `DK-9.8.sine-square-sum-identity` — **identity** — sin^2 phi1+sin^2 phi2 = sin^2 theta1+sin^2 theta2.
- `DK-9.8.direct-one-vector-sharper-bounds` — **consequence** — Theorem 6.3 applied to each trial vector gives the displayed sharper tan phi_k bounds.
- `DK-9.8.methods-complementary` — **assertion** — The source concludes the two methods are complementary rather than one supplanting the other.
- `DK-9.8.eq-9-8` — **numbered-equation** — Exact mathematical content of source equation (9.8) as reconstructed in the distributable TeX.
### `DK-9-infinite-residual-counterexample`

- `DK-9-infinite-residual-counterexample.l2-geometric-vector-example` — **counterexample** — The geometric sequence e and diagonal operator give a trial vector just outside the operator domain.
- `DK-9-infinite-residual-counterexample.arbitrarily-small-domain-repair` — **assertion** — The source asserts an arbitrarily small modification repairs the domain defect.
- `DK-9-infinite-residual-counterexample.rayleigh-quotient` — **identity** — The formal Rayleigh quotient is 1+mu.
- `DK-9-infinite-residual-counterexample.residual-infinite` — **counterexample** — The residual has infinite norm so the paper residual theorems give no estimate.
- `DK-9-infinite-residual-counterexample.weinberger-still-applies` — **consequence** — Independent lower eigenvalue bounds still allow the displayed Weinberger estimate.
- `DK-9-infinite-residual-counterexample.best-lower-bound-result` — **consequence** — At the best lower bounds the true sin theta=mu satisfies mu<=mu/sqrt(1-mu).
### `DK-9.9-9.11`

- `DK-9.9-9.11.angle-factorization` — **identity** — cos omega_k=cos eta_k cos psi_k and omega_k^2<=psi_k^2+eta_k^2.
- `DK-9.9-9.11.schur-correction-bound` — **assertion** — The Schur correction is bounded by the displayed off-diagonal 2x2 matrix and operator inequalities.
- `DK-9.9-9.11.tan2-psi-bound` — **consequence** — The tan2 theorem yields the displayed bound for psi_k.
- `DK-9.9-9.11.acute-psi-selection` — **consequence** — Theorem 8.1 selects 0<=psi_k<pi/4 and yields the stated arctan bound.
- `DK-9.9-9.11.eta-bound` — **consequence** — Equation (9.10) yields the displayed tan eta_k bound.
- `DK-9.9-9.11.final-omega-bounds` — **consequence** — Combining psi_k and eta_k yields the two final omega_k bounds.
- `DK-9.9-9.11.best-possible-3x3-claim` — **source-assertion** — The source says the best possible bound from the stated data is the coordinate/eigenvector angle of the 3x3 comparison matrix.
- `DK-9.9-9.11.best-possible-proof-deferred` — **knowledge-state** — Proof of that best-possible assertion is deferred to the unresolved three-way-subspace Question 10.2. **[non-completion source state]**
- `DK-9.9-9.11.eq-9-9` — **numbered-equation** — Exact mathematical content of source equation (9.9) as reconstructed in the distributable TeX.
- `DK-9.9-9.11.eq-9-10` — **numbered-equation** — Exact mathematical content of source equation (9.10) as reconstructed in the distributable TeX.
- `DK-9.9-9.11.eq-9-11` — **numbered-equation** — Exact mathematical content of source equation (9.11) as reconstructed in the distributable TeX.
### `DK-10.1`

- `DK-10.1.question` — **open-question** — With only pairwise spectral distance delta, how sharply can Theta0 be bounded in terms of R? **[non-completion source state]**
### `DK-10.2`

- `DK-10.2.three-way-setup` — **definition** — Three-way orthogonal decompositions are encoded by the 3x3 block matrix E_i*F_j.
- `DK-10.2.question` — **open-question** — Can nearby reducing three-way decompositions be estimated through off-diagonal blocks analogously to the two-way theory? **[non-completion source state]**
### `DK-10.3`

- `DK-10.3.question` — **open-question** — Find best possible bounds combining eigenvalue and eigenvector changes. **[non-completion source state]**
### `DK-10.4`

- `DK-10.4.spectral-functional-calculus` — **definition** — The source recalls f(A) from the spectral resolution of self-adjoint A.
- `DK-10.4.step-function-specialization` — **construction** — For the gap step function under tan2 hypotheses, f(A)=P, f(A+H)=Q, f(A0)=I.
- `DK-10.4.ambient-functional-change` — **identity** — ||f(A+H)-f(A)||=||Q-P||=||sin Theta||.
- `DK-10.4.ambient-tan2-bound` — **theorem** — delta||tan 2Theta||<=2||H||.
- `DK-10.4.directed-functional-change` — **identity** — ||(f(A+H)-f(A))E0||=||Qperp E0||=||sin Theta0||.
- `DK-10.4.directed-tan2-bound` — **theorem** — delta||tan 2Theta0||<=2||R||.
- `DK-10.4.question` — **open-question** — Seek analogous perturbation bounds for more general functions f. **[non-completion source state]**
