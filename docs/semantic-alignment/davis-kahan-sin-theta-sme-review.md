# Davis–Kahan 1970 sin-θ theorem: SME review candidate

**Status:** The previous candidate elaborated on the user's machine. This revision expands the separation hypothesis directly in the theorem statement, retaining the explicit named proof fields; it has not been separately compiled here. Mathematical-scope review requested; do **not** certify source equivalence or successful Lean compilation on the basis of this packet alone. This packet concerns the **sin-θ theorem only**, not the separate tan-θ, sin-2θ and tan-2θ theorems.

**Lean statement:** `DavisKahan/Sources/DavisKahan1970/SineTheta/ExplicitSeparationPresentation.lean`

**Primary source:** Chandler Davis and W. M. Kahan, “The Rotation of Eigenvectors by a Perturbation. III,” *SIAM Journal on Numerical Analysis* **7** (1970), 1–46, DOI [10.1137/0707001](https://doi.org/10.1137/0707001). Compare Section 1 (notation and angle), the first theorem in Section 2, and the unbounded-operator Appendix to Section 6. The checked-in reconstruction is `prose/distilled_literature/DavisKahan1970_part_III.tex`, claims `S1-block-residual`, `S1-ui-norms`, `S2-sin-theta`, `S2-unbounded-scope` and `DK-6-appendix`.

## Mathematical statement submitted for review

Let $\mathcal H$ be a separable real or complex Hilbert space; no finite-dimensionality is assumed. Let $T$ be a **possibly unbounded self-adjoint operator** on $\mathcal H$. We write $T$, rather than $A+H$, for the paper's perturbed operator. Let $\mathcal F,\mathcal G,\mathcal K$ be Hilbert coordinate spaces and let

$$
E_0:\mathcal F\to\mathcal H,\quad
F_0:\mathcal K\to\mathcal H,\quad
F_1:\mathcal G\to\mathcal H
$$

be linear isometries. Assume that $\operatorname{ran} F_0$ and $\operatorname{ran} F_1$ are mutually orthogonal and span $\mathcal H$. The desired exact subspace is $\operatorname{ran}F_0$; its orthogonal complement is $\operatorname{ran}F_1$. The trial subspace is $\operatorname{ran}E_0$.

Let $A_0$ and $\Lambda_1$ be **possibly unbounded self-adjoint** operators on $\mathcal F$ and $\mathcal G$, respectively. Let $R:\mathcal F\to\mathcal H$ be bounded. Assume the following relations on their specified domains:

$$
\begin{aligned}
&E_0\operatorname{dom}(A_0)\subseteq \operatorname{dom}(T),
&& T E_0 x-E_0A_0x=Rx&& (x\in\operatorname{dom}(A_0)),\\
&F_1\operatorname{dom}(\Lambda_1)\subseteq \operatorname{dom}(T),
&& T F_1y=F_1\Lambda_1y&& (y\in\operatorname{dom}(\Lambda_1)).
\end{aligned}
$$

Thus $R$ is the **bounded extension of the residual**, and $\Lambda_1$ describes the exact complementary spectral block. Let $\delta>0$. Assume at least one of these three separation cases:

1. **Interval/exterior (either orientation).** There are $\beta\le\alpha$ such that $\operatorname{spec}(A_0)\subseteq[\beta,\alpha]$ and $\operatorname{spec}(\Lambda_1)\cap(\beta-\delta,\alpha+\delta)=\varnothing$, **or** the same condition with $A_0$ and $\Lambda_1$ interchanged.
2. **Trial above complement.** For some $c\in\mathbb R$, $\langle A_0x,x\rangle\ge(c+\delta)\|x\|^2$ for all $x\in\operatorname{dom}(A_0)$, and $\langle\Lambda_1 y,y\rangle\le c\|y\|^2$ for all $y\in\operatorname{dom}(\Lambda_1)$.
3. **Trial below complement.** For some $c\in\mathbb R$, $\langle A_0x,x\rangle\le c\|x\|^2$ for all $x\in\operatorname{dom}(A_0)$, and $\langle\Lambda_1y,y\rangle\ge(c+\delta)\|y\|^2$ for all $y\in\operatorname{dom}(\Lambda_1)$.

For complex Hilbert spaces the quadratic-form expressions above are real because the operators are self-adjoint. Cases 2 and 3 are the quadratic-form versions of the corresponding **spectral half-line containments**. They extend the finite-interval Section 2 formulation into the broader unbounded treatment.

The paper's directed angle on trial coordinates can be written using the positive cosine overlap as

$$
\Theta_0=\arccos \bigl|F_0^*E_0\bigr|,
\quad\text{where}\quad |B|=(B^*B)^{1/2},
\quad0\le\Theta_0\le\pi/2.
$$

**Claim:** For every normalized unitarily invariant norm $\|\cdot\|_\Phi$ of the relevant operators **whenever both displayed norms exist**,

$$
\boxed{\delta\,\|\sin\Theta_0\|_\Phi\;\le\;\|R\|_\Phi.}
$$

The factor is one. This inequality is the object under review; optimality of that factor is a separate source claim and is not proved by the displayed implication alone.

## Relation to the Lean theorem

The companion `DavisKahan/Sources/DavisKahan1970/SineTheta/ExplicitSeparationPresentation.lean` exposes every domain relation and both orthogonal-coordinate conditions. **Its public theorem statement does not mention `FormBoundedSylvesterGap` or `RealSpectrumIntervalExteriorGap`.** Instead `hseparation` spells out the three alternatives: interval/exterior in either orientation using `TauCeti.LinearPMap.realSpectrum` and `Set.Icc`, and the two ordered cases using `TauCeti.LinearPMap.SemiboundedBelow`/`SemiboundedAbove`. The two orientations in the first alternative are explicitly displayed. There is no presentation-specific gap predicate to look up.

In the **proof only**, `formGap` converts these hypotheses into `FormBoundedSylvesterGap` by matching each alternative with its existing constructor. For the interval/exterior branch, Lean unfolds the existing `RealSpectrumIntervalExteriorGap` definition when checking the constructor. This is a conversion of the same conditions, not a strengthening or weakening; the proof then applies `TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_whereDefinedUIN_rclike`.

The file **does not define the sine as an arbitrary projection block**: its conclusion names `sourceDirectedSinThetaOperator E₀ F₀`. That object is defined as `cfc Real.sin (sourceDirectedThetaOperator E₀ F₀)` in `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`, and a bridge theorem identifies it with the positive modulus of `(I-F₀F₀*)E₀`.

The source defines the directed angle through the **positive cosine overlap**, whereas the current generic Lean operator is reconstructed using `arcsin` of the **positive sine modulus**. The repository's `DavisKahan/Sources/DavisKahan1970/SineTheta/AngleIdentity.lean` proves the corresponding cosine/sine angle identification for canonical subspace coordinates. **The SME should examine whether this evidence establishes the intended identification in the arbitrary coordinate setup of the headline wrapper**, not merely equality of norms.

The normalized norm record is `NormalizedSymmetricOperatorIdealFamily`. Its laws include the rank-one normalization, symmetric-operator-ideal properties and a **where-defined Ky Fan dominance comparison**. The statement quantifies over every instance of this record, but a claim of “every unitarily invariant norm as defined in 1970” additionally requires either a class equivalence/coverage proof or mathematical agreement that this record introduces no unwanted restriction. *Absence of a particular named Schatten norm in the theorem signature is not an issue; coverage of the entire intended abstract class is.*

The displayed alternatives preserve the scalar-generic form-bounded separation used by the previously compiling theorem, while exposing it instead of naming it. The separate fully spectral `SpectralSylvesterGap` in `DavisKahan/Sylvester/Unbounded/AllGap.lean` is complex-only, so replacing the generic hypothesis with it would narrow the advertised scalar scope. As proved in `Sylvester/Unbounded/FormBoundedGap.lean`, the complex spectral condition implies the form-bounded one; the library does **not** provide the full converse for the two ordered cases. Mathematically, the self-adjoint spectral theorem identifies the formulations, but source fidelity must not be inferred from an unproved Lean equivalence.

The Lean setup uses only the perturbed operator $T$ and a residual $R$. The paper sets up $A$, $A+H$ and their reducing subspaces. A reader should explicitly check that this compressed residual formulation has **no extra hidden assumption** relative to the 1970 sin-θ conclusion and its domain provisions. The Lean hypothesis on `F₁` is a self-adjoint intertwining relation; the claimed exact-block interpretation should also be checked at the **domain** level (not merely on a dense proper subdomain). The Appendix also uses a **common dense domain** for the two terms in the residual; check whether the one-way domain-inclusion hypothesis in the Lean signature suffices for an exact match.

### Why the proof is now readable

The Lean proof packages the explicitly displayed hypotheses into the established `IsTrialResidual` and `IsExactSpectralDecomposition` structures **using their named fields** (`isometry`, `mapsDomain`, `residualEquation`; and `desiredIsometry`, `complementIsometry`, `orthogonal`, `complete`, `mapsDomain`, `intertwines`). These are not new assumptions: each field is filled with a theorem parameter already present in the statement. A short proof-only case split converts the three displayed gap alternatives to the existing inductive constructors; the final line passes that constructed fact to the proved `sinTheta_unbounded_formGap_whereDefinedUIN_rclike`.


## TauCeti upstream reconciliation (October 20, 2026)

TauCeti main now includes `LinearPMap.realSpectrum` and `LinearPMap.SpectralSetsSeparated` in
`TauCeti/Analysis/InnerProductSpace/LinearPMap/SpectralSeparation.lean`, merged in
[TauCeti PR #18918](https://github.com/TauCetiProject/TauCeti/pull/18918). These are reusable
primitives, but `SpectralSetsSeparated A B Set.univ Set.univ delta` alone does **not**
express the three configurations needed here: disjoint interlaced real spectral sets can
have positive pairwise distance without satisfying the interval/exterior or ordered cases.

The migration to the canonical spectrum is now staged across the full
sine-theta proof path. `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean`
no longer defines a duplicate real spectrum. Instead it proves a real/complex
scalar-generic equivalence between the remaining *legacy* `A - λ` inverse and
the accepted `λ I - A` resolvent; the inverses differ by a sign. The visible
separation conditions use the official upstream real-spectrum definition.
The complex spectral branch of the Sylvester engine likewise uses the accepted
`_root_.LinearPMap.spectrum`. See
`dev/tauceti/proof-lineage/2026-10-20-canonical-spectrum-migration.md` for the
historical revision anchors, exact equivalence, and outstanding compile repair
instructions. The worktree was statically checked; the migration changes still
require their Lean build on the maintainer's machine.

`TauCeti.LinearPMap.SemiboundedBelow`/`SemiboundedAbove` currently come from the DKPS
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean` file, not the upstream
TauCeti `LinearPMap/Sylvester.lean` module on main. A useful upstream step is to port the
generic semibounded predicates and equivalence lemmas and a reusable real-spectrum
interval/exterior predicate (or set geometry), then preserve the **three-case** inductive
`FormBoundedSylvesterGap` for the source-facing theorem. Replacing it merely by generic
pairwise spectral separation would change the mathematical claim.

## Questions for an independent reviewer

1. **Hypotheses:** Are the isometric coordinates, self-adjointness and two domain-aware equations a faithful mathematical formulation of the 1970 sine theorem? Is anything stronger than the paper being assumed, or anything essential missing?
2. **Gap:** Do the interval/exterior alternatives match the **printed Section 2** theorem? Do the two ordered form-gap cases faithfully realize the **unbounded Appendix to Section 6** without dropping a domain assumption?
3. **Angles:** Is the `sourceDirectedThetaOperator` / `sourceDirectedSinThetaOperator` expression actually the paper's positive angle $\Theta_0$ / $\sin\Theta_0$, including zero and right-angle components and infinite-dimensional cases? Should the code instead construct the cosine-defined operator $\arccos |F_0^*E_0|$ directly?
4. **Norms:** Does `NormalizedSymmetricOperatorIdealFamily` cover **every normalized unitarily invariant norm** intended by Davis–Kahan, or does its Ky Fan comparison field narrow the quantifier? Is the `N.Mem` conjunction exactly the paper's “where the norms exist” convention?
5. **Completeness claim:** Is the numerical bound at sharp factor one the entire **sin-θ theorem**, as opposed to the other three Section 2 theorems or separate sharpness claims?

## Local validation commands

From `~/code/aiq-dkps-formalization`, build the source-facing module directly:

```bash
lake exe cache get
lake build DavisKahan.Sources.DavisKahan1970.SineTheta.ExplicitSeparationPresentation
```

The file lives in the production source tree and is imported by
`DavisKahan/Sources/DavisKahan1970/All.lean`, so the project aggregate also checks it.
The public declaration is
`TauCeti.DavisKahan1970.sinTheta_unbounded_explicitSeparation_whereDefinedUIN_rclike`.
The former root-level `new_presentation_candidate.lean` is superseded and should
be deleted after the new module builds. Successful compilation does not prove
that the statement has exactly the scope of the historical theorem.

**Compilation status in this packet:** an earlier candidate passed `lake env lean`
on the user's machine. This moved and renamed version has not been Lean-compiled
in this environment (Lean and its dependency environment are unavailable).
The mathematical hypotheses and conclusion are unchanged from the preceding
explicit-separation version; verify the new module build before committing.
