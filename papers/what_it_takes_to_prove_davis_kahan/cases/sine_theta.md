# Case study 1: the full-scope single-angle sine theorem

## Mathematical target and existing evidence

- Original result: Davis--Kahan (1970), Section 2 single-angle sine theorem,
  supported by the Section 5 Sylvester theory and Section 6/general-case proof
  machinery; the full source conditions, including appendices, must be checked.
- Maintained source result: `S2-sin-theta` in
  `dev/davis-kahan-1970-formalization-result-inventory.json`.
- Selected formal endpoint:
  `TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_whereDefinedUIN_rclike`
  (the enclosing namespace is confirmed in the October 20 source snapshot).
- Source implementation:
  `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`.
- Existing full-scope mathematical exposition:
  `papers/dk_formalization_journal/paper.tex`, section on the single-angle
  sine-theta theorem.

The existing project reports the theorem as Lean-verified and source-reviewed.
This case study is an explanatory and dependency investigation, not an attempt
to re-prove an already completed source result.

## Proposed mathematical spine

Let $E_0$ be an isometric trial map, $A$ the ambient self-adjoint operator,
$A_0$ the trial self-adjoint operator, and $R$ the bounded extension of the
residual $AE_0-E_0A_0$ on the relevant domain. Let $F_1$ be exact coordinates
for the complementary reducing subspace, with spectral block $\Lambda_1$.
Define $X=F_1^*E_0$.

| Step | Mathematical obligation | Evidence to pin |
| --- | --- | --- |
| 1. Complementary block | $F_1^*R=\Lambda_1X-XA_0$ on the proper domain | Original source formula, Lean domain and block hypotheses |
| 2. Spectral separation | $\delta N(X)\leq N(F_1^*R)$ for each supported gap alternative | Source Section 5 and general-sine proof, exact gap predicate and norm class |
| 3. Norm contraction | $N(F_1^*R)\leq N(R)$ when both expressions belong to the ideal | Reusable ideal laws and the precise rectangular operator types |
| 4. Sine identification | $|X|=\sin\Theta_0$, or an equivalent rectangular complementary-block modulus statement | Positive source angle operator, exact orthogonal decomposition, modulus lemma |
| 5. Conclusion | $\delta N(\sin\Theta_0)\leq N(R)$ | Formal theorem and source statement; where-defined membership and scalar hypotheses |

This table is a mathematical **working decomposition**. Before publication,
check every step against the selected formal theorem, including the route
between the $F_1^*E_0$ and $(I-F_0F_0^*)E_0$ representations.

## Competing scope: what cannot be discarded

Complete these comparisons with precise source and Lean citations:

| Choice | Hypotheses to compare | Question |
| --- | --- | --- |
| Finite-dimensional / infinite-dimensional | Discrete singular values, approximation numbers, ideal membership | Which finite spectral steps survive in the infinite-dimensional formulation? |
| Bounded / unbounded | Operator domains, adjoints, strong cutoff arguments, bounded residual | Where does the finite proof cease to establish a legal operator equality? |
| Finite interval/exterior gap / ordered half-infinite gaps | Spectrum containment versus operator-form order | Which Sylvester estimate supports each case? |
| Complex / real field | Self-adjoint spectral tools and transfer infrastructure | Which results have a native real proof and which route through complexification? |
| General ideal norm / concrete Schatten or operator norm | Where-defined membership and normalized symmetric ideal families | Which norm comparisons need majorization or polar decomposition? |

## Historical source checks

The historical register starts with the original 1970 paper. For each step above,
record (1) its exact location in 1970; (2) citations made there; (3) a verified
statement/page in an earlier mathematical source where possible; (4) a later
formal abstraction if one is used; and (5) whether the claimed relationship is
explicitly cited, a mathematical antecedent, or retrospective similarity.

Specific literature candidates for the pilot:

- Sylvester's matrix equation in nineteenth-century matrix algebra. Verify
  what the original statement established before identifying it with the
  operator-theoretic proof step.
- Rosenblum's 1956 operator-equation paper,
  https://doi.org/10.1215/S0012-7094-56-02324-9, compared with the exact
  spectral-separation estimate used in this project.
- Earlier Davis eigenvector-rotation papers, particularly the 1963 installment,
  https://doi.org/10.1016/0022-247X(63)90001-5.
- Operator-ideal and singular-value inequalities actually used in the proof;
  assign historical credit from the mathematics and cited primary sources,
  not from Lean filenames.
- The formalized Spectra ancestry for the Borel calculus and unbounded
  self-adjoint infrastructure, with credit tied to precise adapted declarations.

## Evidence checklist for the pilot

- [ ] Record source PDF edition, original page/formula anchors, repository commit,
      and Lean dependency revisions.
- [ ] Pin the elaborated signature and its supporting local definitions.
- [ ] Classify each step as original-paper proof, modern equivalent
      reformulation, or implementation-specific convenience.
- [ ] Confirm domains and both directions of the modulus/rectangular bridge.
- [ ] Trace the full ordered half-infinite spectral cases, with no bounded-only
      substitution.
- [ ] Identify at least one proof alternative and state its exact loss or gain
      of generality.
- [ ] Annotate 10--20 load-bearing Lean declarations with their mathematical
      meaning and separate them from import-only or typeclass infrastructure.
- [ ] Check historical claims against the actual mathematical text and record
      competing attribution when priority is uncertain.
- [ ] Produce one original mathematical dependency diagram, independently
      readable without opening Lean.
- [ ] Obtain mathematical review of the written derivation before extending
      the case study to other results.

## First research deliverable

A mathematically self-contained explanation of the chain from a bounded
residual to the full-scope sine-theta inequality, with an aligned, clearly
qualified Lean proof trace and a page-verified historical bibliography. Its
value should survive if all implementation details are removed from the main
mathematical exposition.

## Completed source-to-mathematics pilot: the selected full-scope endpoint

**Snapshot:** 23 October 2026, uploaded Git HEAD
`2b6aa58dcd30af28a14fe7cea05d73f235d3c7bd`.
The source signature and named proof steps below were inspected directly in this
snapshot; the existing formal theorem is part of the previously verified
formalization. This is a mathematical dependency analysis, **not** a new Lean
compilation and **not** a completed historical priority proof. Precise page
attributions beyond the 1970 section and theorem numbers remain open.

### The theorem in operator terms

Let `E,F,G,H` be separable where required Hilbert-coordinate spaces over
`R` or `C` (the formal endpoint assumes separability of ambient `E`). Let
`A : E -> E`, `A0 : F -> F`, and `Lambda1 : G -> G` be possibly unbounded
self-adjoint operators. Let `E0 : F -> E` and `F0 : H -> E`, `F1 : G -> E`
be bounded isometric embeddings; their images `F0(H)` and `F1(G)` are
orthogonal and exhaust the ambient space. The residual `R : F -> E` is
**bounded**, and on the **domain of `A0`** it satisfies

```
    E0(dom A0) subset dom A,
    A(E0 x) - E0(A0 x) = R x.                            (RES)
```

The complementary block must be compatible with the ambient operator:

```
    F1(dom Lambda1) subset dom A,
    A(F1 y) = F1(Lambda1 y)  for y in dom Lambda1.    (RED)
```

Assume `delta>0` and one of the three **actual**
`FormBoundedSylvesterGap A0 Lambda1 delta` constructors listed in
`DavisKahan/Sylvester/Gap.lean`: `intervalExterior` (with an explicit
real spectral interval/exterior separation), `leftAboveRightBelow`, or
`leftBelowRightAbove` (with opposite semibounded operator forms). In
particular, the ordered alternatives permit unbounded blocks on both
sides; a finite-dimensional matrix proof of an interval/exterior gap is
not enough to cover the theorem.

Set

```
   P0 = F0 F0*,             S = (I-P0) E0 : F -> E,
   T = |S| : F -> F,        Theta0 = arcsin(T) via functional calculus.
```

The formal endpoint uses the **literal sine of the directed angle**,
`sin(Theta0) = T`, established by functional calculus for the spectrum of
`T` in `[0,1]`. If both the sine and residual belong to a normalized
symmetric operator ideal `N`, the conclusion is

```
                  delta N(sin Theta0) <= N(R).         (SINE)
```

The membership assumptions are substantive: an operator-ideal gauge need
not be finite on every bounded operator in infinite-dimensional space.

### The logical spine, with exact evidence and limits

| Stage | Mathematical assertion | Inspected formal evidence | Scope qualification |
|---|---|---|---|
| Residual | (RES) on `dom A0`; isometric `E0` | `Presentation.lean`, `IsTrialResidual`, lines 89–100; `IsTrialResidualEquation`, 111–120 | `R` bounded, while `A,A0` may be unbounded |
| Exact coordinates | (RED); `F0*F1=0`, `F0F0*+F1F1*=I` | `Presentation.lean`, `IsExactSpectralDecomposition`, lines 168–182 | Complement reducing/domain compatibility is not a merely algebraic matrix block |
| Rectangular sine | `S=(I-P0)E0`, `T=|S|`, spectrum of `T` in `[0,1]` | `sourceDirectedSineBlock`, `sourceDirectedSineModulus`, `norm_sourceDirectedSineModulus_le_one`, `spectrum_sourceDirectedSineModulus_subset_Icc` | `E0` and `F0` isometric; modulus is positive and bounded |
| Literal sine | `sin(arcsin T)=T` via continuous functional calculus | `sourceDirectedThetaOperator`, `sourceDirectedSinThetaOperator`, `sourceDirectedSinThetaOperator_eq_modulus` (line 319) | Needs spectral range `[0,1]`; not pointwise sine of an arbitrary operator |
| Analytic gap estimate | `delta N(S)<=N(R)` | `ScalarGeneric.lean`, `sinTheta_unbounded_formGap_symmetricNorming_ofComponents_rclike` (line 192); `Presentation.lean`, `sinTheta_unbounded_formGap_symmetricNorming_rclike` (413) | Depends on exact interval/exterior **or** semibounded gap; includes ideal membership |
| Arbitrary where-defined UIN | `delta N.gaugeReal(S)<=N.gaugeReal(R)` | `sinTheta_unbounded_formGap_rectangular_whereDefinedUIN_rclike` (439) | Passes through every Ky Fan gauge, then `scaledGaugeLEWhereDefined_of_all_mul_kyFan_le`; no assertion outside an ideal |
| Norm transport to positive sine | `N(T)=N(S)` and membership `S in ideal iff |S| in ideal` | `sinTheta_unbounded_formGap_whereDefinedUIN_rclike` (479–528) | Modulus invariance is a separate proof obligation for rectangular operators |

**Why a basic Sylvester equation enters.** Put
`X=F1*E0 : F -> G`, so that `S=F1 X` by completeness. In finite
dimensions, multiplying (RES) by `F1*` and using (RED) gives

```
                 Lambda1 X - X A0 = F1* R.             (SYL)
```

When `A` or `Lambda1` is unbounded, `(SYL)` requires an actual statement
that `X(dom A0)` belongs to `dom Lambda1`, or a weak Sylvester equation
whose pairings are defined on the appropriate domains. The indicated
self-adjoint/reducing hypotheses and the project's formal core address
this bridge. Simply writing `F1* A = Lambda1 F1*` as an everywhere-defined
bounded-operator identity would be invalid. The full-gap estimate for
`(SYL)` is precisely what the Section 5/Appendix spectral-separation
machinery contributes; its resulting constant-one estimate is **not**
valid for every pair of interlaced spectra having only a positive pairwise
distance.

The coisometry `F1*` contracts the residual's relevant unitarily
invariant norm and ideal gauge. The map `F1` is an isometric embedding;
`|F1X|=|X|`, so the singular data of `S=F1X` and `X` coincide. The
analytic route is therefore

```
 (RES)+(RED)+domains -> Sylvester estimate for X
  -> delta N(X) <= N(F1*R) <= N(R)
  -> |F1X| = |X| = |S| = sin Theta0
  -> (SINE) for the where-defined ideal gauge.
```

This line is **a mathematical explanation of one viable route**, not a
claim that the chosen Lean endpoint applies exactly these steps in this
syntactic order. The actual scalar-generic implementation in
`ScalarGeneric.lean` bundles an `UnboundedSinThetaData` problem and
establishes individual Ky Fan cases; the public endpoint in
`Presentation.lean` passes through `symmetricNorming_rclike`, `rectangular_whereDefinedUIN_rclike`, and the modulus bridge. A Lean
*import* of a lemma does not establish that it is a necessary mathematical
ingredient of every possible proof.

### Why there is no second ambient operator in the endpoint

The ambient `A`, trial `A0`, and isometry `E0` determine a residual. A
separate explicitly perturbed `A+H` is *one way* to obtain these objects,
not an additional datum required by the abstract sine theorem. The
mathematical conclusion depends on the **trial residual** and the
**complementary spectral gap**. A purported proof using only `A` and a
vector perturbation misses the role of the trial compression `A0`, the
isometry `E0`, and the block `Lambda1`.

### Historical relationship, and what remains unverified

Davis–Kahan (1970), Section 2 and the Section 5 Sylvester theory are the
primary source of this particular sine-theta scope; their ordered
half-infinite variants require checking against the Appendix and the
source atom inventory. Rosenblum (1956), *On the operator equation
`BX-XA=Q`*, [DOI](https://doi.org/10.1215/S0012-7094-56-02324-9), is
an earlier operator-equation predecessor; its exact ideal-gauge and
semibounded hypotheses were **not** established equivalent to the
modern `FormBoundedSylvesterGap` branches here. Davis (1963),
*The Rotation of Eigenvectors by a Perturbation. I*,
[DOI](https://doi.org/10.1016/0022-247X(63)90001-5), is an earlier
rotation-paper predecessor, with a direct source-to-source comparison
still needed. Historical influence must not be inferred merely because
we use a modern result whose subject resembles an earlier paper.

**Remaining prerequisites for a publication-level historical study:**
verify scanned 1970 Section 2/Appendix page anchors; examine Rosenblum
1956 and Davis 1963 theorem text; compare one fully extracted Lean proof
term's declarations with source-era lemmas; and obtain mathematical
review of the above operator-domain argument. The project already has
Git-history, declaration-crosswalk and source-atom machinery for these
comparisons; new generic analysis scripts are not needed.
