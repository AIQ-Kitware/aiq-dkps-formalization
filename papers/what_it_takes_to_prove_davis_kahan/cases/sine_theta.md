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
