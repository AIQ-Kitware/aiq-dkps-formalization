# Davis--Kahan 1970 missing-statements math-ahead plan

Base: `7463ca25c64a46c48411a2769b47714889974a97`.

This plan is derived from a line-by-line comparison of the distributable
source distillation with the maintained modernized transcription. The private
transcription is a comparison source only; it is not included in this
repository or in the overlay.

The machine-readable authority is
`dev/davis-kahan-1970-full-source-census.json`. Its generated Markdown view is
`dev/davis-kahan-1970-full-source-census.md`.

## What the current compiler campaign covers

The concurrent full-Part-III repair campaign addresses declarations already
present in `DavisKahan.Experimental.PartIII`: direct rotation, the general
Sylvester engine, tangent and double-angle theory, continuation, spectral
selection and repulsion, and finite sharpness. Successful compilation and
promotion will move many census rows from `candidate_under_repair` to a
compiled status.

That campaign does not by itself prove that every source item was ever stated.
This census identifies source statements that are absent, only partially
represented, or represented only by a narrower specialization.

## Definite mathematical gaps not covered by alias repair

### 1. Section 3 nonacute direct rotations

Proposition 3.2 gives the exact existence criterion outside the acute case:
the two crossed intersections must have equal dimension, and the resulting
direct rotation is not unique. No matching general Hilbert-space declaration
was found.

The theorem should be designed conservatively. In finite dimensions it is a
natural-number dimension equality. In infinite dimensions the source means
Hilbert-space dimension/cardinality. Do not silently replace it by finite
rank, separability plus equal finite dimensions, or an acute hypothesis.

### 2. Section 3 classification of two subspaces

Theorem 3.1 classifies dimension-compatible pairs of subspaces by spectral
multiplicity functions of the two angle operators. Corollary 3.1 specializes
this to compact cross-projection, where decreasing angle eigenvalue lists and
zero multiplicities classify the pair.

These are not present. They require a genuine Halmos-style canonical
decomposition or a bridge to the corresponding Spectra theory. They should not
be faked by proving only that principal angles are invariant.

### 3. Proposition 3.5 maximal angle eigenspaces

The repository contains much of the commutation algebra, but not the source's
maximality characterization: in the acute case, each angle eigenspace is the
unique maximal subspace reducing both projections on which all nonzero vectors
make the fixed angle with the opposite subspace.

This is independently useful and should be retained even if it is not needed
for the four headline inequalities.

### 4. Theorem 5.1 in exact Banach-space form

The source theorem is not a self-adjoint spectral theorem. It is a Banach-space
geometric-series estimate from `norm B <= alpha` and
`norm (A inverse) <= 1 / (alpha + delta)`. The repository has stronger and more
specialized Sylvester engines, but no source-audited theorem with this exact
statement was found.

This is small, general, and independently useful. It should receive an exact
source wrapper and proof rather than being subsumed silently by a Hilbert-space
gap theorem.

### 5. Lemma 6.3

The appendix's finite-rank near-maximizer lemma controls the trace norm of an
off-block component from near saturation of a Ky Fan square sum. The modern
approximation-number infrastructure is sufficient to state it, but no exact
source declaration was found.

This is likely useful beyond the paper as a quantitative finite-rank leakage
lemma. It should not be removed.

### 6. Section 9 numerical example

**Superseded in part.** Batches 9A--9E below are now formalized:
`DavisKahan/Sources/DavisKahan1970/Section9/` holds ten modules that compile in
the default build, covering the affine-moment calculations, exact radical
arithmetic, the Schur-complement reduction, the truncation repair for the
domain example, the Weinberger comparison algebra, and all decimal corollaries.

What remains is not compilation but discharge. Every source conclusion is
stated relative to `FreeBeamFiniteDataCertificate` (`Section9/ExactData.lean`)
or `TheoremOutputCertificate` (`Section9/FullExample.lean`), and no value of
either type is ever constructed, so the certificate fields -- which are the
paper's numerical claims -- are assumed rather than derived. Closing this needs
the analytic model: the free-beam closed fourth-derivative operator on
`L2(0,1)` and the bound `alpha_3 > 500`. The remaining fields are then
instantiations of theorems the repository already proves.

The original split is kept below because it still describes the intended
decomposition.

#### Batch 9A: exact finite data

Formalize the two trial functions only through the exact inner products needed
for the paper, or provide a separately proved analytic module for them. Derive
exactly:

- the residual Gram matrix;
- its two eigenvalues;
- the Rayleigh--Ritz matrix;
- the orthogonal-residual Gram matrix;
- its operator and two-singular-value norms.

The decimal constants should be corollaries of exact radical inequalities, not
primary theorem statements.

#### Batch 9B: theorem instantiations

Instantiate the compiled sine, tangent, sine-double-angle and tangent-double-
angle theorems to derive equations (9.1)--(9.7).

#### Batch 9C: Weinberger comparison

Separate the historical comparison from the DK formalization. The exact 3x3
comparison-matrix eigenvalue inequalities may be formalized. The asymptotic
`O(epsilon^4)` statement should not be introduced until its intended analytic
meaning is specified.

#### Batch 9D: domain-limitation example

The paper deliberately displays a vector outside the perturbed operator's
domain and says an arbitrarily small modification fixes the issue. Formalize a
specific modified vector with the claimed behavior; do not state a theorem
about an undefined residual.

#### Batch 9E: individual eigenvectors inside a cluster

Formalize the Schur-complement reduction (9.9)--(9.11), then the combination of
tangent and double-angle estimates giving the final individual-eigenvector
bounds.

The initial implementation can be a finite block-operator theorem independent
of the fourth-derivative operator. The analytic model can instantiate it later.

## Source wrappers likely missing after the current campaign

Even if the underlying declarations compile, the following source statements
need exact wrappers and audits:

- Proposition 3.1's characterization by positivity, not only existence and
  uniqueness;
- Proposition 3.3's converse principal-square-root statement with the crossed-
  intersection mapping condition;
- Proposition 3.4's exact `Q_minus` to `Q` interpretation;
- Proposition 4.1's pointwise singular-value extremality, which is stronger
  than one operator-norm minimality theorem;
- Corollary 4.1 without accidentally importing Proposition 4.4's `pi / 3`
  restriction;

  (Proposition 4.4 itself is no longer a target. As printed it is **false**:
  `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean`
  refutes it over the reals in its own "every unitarily invariant norm" form,
  and no angle threshold repairs it. The repair that *is* true for every
  Q-norm, with neither the `pi / 3` hypothesis nor the real-space restriction,
  is `directRotation_fullDisplacement_qnorm` in
  `DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean`. Do not reintroduce
  the printed statement as an obligation.)
- Proposition 4.2 in the source infinite-series scope;
- Theorem 5.2 as a numbered source theorem;
- Theorem 6.3 in general Hilbert-space scope;
- Theorems 8.1(i)--(iii) as three explicit conclusions tied to the canonical
  selected subspace;
- Theorem 8.2 with both smallness alternatives exactly as printed.

## What is not proof debt

Questions 10.2--10.4 are research questions, not missing theorems. They belong
in the source census and roadmap but are not completion obligations.

Question 10.1 is subtler: the repository resolves the pairwise-gap square-norm
case through Theorem 6.2. It should record exactly which additional source norm
classes are now known and should not claim that the paper's broad question is
fully resolved without a norm-by-norm statement.

## Parallel work while the compiler agent repairs Part III

The following work is documentation or new-module work and can proceed without
editing the agent's active files:

1. review the 48-row census against the private transcription;
2. design exact Lean signatures for Proposition 3.2, Theorem 3.1, Corollary
   3.1, Proposition 3.5, Theorem 5.1 and Lemma 6.3;
3. build a Section 9 finite-data specification with exact constants;
4. convert the source audit to consume the census manifest after the candidate
   proofs have settled;
5. prepare Tau Ceti roadmap milestones from the true source gaps rather than
   from file layout.

## Acceptance for the next source-census pass

Run:

```bash
python3 scripts/render_davis_kahan_1970_source_census.py --check
python3 scripts/check_davis_kahan_1970_source_census.py
python3 scripts/check_distilled_literature_index.py
```

After the compile agent returns, update statuses and Lean references, then add
compiler/dependency evidence to every row promoted to `compiled_exact`.
