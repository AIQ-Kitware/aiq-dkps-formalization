# Rectangular Schatten compiler handoff — rebased on 48b436e

## Exact base

This candidate batch is rebased on the user-supplied archive at

`48b436e512f535cb360958945b52a8aca3c76b20`

The archive had a clean detached working tree with `main`, `origin/main`, and
`origin/HEAD` at that commit.  The Stage 1 compiler repairs are present.  The
new Schatten payload does not modify any of the seven files changed by commit
`48b436e`; the only shared integration surface is `ForMathlib.lean`, where the
new imports were merged while retaining both
`SelfAdjointFunctionalCalculus` and `MoorePenroseInverse`.

## Response to the Stage 1 compiler report

The functional-calculus and Moore--Penrose repairs preserve the intended
mathematics.  In particular, retaining the explicit symmetry witness and the
one-sided identity `A⁺ A = I` under injectivity is correct; no `A A⁺ = I`
claim should be added without surjectivity.

The repaired proof of `principalAngles_orthogonal` is also mathematically the
right route.  The equal-rank hypothesis is essential because it controls the
directed defect multiplicities.  Passing to the adjoint complementary cross
block and then using `principalSines_comm` is preferable to inventing the
missing historical lemma.

The coordinate-angle definition repairs need a mathematical warning before
module 14 is attempted:

* Postcomposing the ambient map `S C⁺ : E → E` with `X : F → E` makes
  `tanThetaEmbedding` type-correct, but it does not generally preserve the
  tangent singular values.  On a principal line it gives a sine factor rather
  than a tangent factor.
* Likewise, `(2 S C⋆) X` has coefficient `2 sin θ cos² θ` on a principal
  coordinate, not `sin (2 θ) = 2 sin θ cos θ`.
* The proposed `(C C⋆ - S S⋆) X` is therefore not a matching coordinate
  `cos (2Θ)` companion.  A canonical trial-coordinate cosine is instead
  obtained from `C⋆ C - S⋆ S` on `F` and then, if an `F → E` target is truly
  required, postcomposing that `F → F` operator with `X`.  A canonical
  trial-coordinate sine requires the positive square root `|C| = (C⋆ C)¹ᐟ²`,
  for example `2 S |C|`; the ambient exact map remains `2 S C⋆`.

Consequently, do not use the current `tanThetaEmbedding`,
`sinTwoThetaEmbedding`, `cosTwoThetaEmbedding`, or `tanTwoThetaEmbedding` as
singular-value-identifying definitions in `DoubleAngle/TanTheta.lean` yet.
They are type-correct placeholders after `48b436e`, but their intended angle
semantics require a separate redesign.  The immediate rectangular Schatten
batch below is independent of them.

There are also two straightforward module-14 API issues already visible:

* `FiniteDimensional.cosTwoThetaEmbedding` is a namespace error; the current
  declaration is `DavisKahanTheory.cosTwoThetaEmbedding`.
* `moorePenroseInverse_eq_inverse_of_injective` does not exist.  The repaired
  Stage 1 API exposes `moorePenroseInverse_eq_inverseOnRange` and
  `inverseOnRange_eq_moorePenroseInverse`.

Do not paper over those errors until the embedding semantics are corrected.

## Scope of this batch

This batch implements one coherent finite-dimensional rectangular norm stack:

1. finite real `ℓᵖ` and `ℓ∞` gauges;
2. canonical decreasing nonnegative weak majorization;
3. finite symmetric-gauge monotonicity via a T-transform descent;
4. finite Minkowski inequalities;
5. rectangular Ky Fan prefix bridges;
6. singular-value weak majorization for sums;
7. rectangular Schatten norms for every real `p ≥ 1`;
8. definiteness, homogeneity, triangle inequality, adjoint and unitary
   invariance, supported ideal inequalities, and `S₁`/`S₂`/`S∞` bridges;
9. preservation of the historical experimental `schatten`, `mem_schatten`,
   and `ofSquareFamily` declarations.

No coordinatewise singular-value subadditivity is asserted.  The sum theorem
is correctly stated as Ky Fan partial-sum subadditivity and weak majorization.

This is the finite-dimensional batch.  It does **not** repair
`DavisKahan/Experimental/InfiniteDimensional/Ideals/Rectangular.lean`.  The
missing `HilbertSchmidt`, `SchattenClass`, and `TraceClass` types reported there
belong to a separate infinite-dimensional operator-ideal architecture.  Do
not redirect this compiler pass to that file.

## Files in the batch

### New production modules

* `ForMathlib/Analysis/Normed/FiniteLpGauge.lean`
* `ForMathlib/Analysis/InnerProductSpace/SchattenNorm.lean`

### Updated production aggregate

* `ForMathlib.lean`

### Updated guarded compatibility module

* `DavisKahan/Experimental/FiniteDimensional/Norms/Rectangular.lean`

## Existing APIs reused

The implementation extends the accepted rectangular UI-norm architecture
rather than creating a parallel matrix theory.  It reuses:

* `LinearMap.singularValues`, antitonicity, nonnegativity, rank cutoff,
  adjoint equality, scalar invariance, and unitary invariance;
* `rectangularKyFanSum` and the existing rectangular `kyFan` seminorm;
* `RectangularUnitarilyInvariantNorm`, including Fan dominance and its
  endomorphism-factor ideal inequalities;
* the existing rectangular `nuclear`, `frobenius`, and `opNorm` families;
* Mathlib's finite real Minkowski theorem;
* the same finite T-transform descent principle used by Fan dominance.

## Canonical choices

### Dimension convention

The intrinsic singular-value vector is indexed by

`Fin (min (finrank 𝕜 E) (finrank 𝕜 F))`.

This is symmetric under adjoints and omits only the forced zero tail.  Explicit
lemmas bridge it to the domain-indexed sums used by the current Frobenius API.

### Weak majorization

`FiniteVector.WeaklyMajorized x y` stores canonical representatives: both
vectors are antitone and nonnegative and every prefix sum of `x` is bounded by
the corresponding prefix sum of `y`.  Singular values already use this order,
so this batch deliberately does not introduce a second sorting implementation.

### Exponents

Finite Schatten norms use a real exponent `p` with `1 ≤ p`, matching the
historical guarded signature and the available finite Minkowski API.
`S∞` is represented separately as the existing rectangular operator norm.

## Main declarations

### Finite-vector layer

* `FiniteVector.prefixSum`
* `FiniteVector.WeaklyMajorized`
* `WeaklyMajorized.refl`, `.trans`, `.of_pointwise`, `.add`,
  `.nonneg_smul`, `.sum_le`, `.zeroPadRight`
* `FiniteSymmetricGauge`
* `FiniteSymmetricGauge.le_of_prefixSum_le`
* `FiniteSymmetricGauge.mono_weaklyMajorized`
* `FiniteVector.lpGauge`
* `FiniteVector.lpGauge_add_le`
* `FiniteVector.lpGauge_mono_weaklyMajorized`
* `FiniteVector.lpGauge_zeroPadRight`
* `FiniteVector.linftyGauge`
* `FiniteVector.linftyGauge_add_le`
* `FiniteVector.linftyGauge_mono_weaklyMajorized`
* `FiniteVector.linftyGauge_zeroPadRight`

### Rectangular layer

* `RectangularUnitarilyInvariantNorm.singularValueVector`
* `prefixSum_singularValueVector`
* `singularValueVector_weaklyMajorized_iff`
* public `rectangularKyFanSum_add_le`
* `singularValueVector_add_weaklyMajorized`
* compatibility spelling `singularValues_add_weaklyMajorized`
* `schattenNorm`
* `schattenNorm_eq_zero_iff`
* `schattenNorm_adjoint`
* left, right, and two-sided supported ideal inequalities
* `schattenNorm_one_apply`
* `schattenNorm_two_apply`
* `schattenNormInf`

## Proof architecture

The Schatten triangle inequality is the composition of:

1. the existing rectangular Ky Fan triangle inequality;
2. conversion of all Ky Fan inequalities into
   `s(A+B) ≺w s(A)+s(B)`;
3. finite symmetric-gauge monotonicity under weak majorization;
4. finite Minkowski for the `ℓᵖ` gauge.

The monotonicity proof is a complete finite descent.  Each step transfers mass
between two coordinates by averaging with a transposition, preserves all
prefix inequalities, strictly reduces the disagreement count, and cannot
increase a signed-permutation-invariant sublinear gauge.

## Compiler order

Compile only the dependency chain first:

```text
lake env lean ForMathlib/Analysis/Normed/FiniteLpGauge.lean
lake env lean ForMathlib/Analysis/InnerProductSpace/SchattenNorm.lean
lake env lean DavisKahan/Experimental/FiniteDimensional/Norms/Rectangular.lean
```

Do not start with the root import.  Repair the leaf fully before moving to the
next file.

Likely elaboration hotspots:

1. exact names and argument order for `Real.Lp_add_le` and real `rpow` lemmas;
2. `Finset.sum_update_of_mem`, `Fin.sum_univ_add`, and dependent `Fin`
   coercions in the T-transform and zero-padding proofs;
3. finite `iSup` signatures in the `linftyGauge` endpoint;
4. rank-tail `Finset.sum_subset` arguments;
5. exact singular-value adjoint/rank-cutoff theorem orientations;
6. simplifier normal forms in the `S₁` and `S₂` bridges;
7. definitional unfolding in the guarded `mem_schatten` wrapper.

Repair API names, coercions, imports, and tactic details without weakening the
theorem statements or replacing weak majorization with a false pointwise
singular-value inequality.  If the T-transform descent contains a genuine
mathematical defect, report the smallest failing statement and counterexample
rather than bypassing it.

## Validation already performed after rebasing

Successful in the math-ahead environment:

* `python3 scripts/check_full_part_iii_math_ahead.py --static-only`
  reports all 174 guarded signatures preserved and no unfinished executable
  proof terms outside Challenge;
* `python3 scripts/generate_all_aggregates.py --check`;
* `python3 scripts/inventory_davis_kahan_debt.py --json`, still exactly 18
  intentional challenge occurrences;
* `git diff --check`.

Lean is not installed in this environment, so none of the new declarations is
compiler-certified here.

## Full validation after the focused files compile

Run sequentially:

```text
python3 scripts/check_full_part_iii_math_ahead.py --static-only
python3 scripts/check_full_part_iii_math_ahead.py
python3 scripts/generate_all_aggregates.py --check
lake build
lake build DavisKahan.All
lake build DavisKahan.Experimental
python3 scripts/audit_full_paper_sine_theta.py
python3 scripts/inventory_davis_kahan_debt.py --json
python3 scripts/check_library_structure.py
lake env lean DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean
lake env lean DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean
lake env lean DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean
```

The immutable targets remain 43 clean Section 6 endpoints, the three
independent Hilbert--Schmidt checks, unchanged guarded signatures, and only the
18 intentional challenge placeholders.  Criterion 3 of the structural checker
may remain inherited-red because the restored Experimental candidates have not
all been compiler-certified; do not weaken the checker to hide that state.
