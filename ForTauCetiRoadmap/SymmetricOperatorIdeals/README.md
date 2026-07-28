# Roadmap: symmetric operator ideals

A **symmetric operator ideal** on Hilbert space is a rule assigning to every pair
of spaces `E`, `F` a subspace of `E →L[𝕜] F` stable under composition with
arbitrary bounded maps on either side and under adjoints, together with a norm on
that subspace dominating the operator norm and submultiplicative against outer
compositions. The Schatten classes, trace class, Hilbert--Schmidt, and the finite
Ky Fan gauges are the standard examples; each is a gauge of the sequence
`n ↦ aₙ(T)` of approximation numbers.

This roadmap is the dependent one that
[`../ApproximationNumbers/README.md`](../ApproximationNumbers/README.md)
disowns. It should not be submitted before that one settles, because every
object here is a functional of the `s`-sequence it defines.

Mathlib has `Schatten` for `p = 1, 2` on a single space via `HilbertSchmidt` and
trace-class machinery, but no *family* interface: no object over which a theorem
can be stated once for "an arbitrary symmetric ideal norm", and nothing
rectangular. That family interface is what this area contributes.

## Scope boundary

This roadmap owns:

- the operator-ideal family interface itself, and its ideal/`Elem`/completeness
  API;
- symmetric norming functions and their extension to infinite sequences;
- the finite Ky Fan gauges `∑_{n<k} aₙ` and Ky Fan dominance;
- the Calkin correspondence: symmetric gauge `Φ` ↦ ideal `S_Φ`;
- Schatten `p`, Hilbert--Schmidt, and trace class as instances of that
  correspondence, with their defining identities;
- block-sum rearrangement for ideal gauges;
- real/complex transport of operator ideals.

This roadmap does **not** own:

- approximation numbers and their elementary theory (the area above);
- unbounded operators, spectral projections, or Davis--Kahan angle theorems.

## What has already landed

Staged in `ForTauCeti/Analysis/OperatorIdeal/Family/{Basic,OperatorNorm}.lean`,
sorry-free and building, and recorded in `dev/tauceti/extraction-manifest.json`:

- `TauCeti.OperatorIdealFamily` — the gauge and its four laws, with independent
  source and target universes;
- `TauCeti.OperatorIdealFamily.{carrier, Elem, IsComplete}` — the ideal as a
  `Submodule`, as a normed space carrying the *ideal* norm, and its
  completeness;
- `TauCeti.SymmetricOperatorIdealFamily` — the adjoint-invariant diagonal layer;
- `TauCeti.operatorNormFamily` — the first instance, with the isometry
  `Elem E F ≃ₗᵢ[𝕜] (E →L[𝕜] F)` and the resulting `IsComplete` instance.

A second instance landed on 2026-07-28 in
`ForTauCeti/Analysis/OperatorIdeal/Family/HilbertSchmidt.lean`, over the energy
staged in `ForTauCeti/Analysis/InnerProductSpace/HilbertSchmidtEnergy.lean`:

- `ContinuousLinearMap.hilbertSchmidtEnergy b T = ∑' i, ‖T (b i)‖ₑ ^ 2`, with
  Parseval in `ℝ≥0∞`, the rectangular adjoint swap, and basis independence;
- `ContinuousLinearMap.hilbertSchmidtENorm`, its square root, with Minkowski at
  `p = 2` (`ENNReal.tsum_sq_add_rpow_le`, itself a staged extension of Mathlib's
  `Finset`-level `ENNReal.Lp_add_le` to `tsum`), domination of the operator
  norm, adjoint invariance and the two-sided ideal bound;
- `TauCeti.hilbertSchmidtIdealFamily` — a `SymmetricOperatorIdealFamily` whose
  carrier is exactly `ContinuousLinearMap.IsHilbertSchmidt`.

This is the instance that matters most for the interface: it is built from
orthonormal expansions and shares no machinery with `operatorNormFamily`, so
the two together are evidence that the structure is not shaped around a single
example.

A third instance landed on 2026-07-28 in
`ForTauCeti/Analysis/OperatorIdeal/Family/KyFan.lean`: `TauCeti.kyFanIdealFamily
k hk`, over the gauge staged in
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean`. It is the
instance the note below called "parked", now unparked, and it carries **no**
`HasKyFanApproximationGaugeTriangle` hypothesis: over `ℂ` that triangle
inequality is `ContinuousLinearMap.kyFanGauge_add_le`, proved outright, because
the min–max theorem it rests on no longer needs `vendor/Spectra`'s
projection-valued measures (see
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`).

The generic-scalar version below remains, `rfl`-equal to this one at `𝕜 = ℂ`;
it is still needed for real scalars, whose triangle inequality is obtained by
complexification.

The historical note follows, describing the state before that:
`DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean`:
`kyFanSymmetricIdealFamily k hk`, the `ENNReal.ofReal` transport of
`kyFanApproximationGauge k`, with a completeness instance proved from the
two-sided comparison `‖A‖ ≤ ∑_{n<k} aₙ(A) ≤ k‖A‖`. It is parked because both
`kyFanApproximationGauge` and the capability class supplying its triangle
inequality live in the Davis--Kahan library; its intended home is
`ForTauCeti/Analysis/OperatorIdeal/Family/KyFan.lean` and the note is on the
declaration.

## Pinned decisions

### One `ℝ≥0∞`-valued gauge as the sole datum

A family is presented by a *single* field

```lean
gauge : ∀ {E F} [...], (E →L[𝕜] F) → ℝ≥0∞
```

with the ideal recovered as its finiteness domain
(`OperatorIdealFamily.carrier : Submodule 𝕜 (E →L[𝕜] F)`), **not** by a
membership predicate plus an independent real gauge.

- *It is the only presentation with an extensionality theorem.* With membership
  and gauge as independent data the laws constrain the gauge only *on* members,
  so two families can agree on every ideal element and still differ off it —
  the "free data" failure mode, which makes `ext` unstatable. With one field,
  `OperatorIdealFamily.ext` is immediate.
- *It is the classical presentation.* A symmetric norming function
  (Gohberg--Krein, Calkin) is defined on everything and the ideal *is* where it
  is finite; `ℝ≥0∞` is the honest codomain of an ideal norm. This does not
  conflict with the real-valued codomain pinned for `approximationNumber`: an
  approximation number is a real number attached to a single operator, while an
  ideal gauge is genuinely `∞` off its ideal.
- *Every law becomes unconditional.* In `ℝ≥0∞` subadditivity, homogeneity
  `gauge (c • A) = ‖c‖ₑ * gauge A`, the two-sided bound
  `gauge (L ∘L A ∘L R) ≤ ‖L‖ₑ * gauge A * ‖R‖ₑ`, and `‖A‖ₑ ≤ gauge A` hold
  verbatim at non-members, so no axiom and no downstream lemma carries a
  membership hypothesis.
- *Four laws suffice.* Closure under `0`, `+`, `•`, `-` and finite sums is
  `Submodule` membership for the carrier; `gauge 0 = 0` follows from homogeneity
  at `c = 0` (which also rules out the everywhere-`∞` gauge); definiteness
  follows from `‖A‖ₑ ≤ gauge A`.
- *Completeness is a typeclass.* `OperatorIdealFamily.Elem` is a type synonym
  for the carrier — the bare subtype already inherits the *operator* norm and
  the two differ — carrying a `NormedAddCommGroup`/`NormedSpace` for the ideal
  norm; completeness is `CompleteSpace` for it, not a hand-rolled Cauchy
  criterion.

### Hilbert spaces, independent universes

The space parameters are `[RCLike 𝕜]` with `InnerProductSpace` and
`CompleteSpace` on both sides, and the source and target universes stay
independent in the base layer.

The Hilbert restriction is **forced by the examples, not by the laws.** All four
laws are norm-only and are meaningful verbatim over Banach spaces. But of the
five gauges a Davis--Kahan-scale development actually needs — operator norm,
finite Ky Fan, Schatten `p`, trace class, Hilbert--Schmidt — only the first
survives outside Hilbert space, and the obstruction is `gauge_add_le`. The
finite Ky Fan gauge `∑_{n<k} aₙ` is *defined* at full Banach generality, since
`approximationNumber` is stated for seminormed spaces over a
`NontriviallyNormedField`; its subadditivity is what is Hilbertian. The
available proof runs through singular values and majorization, and the classical
additivity of approximation numbers,

```text
a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T),
```

does not recover it: at `k = 2` it yields only `a₀(S) + 2a₀(T) + a₁(S)`, which
is not `∑_{n<2} aₙ(S) + ∑_{n<2} aₙ(T)`. A Banach-wide base would therefore be a
structure with one instance and no route to the motivating ones.

Re-widening is mechanical should a Banach instance appear — no proof in the
module uses the inner product, only the norm.

The universe split is a separate, genuine obstruction: `adjoint` exchanges
source and target, so a family closed under adjoints cannot keep the two
universes independent. Hence two structures rather than one with an optional
field.

## What is missing

1. **S1 — symmetric norming functions.** A symmetric gauge `Φ` on finitely
   supported `ℝ≥0` sequences (monotone, symmetric, `Φ(e₀) = 1`), its extension
   to infinite sequences, and the induced ideal `S_Φ = {T // Φ(a(T)) < ∞}` with
   `‖T‖_Φ := Φ(a(T))`. The *target* is fixed: this construction produces a
   `TauCeti.SymmetricOperatorIdealFamily` whose gauge is `Φ ∘ a` read in
   `ℝ≥0∞`. This is the third instance of the interface.
2. **S2 — Ky Fan dominance as a mixin.** `∀ k, ∑_{n<k} aₙ(S) ≤ ∑_{n<k} aₙ(T)`
   implies `Φ`-domination for every symmetric gauge `Φ`, and the triangle
   inequality for each `‖·‖_Φ` follows. The Davis--Kahan library bundles this as
   `KyFanDominantIdealFamily`, a three-field `structure` over the canonical
   family; the Tau Ceti form should be a `class` over
   `SymmetricOperatorIdealFamily`, so that a family carries dominance as a
   property rather than as data.
3. **S3 — Schatten instances.** `Φ_p(a) = (∑ aₙ^p)^{1/p}` and the Schatten
   `p`-ideals as instances of S1, with trace class (`p = 1`) as the named
   example still missing.

   Two corrections to the earlier text. First, **Mathlib has neither `Schatten`
   nor a Hilbert--Schmidt theory** — searched 2026-07-28, there is no file
   matching either name under `Mathlib/Analysis/` — so there is nothing to
   reconcile with and no duplication risk; the whole layer is new mathematics
   for the ecosystem. Second, **`p = 2` is done**, but by the *direct* route
   rather than through S1: the Hilbert--Schmidt family above is built from
   `∑' i, ‖T (b i)‖ₑ ^ 2` and the Fubini exchange, and never mentions
   approximation numbers. That is deliberate — it needs no spectral theory, so
   it does not wait on S1 — but it leaves an obligation: **prove
   `∑' n, aₙ(T) ^ 2 = ∑' i, ‖T (b i)‖ₑ ^ 2`**, reconciling the singular-value
   and orthonormal-expansion definitions. In the Davis--Kahan library that
   identity is `paperHilbertSchmidtEnergy_eq_basisEnergy`, and its proof runs
   through finite-dimensional Eckart--Young and monotone convergence; the
   staged form is the S1-facing statement.
4. **S4 — block sums and scalar transport.** The ideal gauge of an orthogonal
   block-diagonal sum in terms of the summands, and invariance of the theory
   under real ⇆ complex complexification, so the real-scalar ideal theory is a
   transported instance rather than a re-proof.

## Ordering and PR slices

1. **The family interface** — `Family/{Basic,OperatorNorm}.lean` as staged.
   Dependency-closed on Mathlib alone. Can ship with the approximation-number
   PR or immediately after it.
2. **Ky Fan** — *staged 2026-07-28* as `ForTauCeti/Analysis/OperatorIdeal/Family/KyFan.lean`
   over `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFan.lean`, with
   the capability class discharged rather than assumed. Ships with PR 1/2.
3. **S1 + S2** — symmetric gauges and dominance.
4. **S3** — Schatten and trace class. Hilbert--Schmidt is already staged and
   can ship with the family interface; the rest waits on S1.
5. **S4** — block sums and transport.

## References

- A. Pietsch, *Operator Ideals*, North-Holland, 1980.
- I. C. Gohberg and M. G. Krein, *Introduction to the Theory of Linear
  Nonselfadjoint Operators*, AMS, 1969, chapters on symmetrically normed ideals.
- J. W. Calkin, "Two-sided ideals and congruences in the ring of bounded
  operators in Hilbert space," *Ann. of Math.* 42 (1941), 839--873.
- B. Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS, 2005.
- R. Bhatia, *Matrix Analysis*, Springer, 1997, for Ky Fan inequalities and
  majorization.

## Provenance and coordination

The staged implementation replaces a Davis--Kahan record,
`RectangularSymmetricIdealFamily`
(`DavisKahan/OperatorIdeal/UnitarilyInvariant/RectangularFamily.lean`), which
had the free-data shape this roadmap's first decision rejects: membership and a
total real gauge as independent fields, one universe, hand-rolled completeness,
fourteen fields. That record is derivable from the canonical family
(`SymmetricOperatorIdealFamily.toRectangular`) and there is deliberately no
inverse — a historical record does not determine a canonical family, which is
the defect restated. It is being retired in the Davis--Kahan tree and is not
part of any submission.

When code is migrated, preserve declaration-level provenance, authorship, and
Apache-2.0 licensing.
