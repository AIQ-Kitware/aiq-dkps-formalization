# Canonical spectrum migration: full-scope Davis--Kahan proof lineage

## Goal and fixed mathematical result

Replace the two donor notions of the spectrum of a partial linear map with
**the definitions actually accepted by TauCeti**:

- `_root_.LinearPMap.spectrum A` is the complement of the canonical resolvent set
  for `z I - A`;
- `_root_.LinearPMap.realSpectrum A` is its real-scalar preimage, available
  uniformly over `RCLike` (both real and complex Hilbert spaces).

The maintained proof of the Davis--Kahan 1970 single-angle sine theorem should
consume these accepted concepts, not a second locally maintained spectrum.
The source-facing endpoint is
`TauCeti.DavisKahan1970.sinTheta_unbounded_explicitSeparation_whereDefinedUIN_rclike`
and its underlying theorem is
`TauCeti.DavisKahan1970.sinTheta_unbounded_formGap_whereDefinedUIN_rclike`.

**Mathematical scope is invariant.** Preserve self-adjoint possibly unbounded
operators, the real/complex scalar generality, full Hilbert-space dimensions,
interval/exterior separation in both orientations, the two ordered half-line
form-gap alternatives, the bounded residual with explicit domain hypotheses,
and normalized symmetric ideal norms where both norms are defined. Do not
substitute generic pairwise separation: it does not imply the factor-one
Sylvester bound for these configurations.

## Immutable provenance / comparison anchors

These are **commit identities**, not copies of obsolete implementations kept
alive in production:

| Evidence layer | Git revision | Role |
|---|---|---|
| Before upstream-first migration | `acac427e5a34b769bfe52359216acfc6b6dd5582` | Original maintained DKPS theorem/proof route; benchmark for historical declaration closure |
| Luna pause point | `2bca6ddd155878315acdcef2e93049d218d524b3` | Partial adoption of canonical spectrum before this change |
| TauCeti dependency | `14b2d241ddc09c76f3354c7324b8be49e81a4245` | Accepted upstream declarations used by this migration; pin, not approximate branch state |
| Pinned Mathlib | `e3e75e86143b43849829fdcd44a39a6b0fe35234` | Mathlib revision targeted by the pinned TauCeti |
| Lean | `leanprover/lean4:v4.36.0-rc1` | Matching toolchain |

The old `Presentation.lean` at `acac427e` is SHA-256
`0008940235391e5f3012a88a3dd6cbfb52600ea87df430d764fe84db1912d576`.
The pre-overlay `Sylvester/Gap.lean` at the paused state is SHA-256
`3f4bceb51cabe1d7bc7238007f24a0b81b85fb0072a9dc9896e65faddaeff70e`.
Do not rewrite the historical commits, squash away the only surviving old
proof, or treat Palomar's separate Challenge/Solution path as a byte-for-byte
snapshot of the maintained 1970 proof. Existing detached historical submodules
remain untouched.

If the original commits are not reachable from another permanent ref, preserve
them before branch cleanup; the following creates **new** tags only (never
force-moves tags):

```bash
git cat-file -t acac427e5a34b769bfe52359216acfc6b6dd5582
git cat-file -t 2bca6ddd155878315acdcef2e93049d218d524b3
git tag dkps-lineage/pre-upstream-spectrum-2026-10-19 acac427e5a34b769bfe52359216acfc6b6dd5582
git tag dkps-lineage/pre-canonical-spectrum-2026-10-20 2bca6ddd155878315acdcef2e93049d218d524b3
```

If a tag already exists, inspect it instead of overwriting it. Tags are local
until deliberately pushed; document whether the anchor is also available from
the remote. These are optional preservation actions, not prerequisites for
compiling the overlay.

## Mathematical equivalence solved by this migration

The donor real resolvent condition supplies a bounded inverse `R` for
`A - λ I`, including inverse laws and transport into `dom A`. The accepted
`LinearPMap.resolventSet` supplies an inverse of `λ I - A`. **Negate the
inverse**, rather than assuming the predicates are definitionally equal:

\[
  (A-\lambda I)R=R(A-\lambda I)=I
  \quad\Longleftrightarrow\quad
  (\lambda I-A)(-R)=(-R)(\lambda I-A)=I.
\]

The transport-of-domain requirement is unchanged under negation because an
operator domain is a submodule. No closedness, self-adjointness, complete space,
or restriction to `ℂ` is needed for this equivalence. Its generic Lean home is
`TauCeti.LinearPMap.mem_realResolventSet_iff_mem_canonical_resolventSet`
in `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean`.

Consequently,

\[
  \operatorname{realSpectrum}_{\rm canonical}(A)
   =\{\lambda\in\mathbb R:\lambda\notin
                \operatorname{realResolventSet}_{\rm legacy}(A)\}.
\]

`canonical_realSpectrum_eq_compl_realResolventSet` proves this equality; the
**old local `realSpectrum` definition and its membership lemma are removed**.
The old real resolvent set is a temporary implementation source only for
inversion arguments not yet ported to the accepted resolver. The current
complex donor spectrum likewise survives only at existing legacy boundary
constructors and *is not* used in maintained source-facing spectrum hypotheses.

For `ℂ`, the accepted real spectrum is definitionally the preimage of the
accepted complex spectrum under `Complex.ofReal`. The formerly difficult
`realSpectrum_eq_spectraSpectrum` wrapper was removed because its statement
is now definitional. Its consumers were changed to direct uses of the
canonical spectrum, and the interval/exterior gap conversion no longer needs
a donor-to-upstream spectral bridge. The meaningful part of the conversion is the **geometry of the gap**:
outside the enlarged closed interval is the complement of the enlarged open
interval. Preserve strict/open endpoints in this conversion.

This is a change of *formal representation*, not a new mathematical
assumption. The exact before-and-after theorem types are not definitionally
equal at the original donor-resolvent boundary. A future dependency comparison
must normalize by the proved spectrum equivalence; string equality of the
printed theorem statements is not an appropriate comparison.

## Scope of the proposed overlay

The migration changes the public-facing spectral vocabulary through the
following connected families of modules, plus their direct consumers:

1. `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean`,
   `UnitaryTransport.lean`, `Complexification.lean`: delete duplicate real
   spectrum, retain a generic sign-convention bridge, and transport canonical
   spectrum under unitary equivalence and real complexification.
2. `DavisKahan/SpectralTheory/PartialMap/RealSpectrum.lean` and
   `Complexification.lean`: reuse upstream spectrum and local canonical
   complexification; eliminate the repeated sign-convention proof.
3. `DavisKahan/Sylvester/Gap.lean`, `Unbounded/AllGap.lean`,
   `Unbounded/IntervalExterior.lean`, `Unbounded/FormBoundedGap.lean`,
   `ForTauCeti/Analysis/InnerProductSpace/Sylvester/SpectralGap.lean`:
   present the same three geometric gap configurations using the *same*
   canonical spectral carrier; keep the ordered form-gap engine intact.
4. `DavisKahan/SpectralTheory/UnboundedCentralBand.lean` and
   `ReducingSpectrumUnion.lean`: place conversions precisely at the old
   projection-valued-measure and block-inverse backends, not in theorems.
5. `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean` and
   `ExplicitSeparationPresentation.lean`: the full source-facing sine theorem
   has canonical spectral hypotheses. Its explicit separation remains expanded
   and still includes both orientations and both semibounded alternatives.
6. Section 8 and 9, FreeBeam, real/complex transfer, Sylvester
   Hilbert--Schmidt, and double-angle consumers: migrate the public spectrum
   terms without dropping their cases or introducing narrower scalar types.

No historical submodule or `dev/palomar-candidate` source was changed.

## Concrete Lean repair fronts, in dependency order

Luna should now repair **this implementation**, rather than replace it with a
new set of aliases. The authoring environment for this overlay did not have
Lean/Lake, so the following is a prioritized engineering handoff, not a claim
that every file compiled here.

1. **Bridge first:** build
   `ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed`.
   In the new generic inverse-sign equivalence, verify the record constructor
   shape of `_root_.LinearPMap.mem_resolventSet_iff`, the `RCLike` coercion, and
   proof normalization. If `module`/`linear_combination` need tactic imports,
   use precise imports or elementary module algebra, not additional axioms.
   No `sorry`, `admit`, or axiom should remain.
2. Build `ForTauCeti.Analysis.InnerProductSpace.LinearPMap.UnitaryTransport`
   and `.Complexification`. Confirm their canonical spectrum equalities work
   over *both* real and complex scalars. The old real-resolvent bridge is a
   proof-local adapter; keep it out of theorem statements.
3. Build `DavisKahan.SpectralTheory.PartialMap.RealSpectrum` and
   `.Complexification`. The accepted complex real-spectrum preimage should
   elaborate directly. Keep the old donor-complex/resolvent equivalence lemma
   only where an unported proof actually consumes the legacy type.
4. Build `ForTauCeti.Analysis.InnerProductSpace.Sylvester.SpectralGap`,
   `DavisKahan.SpectralTheory.GapResolvent`,
   `DavisKahan.SpectralTheory.UnboundedCentralBand`, and
   `DavisKahan.SpectralTheory.ReducingSpectrumUnion`. These are the expected
   hotspots: an old constructive resolvent witness and the canonical `IsResolventAt`
   have equivalent fields but different namespace/record boundaries.
   **Do not turn a genuine spectral witness into `rfl`**; use the proven bridge.
5. Build `DavisKahan.Sylvester.Gap`,
   `DavisKahan.Sylvester.Unbounded.IntervalExterior`,
   `DavisKahan.Sylvester.Unbounded.AllGap`, and
   `DavisKahan.Sylvester.Unbounded.FormBoundedGap`.
   The spectral-vs-form distinction remains meaningful for ordered cases;
   the old-donor-vs-canonical *set* distinction should no longer appear.
   Keep both orientations when treating interval/exterior separation.
6. Build `DavisKahan.DoubleAngle.UnboundedIdeal`,
   `DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise`,
   `DavisKahan.Sources.DavisKahan1970.Section8.Theorem81UnboundedBranch`,
   and the Section 8/9 and FreeBeam consumers. Remove needless upstream-to-donor
   round trips that become trivial after the source theorem signatures migrate.
7. **Endpoint gates:** build
   `DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation`,
   `DavisKahan.Sources.DavisKahan1970.SineTheta.ExplicitSeparationPresentation`,
   then `DavisKahan.All` and the repository default targets. Run the maintained
   29-result census. Do not downgrade previously verified results on the basis
   of this migration's temporary compilation errors; repair the API transition.

Use `lake exe cache get` before any `lake build` invocation. Recommended first
repair session:

```bash
cd ~/code/aiq-dkps-formalization
lake exe cache get
lake build ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
lake build ForTauCeti.Analysis.InnerProductSpace.LinearPMap.UnitaryTransport \
  ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Complexification
lake build DavisKahan.SpectralTheory.PartialMap.RealSpectrum \
  DavisKahan.SpectralTheory.PartialMap.Complexification
lake build DavisKahan.Sylvester.Unbounded.FormBoundedGap
lake build DavisKahan.Sources.DavisKahan1970.SineTheta.ExplicitSeparationPresentation
```

If an early build fails, fix that dependency before building the downstream
set. For a multi-module build after repairs, refresh the cache as needed; the
initial `lake exe cache get` must not be skipped.

## Regression obligations

- Both `realSpectrum` and `spectrum` in **maintained theorem statements** use
  the accepted `_root_.LinearPMap` definitions. No donor `realSpectrum`
  remains. Remaining donor `spectrum` or `resolventSet` references must be
  limited to isolated legacy backend theorem proofs and removed once unused.
- Do not add a new spectral-gap alias (`DavisKahanSeparation`, etc.) or
  replace the explicit-separation presentation with an opaque inductive.
- Do not remove interval/exterior orientation reversal or either ordered
  semiboundedness branch; do not replace `RCLike` by complex-only machinery.
- Preserve all source census theorem names and statements except for the
  mathematically justified representation change. If a headline/census
  result is itself accepted upstream, its statement may remain here as a
  forwarding wrapper, rather than losing the source anchor.
- No rewrites to detached historical submodules, Palomar, or the original
  1970 source-result inventory simply to make the dependency graph smaller.
- Preserve source and Spectra provenance even when implementation code moves.
- Running the default `lake build` and the repository's maintained census
  check is the proof verification gate. A pure grep check is not that gate.

## Measuring how the dependency graph changes

Do **not** introduce another graph extractor. Reuse the existing `leanq`
`graph-index`, `dev/README.md`, and the existing formalization-journal
prerequisite/theory-graph scripts. Capture graphs at the three immutably
identified checkpoints, with toolchain, Mathlib, and TauCeti revisions in
sidecar metadata. The August 17, 2026 graphs are separate dated evidence;
do not silently relabel them as the October 20 graphs.

For the *same source result*, compare the canonical elaborated theorem type,
its source correspondence, the project-local proof closure, the TauCeti/Mathlib
boundaries, and the 10--20 load-bearing mathematical declarations identified
in `RESEARCH_PLAN.md` and `cases/sine_theta.md` for the proposed paper
*What Does It Take to Prove Davis--Kahan?* The research plan is a separate
artifact and should not be overwritten by this migration.

Classify each observed graph difference:

| Difference | What it could mean | Evidence required |
|---|---|---|
| Donor declaration replaced by identical TauCeti proof | Ownership relocation | Compare normalized theorem statements and proof ideas |
| One new TauCeti lemma subsumes several special cases | Generalization | List the old cases and show the new hypotheses imply each |
| Different intermediate lemma/proof route | Possible mathematical simplification | Explain the *mathematical* reduction, not just counts |
| Definition/universe/typeclass churn | API/representation overhead | Record as such, not as a new mathematical dependency |
| Changed theorem assumption or ideal class | Potential scope regression | Prove equivalence or restore the original hypothesis |
| New direct-rotation dependence in the sine theorem | Unexpected cross-branch coupling | Inspect proof terms and the Section 4 historical distinction |

The observed older proof closure cannot establish a logically minimal basis.
A smaller graph likewise cannot establish that the mathematical argument
became simpler unless the proof comparison demonstrates that fact.
