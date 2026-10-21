# Upstream consumption: native reducing restrictions and UI-seminorm API

## Exact checkpoint

- Apply over DKPS commit `7cd3d7a11b91` (the 2026-10-21 12:13 snapshot).
- That snapshot pins TauCeti `87dad819828705ed8329ff53b9bc53634a064b1a`,
  Mathlib `e3e75e86143b43849829fdcd44a39a6b0fe35234`, and Lean `v4.36.0-rc1`.
- The pre-upstream formal proof remains recoverable at DKPS `acac427e5a34`.
- This record began with the Oct 21 foundation overlay and was updated after
  the canonical-restriction follow-up and user-run targeted Lean builds.
  The user reported the final `Closed` + `RestrictionExtras` targeted build
  successful; a new full `lake build` after that replacement has not been
  established in this handoff. This documentation update changes no Lean files.

## Mathematical change 1: reducing subspaces

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` formerly
implemented the density, closed-graph, and self-adjointness proofs for a
restriction to an orthogonally complemented reducing subspace. They are now
proofs by application of the accepted TauCeti theorems.

The donor predicate has *four* components: domain preservation under both
orthogonal projections, and invariance of both subspaces. Upstream's
`_root_.LinearPMap.IsReducing A U` has *three*: domain preservation under
`P_U`, and the two invariances. The fourth follows because
`P_{Uᗮ}x = x - P_U x`. This is not a change of hypothesis scope.

New exact, non-axiomatic conversion points:

- `TauCeti.LinearPMap.ReducesSubspace.toIsReducing`
- `TauCeti.LinearPMap.ReducesSubspace.ofIsReducing`
- `TauCeti.LinearPMap.reducesSubspace_iff_isReducing`
- `TauCeti.LinearPMap.reducingRestriction_eq_restrict`

The latter identifies the historical `reducingRestriction` partial map with
`A.restrict hred.toIsReducing.isInvariant`. Three formerly independent donor
proofs now forward to accepted upstream results:

- `IsReducing.dense_restrict_domain`
- `IsClosed.restrict`
- `IsReducing.isSelfAdjoint_restrict`

**All three existing donor theorem statements are textually unchanged.**

### Follow-up: the representation is now canonical (2026-10-21)

The first overlay introduced the equivalence and forwarding proofs but
retained the old restricted-domain/operator constructors. The subsequently
compiled canonical-restriction follow-up **deleted the independent restricted
linear-map implementation** and made the historical entry point a direct
alias to upstream:

```lean
noncomputable def reducingRestriction
    (A : E →ₗ.[𝕜] E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (hred : ReducesSubspace A U) : U →ₗ.[𝕜] U :=
  A.restrict hred.toIsReducing.isInvariant
```

`reducingRestrictionDomain` now forwards to `A.domain.comap U.subtype` rather
than defining a second representation; bounded reducing-block constructors
also consume native `A.restrict`. The API provides explicit domain-membership
and application lemmas because TauCeti's `restrict` is not definitionally
transparent across module boundaries. The user reported the `Closed` and
`RestrictionExtras` targeted Lean build successful after the v2 opacity repair.

**This is implementation retirement, not yet consumer/API retirement.**
`ReducesSubspace`, `reducingRestriction`, its domain alias and the historical
application lemmas still remain as temporary compatibility entry points.
The next work is to migrate consumer statements/proofs to native
`LinearPMap.IsReducing` and `A.restrict`, in dependency order, and delete
adapters as soon as their last clients disappear. Do not manufacture a new
namespace wrapper around upstream just to keep the old spelling. The stronger
local adjoint-domain iff remains valuable until an accepted equivalent is
established; do not delete it merely for a numeric reduction.

Upstream sources at the pinned SHA:

- `TauCeti/Analysis/InnerProductSpace/LinearPMap/Reducing.lean`
- `TauCeti/LinearAlgebra/LinearPMap/Restrict.lean`
- `TauCeti/Topology/Algebra/Module/LinearPMap/Restrict.lean`

## Mathematical change 2: eliminate temporary seminorm shims

`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Transport.lean`
no longer declares nine forwarding lemmas (`nonneg`, `apply_zero`, `add_le`,
`smul_eq`, `apply_neg`, `invariant`, `invariant_left`, `invariant_right`,
`eq_of_same_singularValues`). All maintained callers were changed to the
accepted `apply_nonneg`, `map_zero`, `map_add_le_add`, `map_smul_eq_mul`,
`map_neg_eq_map`, `map_linearIsometryEquiv_comp_comp`,
`map_linearIsometryEquiv_comp`, `map_comp_linearIsometryEquiv`, and
`map_eq_of_singularValues_eq` APIs. This touches finite-dimensional sine/double
angle, direct rotations, sharpness, and the local Sylvester norm estimates.

The actual **codomainIsometryTransport** and **domainIsometryTransport**
constructions remain: they cover *isometric embeddings*, not just the
surjective isometric equivalences TauCeti provides. Do not delete these
unless an accepted upstream replacement is identified.

## Compatibility bridges and retirement queue

| Current entry point | Reason it survives | Removal criterion |
| --- | --- | --- |
| `ReducesSubspace.toIsReducing`, `ofIsReducing`, `reducesSubspace_iff_isReducing` | Historical four-field predicate against canonical three-field predicate | Migrate all consumers; delete reverse conversion and old predicate |
| `reducingRestriction` and `reducingRestriction_eq_restrict` | Thin historical name on native `A.restrict` | Last caller uses `A.restrict` with a canonical invariance proof |
| `reducingRestrictionDomain` and projection-domain transport lemmas | Old proof statements use donor domain types | Last caller uses `mem_restrict_domain` and upstream action lemmas |
| Private isometry coercion helpers in finite-dimensional sin/double-angle code | Lean elaboration of `LinearIsometryEquiv` versus `toLinearEquiv` | Direct upstream norm lemmas can be applied in stable canonical form |
| Legacy resolvent-set and spectrum equivalence results | Some unbounded spectral consumers still use the old sign/domain representation | Canonical-resolvent APIs cover the remaining consumers; preserve mathematically distinct lemmas |
| Isometric-embedding `codomainIsometryTransport` / `domainIsometryTransport` | **Not merely compatibility:** supports non-surjective embeddings | Keep unless a genuinely equivalent stronger accepted theorem appears |

Record actual deleted declarations and their consumers when finishing a slice.
A green build validates a transition but is **not** a reason to retain obsolete
bridges. The full downstream and paper-facing result closure must continue to
compile. See the [upstream contribution census](dkps-upstream-contribution-census.md)
for the matching *outbound* provenance record; it is not a requirement to
introduce more migration infrastructure.

## Next implementation slices

1. Migrate the **lower-level reducing restriction consumers** from
   `ReducesSubspace`/`reducingRestriction` to the upstream `IsReducing` predicate
   and `A.restrict`; use public membership/action lemmas, not opaque unfolding.
   Retain historical theorem names only where their source-facing statements
   actually require them. Retire old conversion proofs and domain aliases when
   their last callers are gone.
2. Audit **principal-angle representations**, not merely theorem names: use
   upstream `Submodule` angle maps and projection operators where equivalent.
   Keep genuinely distinct directed or infinite-dimensional statements.
3. Retire **real-valued approximation-number and operator-ideal forwarding
   APIs** only after converting their consumer proof statements to TauCeti's
   singular-value/family representations. Do not recreate a second canonical
   layer to avoid editing callers.
4. Complete **canonical resolvent/spectrum** consumer conversion, with special
   attention to sign, domain and interval/exterior hypotheses. Keep the full
   unbounded, real/complex, where-defined UIN Davis--Kahan results intact.

## Targeted verification checkpoint

The last user-confirmed successful targeted build covered the canonical
restriction foundation and its first consumer:

```bash
cd ~/code/aiq-dkps-formalization
lake exe cache get
lake build \
  ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed \
  DavisKahan.SpectralTheory.ReducingSubspace.RestrictionExtras
```

After further consumer refactoring, build each touched dependency-closed slice
and run the full `lake build` and maintained source census before treating the
campaign as completed. A newer complete build was not reported after this
last representation change; do not infer it from the targeted checkpoint.

```bash
lake exe cache get
lake build
python3 scripts/check_davis_kahan_1970_source_census.py
```

If a kernel/elaboration error arises at a restriction boundary, use the public
domain-membership/application lemmas and `LinearPMap.ext` rather than assuming
an opaque upstream definition unfolds by `rfl`. Do **not** weaken
`ReducesSubspace`, assume boundedness, change a source-facing theorem, or add
axioms/admitted proofs. For canonical seminorm API access, prefer the
existing class lemmas (`map_add_le_add`, `map_smul_eq_mul`, `apply_nonneg`) over
reintroducing deleted forwarding names.

No headline or census theorem statements were edited. This is a dependency
and proof-implementation cleanup, not a research-paper graph/tooling change.
