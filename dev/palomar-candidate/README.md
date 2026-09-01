# A Palomar candidate for the four Section 2 theorems

**This is a feasibility experiment, not a submission surface.**  The submitted
entry lives in the standalone repository under `submodules/`, which owns it.
Nothing here has been submitted to or registered with Palomar.

It exists because an earlier audit concluded that a four-theorem Challenge was
blocked, and reached that conclusion from the *location* of the development's
vocabulary rather than by trying to write one.  That inference does not follow
from Palomar's policy, which permits Challenge-local definitions.  So the
candidate was built.

## What it establishes

The Challenge **is** writable.

| measurement | value | policy |
| --- | --- | --- |
| `Challenge.lean` | **511 lines / 23,579 bytes** | hard cap 1000 lines / 100 KiB; preferred 300 lines / 32 KiB |
| imports | **1** (`import Mathlib`) | Lean core + allowlisted Mathlib / Tau Ceti / CSLib |
| local definitions | 27 | permitted |
| headline theorems | 4 | — |
| `sorry` in the Challenge | 4, one per headline theorem | the Comparator convention |
| functional calculus used | **none** | — |
| `Solution.lean` | 291 lines / 12,855 bytes | no cap |

Reproduce with:

```bash
lake env lean dev/palomar-candidate/Challenge.lean \
  -o dev/palomar-candidate/Challenge.olean
lake env sh -c 'LEAN_PATH="$PWD/dev/palomar-candidate:$LEAN_PATH" \
  lean dev/palomar-candidate/Solution.lean'
rm -f dev/palomar-candidate/*.olean dev/palomar-candidate/*.ilean
```

(The `.olean` is deliberately not committed: Palomar rejects a repository with
committed build artifacts.  The namespace is `RotationOfEigenvectors` only so
that the file can be compiled inside this repository without colliding with the
development's own `DavisKahan1970`.)

## The idea that made it small

A unitarily invariant norm sees only the singular-value sequence.  So no angle
operator has to be *constructed* by a functional calculus; it only has to be
*named*:

* `sin Θ₀` is the paper's own `(I − F₀F₀⋆)E₀`;
* `sin 2Θ` is the projector difference between `U` and its mirror image in `V` --
  reflecting doubles every principal angle;
* `sin 2Θ₀` is the overlap of `U` with the mirror image of its own complement;
* the tangents are *characterised* by their singular values, `tan θ` against
  `sin θ`, which is how Davis and Kahan introduce them.

That removes the whole continuous-functional-calculus layer from the statement
surface, and with it the real-scalar problem that the earlier audit had
mistaken for the blocker.

The unitarily invariant norm itself is the dimension-coherent symmetric norming
function: a two-sided unitarily invariant seminorm on `n × n` complex matrices
for each `n`, normalised on one unit singular value, unchanged by appending a
zero, and evaluated on an operator as the supremum over prefixes of its
singular-value sequence.  That is the development's own definition, and
`Solution.lean` proves the two agree **by `rfl`**.

## What it does not yet establish

`Solution.lean` proves the Challenge's `sin Θ` statement from the development,
and at `ℂ` and at `ℝ` it proves it outright.  Three things remain, and they are
named exactly in `Solution.lean`'s closing section:

1. **The scalar field.**  The `[RCLike 𝕜]` statement needs
   `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜` and
   `HasUnboundedSylvesterKyFan 𝕜` at an arbitrary `RCLike` field.  These are
   development capabilities, not source hypotheses, and they are instances at
   both of the paper's fields.  Discharging them generically is one scalar-field
   transport, for which Mathlib now supplies the dispatch
   (`RCLike.I_eq_zero_or_im_I_eq_one`, `realLinearIsometryEquiv`,
   `complexLinearIsometryEquiv`).  It would serve all four theorems at once.
2. **One missing development lemma** for the ambient `sin 2Θ` clause: that
   reflection through a subspace *reducing* the perturbed operator preserves the
   unperturbed domain and intertwines.  The development proves this for a
   *spectral* subspace only.
3. **`tan Θ` and `tan 2Θ` correspondence**, not yet carried out.  Their
   endpoints exist at both fields and the tangent characterisation used here is
   the development's own, so the shapes match.

## One defect the experiment found in its own Challenge

The `sin 2Θ` **directed** clause quantifies over an arbitrary subspace reducing
`A`, while the development's directed residual endpoint selects its subspace
from a measurable spectral set.  As written, the Challenge is therefore
*stronger* than what the development proves.  The repair is to prove the
directed endpoint for an arbitrary reducing subspace, or to weaken the clause --
not to leave the stronger claim standing.  This is recorded rather than quietly
fixed because it is the kind of thing that only shows up when the candidate is
actually built.
