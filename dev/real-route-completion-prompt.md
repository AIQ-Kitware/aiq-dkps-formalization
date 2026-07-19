# Task: complete (or cleanly retire) the real-scalar sine-theta route

## Read this first — what is already DONE

**The original objective is achieved and machine-verified. Do not redo it, and do not regress it.**

The complex source-facing sine-theta theorem is now admission-free. Verified by
`#print axioms` on a fresh build — each prints exactly
`[propext, Classical.choice, Quot.sound]`:

| declaration | status |
|---|---|
| `ForMathlib.DavisKahanExt.ClosedOperator.realSpectrum` | clean (now a real definition, no longer an admission) |
| `SpectraBridge.realSpectrum_eq_spectraSpectrum` | clean |
| `genuineSylvesterIntervalExteriorGap_of_legacy` | clean |
| `davisKahan1970_sylvester_complex` | clean |
| `sinTheta_unbounded_complex`, `sinTheta_unbounded_exact_complex` | clean |
| `generalizedSinTheta_unbounded_complex`, `..._exact_complex` | clean |
| `GeneralSinThetaProblem.result` (= `DavisKahan1970.generalizedSinTheta`) | clean |
| `IsometricSinThetaProblem.result_complex` (= `DavisKahan1970.sinTheta`) | clean |
| `BoundedGeneralSinThetaProblem.result` | clean |

These modules all compile: `Core/Unbounded.lean`,
`SpectraBridge/RealSpectrumBridge.lean`, `Sylvester/LegacyGapCompletion.lean`,
`SinTheta/LegacyGapCompletion.lean`, `SinTheta/Canonical.lean`,
`SinTheta/Specializations.lean`, plus `Core/ComplexificationFunctionalCalculus.lean`
and `SinTheta/FrameFactorizationGeneric.lean`.

**Trap to avoid:** a stale `.olean` will make `#print axioms` report `sorryAx`
for a declaration that is actually clean. If a build fails partway, downstream
oleans are left stale. Always `lake build <module>` to success before trusting
an axiom check on it, and compare `.olean` mtimes against source mtimes if a
result looks wrong.

## What is NOT done — your task

A previous agent added, beyond what was asked, a full **real-scalar route**:
complexify a real closed operator, transport the Sylvester/sine-theta theory
through the complexification, and descend back to `ℝ`. It was written without
ever compiling. It does not build.

Current state (all counts from real builds):

| module | lines | state |
|---|---|---|
| `Core/ClosedOperatorComplexification.lean` | 528 | **22 errors** (down from ~60) |
| `SinTheta/RealFrameFactorization.lean` | 308 | ~31 errors, partially repaired |
| `Ideals/ComplexificationApproximation.lean` | 306 | blocked |
| `Sylvester/RealUnbounded.lean` | 98 | blocked |
| `SinTheta/RealUnbounded.lean` | 89 | blocked |
| `SinTheta/RealGeneralized.lean` | 134 | blocked |
| `SinTheta/RealCanonical.lean` | 139 | blocked |
| `SinTheta/RealSpecializations.lean` | 132 | blocked |

**Every blocked module is blocked by `Core/ClosedOperatorComplexification.lean`
alone.** That file is the single bottleneck; fix it first and six modules
become independently workable.

`DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean` imports
`SinTheta/RealSpecializations.lean`, so **`lake build` is currently red** even
though the complex chain is green.

### Remaining errors in the bottleneck file

```
350, 353        Type mismatch after simplification (isSymmetric_complexify)
398,399,404,405 Application type mismatch (adjoint-domain characterisation)
420, 421        fun_prop cannot prove Continuous (ofRealDomain / ofImaginaryDomain)
427,428,434,435 unsolved goals; `Continuous.cl` does not exist
439, 440        fun_prop cannot prove Continuous (domainRe / domainIm)
442, 443        Unknown constant `Complex.continuous_iff.mpr`
494,495,501,502 Type mismatch (resolvent transport)
524, 528        Type mismatch (spectrum / gap transport)
```

Several of these are the *same* missing fact: **continuity of the domain
coordinate maps**. The file already has `continuous_re` / `continuous_im`
(added during repair) — the `ofRealDomain` / `ofImaginaryDomain` / `domainRe` /
`domainIm` continuity lemmas are the natural next additions, and they should
be proved explicitly rather than by `fun_prop`, which cannot see through the
`WithLp` L2 structure or subtype domains.

## You have explicit permission to retire this route

The real route is **optional scope**. It was not requested. If you judge, after
honest effort, that a piece of it is mathematically wrong rather than merely
mis-elaborated — or that completing it would require inventing substantial new
theory — the correct outcome is to **retire it cleanly, not to fake it**.

To retire cleanly:
1. Remove the real aliases and the `RealSpecializations` import from
   `DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean`, restoring it to
   the complex-only surface (keep `sinTheta := IsometricSinThetaProblem.result_complex`).
2. Remove the real modules from `SinTheta/All.lean` and `Sylvester/All.lean`.
3. Leave the real `.lean` files in the tree, untouched, so the work is not lost.
4. Say so plainly in your report.

A green build with a verified complex theorem is a strictly better outcome than
a red build with an aspirational real one. Do not delete anyone's files.

## Absolute constraints

- **Never introduce `sorry`, `admit`, `native_decide`, or a new `axiom`.** If you
  cannot prove something, leave the code failing and report it. A file with 5
  honest errors beats a file that "compiles" via a placeholder.
- **Never weaken a theorem statement** to make it provable. Never delete a
  declaration to make an error disappear.
- Repository policy (`AGENTS.md`): the literal words `sorry` and `axiom` must
  never appear in a Lean comment or docstring. Write "left incomplete" or
  "open obligation" instead.
- Do not modify anything in the verified complex chain listed at the top,
  except to fix a genuine regression you caused.
- Do not touch `Core/UnboundedSpectral.lean` (31 legacy admissions). The fixed
  chain no longer depends on it; that is intentional.
- `Challenge/**/Conformance.lean` is immutable by repository policy.

## Fix patterns already proven in this codebase

1. **`abbrev X := F E` with `E` a section variable** makes `E` an *implicit
   argument*, so every use carries an unsolvable metavariable ("typeclass
   instance problem is stuck ... contains metavariables"). Fix with
   `local notation "X" => F E`. This alone removed ~26 errors.
2. **`rw [h]` where `h` is a `let`-bound local** fails ("Expected an equality or
   iff proof"). Introduce an explicit `have hEq : lhs = rhs := ...` and rewrite
   with that.
3. **Rewriting inside a dependent subtype proof** gives "motive is not type
   correct". Instead prove a congruence lemma
   `(u : H) = (v : H) → f u = f v` (via `congrArg f (Subtype.ext h)`) and use it.
   `ClosedOperatorComplexification.toLinearMap_congr` already exists for this.
4. **`linarith`/`nlinarith` fail when hypotheses are only *definitionally*
   equal to the goal's atoms.** Fix by ascribing the hypothesis type explicitly
   (`have h : <goal-shaped statement> := hA x`), which forces the defeq check at
   elaboration time and gives the arithmetic tactic syntactically matching atoms.
5. **`RCLike.conj_ofReal` / `RCLike.re_ofReal_mul` do not fire on `ℂ`.** Over `ℂ`,
   `↑a` is `Complex.ofReal`, not `RCLike.ofReal`. Use `Complex.conj_ofReal`, and
   for `RCLike.re (↑a * w)` introduce a bridge
   `have : ∀ w : ℂ, RCLike.re ((a:ℂ) * w) = a * RCLike.re w := by intro w; simp [RCLike.re_to_complex, Complex.mul_re]`.
6. **`ContinuousLinearMap.apply 𝕜 X x`** — the second explicit argument is the
   **codomain**, not the domain.
7. `Continuous.prodMk` is the current name (not `prod_mk`). `Continuous.cl` does
   not exist — you probably want `IsClosed`/`closure` API or `Continuous.comp`.
8. There is **no `ext` lemma for `ClosedOperator`** in the core API;
   `ClosedOperatorComplexification.closedOperator_ext` was added during repair
   (domain equality + agreeing action; the other two fields are propositions).
9. `WithLp.homeomorphProd 2 E E` is the L2↔product homeomorphism; use it (not
   `fun_prop`) to get continuity through `RealComplexification`.

## Method

1. Fix `Core/ClosedOperatorComplexification.lean` first — it unblocks everything.
2. Work errors top-down; later ones are often cascades.
3. Rebuild after each fix; the error count must decrease monotonically.
4. Before using ANY lemma name, confirm it exists:
   `grep -rn "theorem <name>" .lake/packages/mathlib/Mathlib/ DavisKahan/ ForMathlib/`.
5. Then take the six unblocked modules; several are short (89–139 lines).

## Verification protocol — run all of it

```bash
cd ~/code/aiq-dkps-formalization
lake build                      # must be error-free
```

Then in a scratch file:

```lean
import DavisKahan.Sources.DavisKahan1970.GeneralSinTheta
#print axioms ForMathlib.DavisKahan1970.sinTheta
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_boundedSpecialization
-- only if you completed the real route:
#print axioms ForMathlib.DavisKahan1970.sinTheta_real
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_real
```

All must print `[propext, Classical.choice, Quot.sound]` and nothing else.

Also confirm no admissions were added and nothing unreachable broke:

```bash
git diff | grep -nE '^\+.*\b(sorry|admit)\b'   # must be empty
for f in $(find DavisKahan ForMathlib -name '*.lean'); do
  [ -f ".lake/build/lib/lean/${f%.lean}.olean" ] || echo "UNBUILT: $f"
done
```

`lake build` only builds modules reachable from the library roots, so unimported
files rot silently — that check matters. `SinTheta/FullUnboundedAudit.lean` is
intentionally unimported; compile it directly with `lake env lean <path>`.

## Reporting standard

Report only what Lean accepted, with the numbers you actually observed. For each
module: done / partially done (with error count) / retired. Quote the verbatim
Lean error for anything you could not fix, plus your diagnosis.

Explicitly flag anything you believe is **mathematically wrong** rather than
mis-elaborated — that is the most valuable thing you can tell us, and it is the
trigger for retiring the route rather than grinding on it.

Do not claim a module compiles unless `lake build <module> | grep -c "error:"`
printed `0`.
