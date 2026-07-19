# Status handoff: unbounded sine-theta, complex and real routes

Date: 2026-07-19. Written after a compile-repair pass over the two
"not compile checked" drops (`9d05c59`, `88fe012`, `2678bff`).

## Read this first

**Both the complex and the real unbounded sine-theta routes are now complete
and admission-free.** Do not redo them, and do not regress them.

Every declaration below was checked with `#print axioms` against a fresh build
and prints exactly `[propext, Classical.choice, Quot.sound]`:

### Complex route (was already done; re-verified, no regression)

| declaration |
|---|
| `ForMathlib.DavisKahanExt.ClosedOperator.realSpectrum` |
| `SpectraBridge.realSpectrum_eq_spectraSpectrum` |
| `genuineSylvesterIntervalExteriorGap_of_legacy` |
| `davisKahan1970_sylvester_complex` |
| `sinTheta_unbounded_complex`, `sinTheta_unbounded_exact_complex` |
| `generalizedSinTheta_unbounded_complex`, `..._exact_complex` |
| `GeneralSinThetaProblem.result` |
| `IsometricSinThetaProblem.result_complex` |
| `BoundedGeneralSinThetaProblem.result` |

### Real route (completed during this pass)

| declaration |
|---|
| `ClosedOperatorComplexification.isSelfAdjoint_complexify` |
| `ClosedOperatorComplexification.closedSylvesterEquation_complexify` |
| `ClosedOperatorComplexification.mem_complexify_adjoint_domain_iff` |
| `sinTheta_unbounded_real`, `sinTheta_unbounded_exact_real` |
| `generalizedSinTheta_unbounded_real`, `..._exact_real` |
| `IsometricSinThetaProblem.result_real` |
| `RealGeneralSinThetaProblem.result` |
| `RealBoundedGeneralSinThetaProblem.result` |

The previous handoff prompt (`dev/real-route-completion-prompt.md`) authorized
**retiring** the real route if it turned out to be unsound. That authorization is
withdrawn — it is sound and it is finished. That file is superseded by this one.

## Verification protocol — the part that actually matters

**`lake build` does NOT cover this work, and reports success anyway.**

`DavisKahan.lean` deliberately imports only the bounded, finite-dimensional, and
`PartIII` facades; its docstring states that experiments and other source
transcriptions require explicit imports. `PartIII.lean` in turn imports only
finite-dimensional modules. So the entire unbounded sine-theta tree — and the
general source facade `Sources/DavisKahan1970/FullPartIII.lean` — is outside the
default target set.

Consequences you must design around:

- A green `lake build` is **not** evidence about anything in this document.
- Unimported files rot silently. Check with:
  ```bash
  for f in $(find DavisKahan ForMathlib -name '*.lean'); do
    [ -f ".lake/build/lib/lean/${f%.lean}.olean" ] || echo "UNBUILT: $f"
  done
  ```
- **A stale `.olean` makes `#print axioms` confidently report a clean result for
  a declaration whose source no longer compiles.** If a build fails partway,
  every downstream olean is left stale. Always build the specific module to
  success before trusting an axiom check on it, and compare olean mtimes against
  source mtimes when a result looks surprising. This cost a previous session a
  wrong conclusion.

Build the real targets explicitly:

```bash
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.RealSpecializations
lake build DavisKahan.Sources.DavisKahan1970.GeneralSinTheta
lake build DavisKahan.Sources.DavisKahan1970.FullPartIII
```

`SinTheta/FullUnboundedAudit.lean` is intentionally unimported; compile it
directly with `lake env lean <path>`.

**Recommendation for the maintainer, not for an agent to do unilaterally:**
consider whether `FullPartIII` belongs in the default target set. Excluding the
*experimental* tree is clearly deliberate; excluding the general source facade
may be an unintended consequence of the same choice.

## Absolute constraints

- **Never introduce `sorry`, `admit`, `native_decide`, or a new `axiom`.** If you
  cannot prove something, leave it failing and report it. A file with 5 honest
  errors beats a file that "compiles" via a placeholder.
- **Never weaken a theorem statement** or delete a declaration to make an error
  disappear.
- Repository policy: the literal words `sorry` and `axiom` must never appear in a
  Lean comment or docstring. Write "left incomplete" or "open obligation".
- Do not modify the verified declarations listed above except to fix a genuine
  regression you caused.
- `Core/UnboundedSpectral.lean` carries 31 legacy admissions. The verified chain
  no longer depends on it; that is intentional. Leave it alone.
- `Challenge/**/Conformance.lean` is immutable.

## Fix patterns proven in this codebase

These were each paid for with real debugging time. Read them before starting.

1. **`abbrev X := F E` with `E` a section variable** makes `E` an *implicit
   argument*, so every use carries an unsolvable metavariable ("typeclass
   instance problem is stuck ... contains metavariables"). Use
   `local notation "X" => F E`. This alone removed ~26 errors.
2. **`@[simp]` is not a guarantee of firing.** `complexify_apply_re` /
   `complexify_apply_im` are marked `@[simp]`, match syntactically, and *never
   fire under `simp`* in this codebase. Every resolvent-transport failure in
   `ClosedOperatorComplexification` traced back to this one fact. Pull them into
   explicit `rw` chains.
3. **`omit` goes above the docstring and needs `in`.** See AGENTS.md. Putting the
   docstring first fails with `unexpected token 'omit'; expected 'lemma'`, which
   never mentions docstrings.
4. **`linarith`/`nlinarith` fail on definitionally-but-not-syntactically equal
   atoms**, and also when a needed sign fact is simply absent from context.
   Prefer a deterministic lemma (`pow_le_pow_left₀`) over a heuristic call.
5. **`Submodule.span_induction` takes the membership proof LAST.** Use
   `induction hz using Submodule.span_induction with | mem | zero | add | smul`
   so argument-order changes cannot silently break it.
6. **`linearIndependent_iff'` binds the `Finset` before the coefficients**
   (`∀ s : Finset ι, ∀ g : ι → R, ...`).
7. **`fun_prop` cannot see through `WithLp` or subtype domains.** Supply
   continuity explicitly; `WithLp.homeomorphProd 2 E E` is the L2↔product
   homeomorphism.
8. **`Continuous.prodMk` is the current name.** `Continuous.cl` and
   `Complex.continuous_iff` do not exist. To build complex continuity from
   coordinates, go through `Complex.re_add_im` and `Complex.continuous_ofReal`.
9. **Rewriting inside a dependent subtype proof** gives "motive is not type
   correct". Prove a congruence lemma `(u : H) = (v : H) → f u = f v` via
   `congrArg f (Subtype.ext h)` instead. `ClosedOperatorComplexification.
   toLinearMap_congr` exists for this.
10. **There is no `ext` lemma for `ClosedOperator`.** Use
    `ClosedOperatorComplexification.closedOperator_ext` (domain equality plus
    agreeing action; the remaining fields are propositions).
11. **`RCLike.conj_ofReal` / `RCLike.re_ofReal_mul` do not fire on `ℂ`**, where
    `↑a` is `Complex.ofReal`. Use the `Complex.*` lemmas.
12. **`ContinuousLinearMap.apply 𝕜 X x`** — the second explicit argument is the
    **codomain**, not the domain.
13. **Namespace shadowing is a live hazard here.** `selfAdjointSpectralProjection`
    resolves to a 3-argument incomplete placeholder in `Core/UnboundedSpectral.lean`
    that beats the real 4-argument `SpectraBridge` version brought in by `open`.
    Always qualify it. Similarly `RealComplexification.complexify` (bounded) and
    `ClosedOperatorComplexification.complexify` (closed) coexist in scope.
14. Before using ANY lemma name, confirm it exists:
    `grep -rn "theorem <name>" .lake/packages/mathlib/Mathlib/ vendor/Spectra/ DavisKahan/ ForMathlib/`.
    Existence is not the same as being *in scope* — check the namespace too. Four
    "unknown identifier" errors in this pass were real lemmas in unopened
    namespaces (`Spectra.YosidaHille`, `Spectra.Essential`).

## Known latent design problem — read before "fixing" it

`Core/Complexification.lean` creates a `Module ℝ (RealComplexification E)`
**diamond**:

- `instModuleReal` (line 71) supplies `Module ℝ` directly from `WithLp 2 (E × E)`;
- `instModuleComplex` (line 133) supplies `Module ℂ`, whose scalar restriction
  yields a *second, non-defeq* `Module ℝ`.

So `ContinuousLinearMap.algebra` builds an `Algebra ℝ (… →L[ℂ] …)` over
`instModuleReal`, while mathlib's `IsSelfAdjoint.instContinuousFunctionalCalculus`
has `Algebra.complexToReal` baked into its conclusion — and unification fails.
Any `HPow (RealComplexification F →L[ℂ] RealComplexification F) ℝ ?m` failure is
this.

Workaround (this accounted for 28 of 31 errors in `RealFrameFactorization`):
reinstall both instances in each consuming file, since `local instance` does
**not** propagate to importers:

```lean
noncomputable local instance :
    Algebra ℝ (RealComplexification E →L[ℂ] RealComplexification E) :=
  Algebra.complexToReal
noncomputable local instance :
    ContinuousFunctionalCalculus ℝ
      (RealComplexification E →L[ℂ] RealComplexification E) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
```

plus imports `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.{Basic,Instances}`.

The principled fix — deriving `instModuleReal` and `instNormedSpaceReal` by
restriction from the complex structure so the two paths are definitionally equal
— remains **out of scope**: that file is foundational and widely imported, and
changing it forces a very large rebuild. Raise it as a separate ticket.

## Reporting standard

Report only what Lean accepted, with the numbers you actually observed. Do not
claim a module compiles unless `lake build <module> 2>&1 | grep -c "error:"`
printed `0`. For anything you could not fix, quote the verbatim Lean error plus
your diagnosis.

Explicitly flag anything you believe is **mathematically wrong** rather than
mis-elaborated. Across this entire pass, exactly one such issue surfaced (a
reversed orientation in `starProjection_add_starProjection_orthogonal` usage),
and it was masked behind an elaboration error until that error was cleared —
so "all remaining errors are elaboration-level" is a conclusion available only
*after* the elaboration errors are gone, never before.
