# Lean 4 Module-System Migration — DKPS

Migrate the maintained Lean source files in `~/code/aiq-dkps-formalization` to Lean 4's module system, eliminating warnings about importing Mathlib modules from non-module files.

This is a **semantics-preserving structural migration**. Preserve all mathematical results, theorem statements, hypotheses, public APIs, typeclass behavior, and existing upstream TauCeti integration.

Make substantial progress across coherent groups of files rather than fixing warnings one at a time. Prefer straightforward, mechanical transformations where possible, but carefully handle visibility, imports, and definitional transparency.

## 1. Understand the dependency graph first

Lean's module system is opt-in through the `module` header. A file using the module system cannot import a file that does not use it.

Consequently, simply adding `module` to every file emitting an import warning is not sufficient.

Construct the relevant local import dependency graph and distinguish:

- External Mathlib and TauCeti modules, which already use the module system.
- Local DKPS files already converted to modules.
- Local DKPS files still using the older file format.
- Aggregator files that re-export collections of modules.
- Files containing macros, tactics, custom elaborators, or initialization code.
- Files whose definitions are unfolded by downstream proofs.

Use this graph to choose the conversion order.

**Convert bottom-up, from imported dependencies toward their consumers.**

For example, `DavisKahan/Geometry/Polar/DirectRotation.lean` imports `DavisKahan.BoundedOperator.Reflection`. If `Reflection.lean` remains a non-module file, migrate its dependency closure before converting `DirectRotation.lean`.

Apply the same principle throughout the repository, including the `ForTauCeti`, `DavisKahan`, `YuWangSamworth2015`, and paper-specific hierarchies.

Do not modify TauCeti itself or vendored dependencies as part of this migration.

## 2. Use a compatibility-preserving initial conversion

For most theorem-oriented files, begin with Lean's documented migration pattern:

```lean
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import DavisKahan.BoundedOperator.Reflection

@[expose] public section

namespace TauCeti.DavisKahan

-- Existing declarations and proofs remain here.

end TauCeti.DavisKahan
```

The example assumes both imported files have already been converted.

The important concepts are:

**`module`**

Enables the new module system, with separate public and private scopes.

**`public import`**

Makes the imported module's public declarations available to downstream importers. An ordinary `import` makes them available within the current module without re-exporting that import.

**`public section`**

Ensures declarations that were previously accessible to downstream files remain publicly accessible by default.

**`@[expose] public section`**

Additionally preserves access to definition bodies for downstream proofs that rely on unfolding and definitional equality.

For the initial migration, favor compatibility over aggressively minimizing visibility. Broad exposure is acceptable during conversion and can be refined afterward.

Do not accidentally change explicitly `private` declarations into public declarations.

Preserve existing namespace organization and explicit declaration modifiers.

## 3. Preserve transitive import behavior

One of the main differences from the older system is that imports no longer necessarily re-export their contents.

Suppose the original dependency chain is:

```text
A imports B
B imports C
```

Previously, code in `A` may have used declarations from `C` without importing `C` directly.

After migration, that behavior depends on whether `B` publicly imports `C`.

Handle this deliberately:

- Use `public import` when downstream consumers rely on re-exported declarations.
- Use ordinary `import` for implementation-only dependencies.
- Preserve the public import behavior of aggregator modules.
- Introduce direct imports when they make an actual dependency clearer.
- Avoid repeatedly adding broad imports merely to make missing identifiers disappear.

During the first conversion pass, preserving existing imports as `public import` is a reasonable default for library modules. Narrow them later when downstream dependencies are understood.

Pay particular attention to modules whose original role was to collect and re-export results from several other files.

## 4. Preserve definitional transparency

This is the most important proof-engineering issue.

In the module system, a public definition can be visible while its implementation remains opaque to importing modules.

This can break previously compiling proofs that rely on:

- `rfl`
- `change`
- `dsimp`
- `simp [someDefinition]`
- `rw` through reducible definitions
- Definitional equality between operator expressions
- Typeclass unification
- Coercion normalization

When a definition becomes opaque, Lean may report an error equivalent to:

```text
Expected a definition with an exposed body
```

or report that two expressions are no longer definitionally equal.

The preferred repair is to expose the relevant definition at its source:

```lean
@[expose] public def someDefinition := ...
```

Or retain the broader `@[expose] public section` during the initial migration.

Do not rewrite mathematical proofs merely to compensate for accidentally hidden definitions.

Do not change a theorem statement, insert new assumptions, or introduce new wrapper lemmas when restoring the original transparency resolves the problem.

In particular, DKPS relies heavily on definitional equivalences between:

- Real and complex operator representations
- Continuous linear maps and linear maps
- Orthogonal projections and submodule restrictions
- Functional-calculus constructions
- Adjoint and composition representations
- Spectral and singular-subspace operators

Preserve these relationships throughout the migration.

## 5. Handle `import all` carefully

Lean provides:

```lean
import all Some.Module
```

This exposes private information from an imported module.

However, `import all` is generally restricted to modules in the same Lake package. It is not the correct solution for accessing private implementation details from Mathlib or TauCeti.

Use it selectively when local DKPS modules legitimately depend on private implementation details of other DKPS modules.

Prefer making a genuinely shared declaration public, or exposing a definition, when that is the more appropriate long-term interface.

Do not globally enable cross-package private imports as a shortcut.

## 6. Handle metaprogramming separately

Files containing custom Lean syntax, macros, tactics, elaborators, or initialization code may need different migration treatment.

The module system distinguishes ordinary code from metaprogramming dependencies.

Relevant constructs include:

```lean
meta import Some.Module
```

and, when downstream metaprograms also need the dependency:

```lean
public meta import Some.Module
```

Inspect the actual metaprogram dependencies instead of converting every import mechanically.

Distinguish these situations:

- A metaprogram needs declarations available during elaboration.
- A public metaprogram needs to expose its dependencies downstream.
- Ordinary proofs use tactics supplied by an imported module.
- Runtime code and compile-time code are being mixed.

Do not turn mathematical declarations into `meta` declarations to work around import errors.

Do not alter executable initialization behavior as an incidental part of the migration.

## 7. Diagnose migration failures according to their cause

Use the following interpretation when errors arise.

| Error or symptom | Likely underlying issue | Preferred approach |
|---|---|---|
| `cannot import non-module` | An imported local file has not been migrated | Convert its dependency closure first |
| Unknown identifier or constant | A needed declaration became private, or a transitive import stopped being available | Restore appropriate public visibility or import |
| Expected exposed definition | Definition body is private | Use `@[expose]` at the defining module |
| Definitional equality failure | Previously transparent definition became opaque | Check source-level exposure |
| Kernel unknown constant | Public declaration refers to inaccessible implementation details | Repair visibility at the source |
| Metaprogram requires `meta` import | Dependency is unavailable in the meta phase | Correct the meta import relationship |
| New typeclass inference failure | An instance or definition needed during inference is no longer exposed | Restore the original instance visibility and transparency |
| New elaboration timeout | Missing transparency or changed import visibility may be expanding search | Diagnose visibility and elaboration context before modifying proofs |

Be particularly careful with operator-algebra instances.

There have already been problems involving distinct scalar-multiplication instances such as `instSMul` and `realAlgebra.toSMul`.

A module migration must not change which scalar multiplication, algebra instance, or functional-calculus instance a theorem uses.

Do not introduce local instance overrides to work around a module visibility problem unless the original mathematics genuinely requires them.

## 8. Preserve mathematical and public API stability

Treat the conversion as infrastructure work, not a mathematical refactoring.

Keep the following unchanged:

- Theorem names, types, hypotheses, and conclusions
- Existing definitions and their semantics
- Instance priorities and instance selection
- Namespace structure
- Source-paper correspondence
- Existing upstream TauCeti API usage
- Proof strategies except where module visibility genuinely requires adjustment

Avoid unrelated proof simplification, import modernization, theorem renaming, or donor-code retirement.

In particular, do not attempt to replace local DKPS mathematics with TauCeti mathematics while converting its modules. That is a separate concern and creates unnecessary ambiguity when diagnosing failures.

Do not add `sorry`, `admit`, axioms, weakened statements, or proof shortcuts.

Do not raise heartbeat limits or introduce compatibility options simply to conceal a migration-induced problem.

## 9. Work in coherent dependency-closed batches

Choose related groups of modules that can be converted together.

A useful progression is:

1. Foundational local files that depend only on already-module-system dependencies.
2. Their immediate mathematical consumers.
3. Shared spectral, operator, projection, and functional-calculus utilities.
4. Larger Davis–Kahan proof hierarchies.
5. Paper-facing theorem modules.
6. Aggregator modules and remaining cross-family consumers.

Adjust that order to the actual dependency graph rather than enforcing an arbitrary directory sequence.

For each batch, identify the dependency closure, convert it, and resolve visibility issues before expanding into another cluster.

A small batch of five to twenty related modules is a reasonable working unit, but larger mechanically straightforward clusters are fine.

Prioritize files responsible for many repeated import warnings, especially if converting their shared dependencies unlocks numerous downstream files.

Avoid repeatedly modifying the same files through disconnected one-line changes.

## 10. Treat module conversion and module optimization as separate phases

The immediate objective is **a faithful module-system conversion**.

Initially, it is acceptable to use:

```lean
public import ...
@[expose] public section
```

throughout much of the repository to preserve the original behavior.

Once the conversion is stable, improve the interfaces selectively:

- Replace unnecessary `public import` statements with ordinary imports.
- Remove excessive `@[expose]` where definitions do not need to unfold downstream.
- Restrict internal helpers to private scope.
- Keep public declarations needed by paper results and downstream library consumers.
- Reduce unnecessary transitive imports without breaking consumers.

Do not optimize prematurely. The visibility changes should be driven by actual dependencies rather than assumptions about what seems internal.

The benefits of the module system depend partly on keeping implementation details private, but preserving mathematical correctness and compatibility comes first.

## 11. Preserve the intended meaning of the warning cleanup

The goal is to eliminate warnings such as:

```text
imports `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute`
from package `mathlib`, which is designed for use with the module
system; consider adding `module` to the start of this file
```

by actually converting DKPS to use Lean's module system.

Do not achieve this by setting `allowNonModules = true`, disabling warning categories, changing global linter configuration, or suppressing diagnostic output.

Those approaches would hide the warning without achieving the architectural conversion.

Warnings about deprecated Mathlib declarations, unused tactics, or unrelated lint issues are separate concerns. Avoid broad cleanup in those areas unless a change is directly necessary for the module migration.

## 12. Completion criteria

Continue progressively until all maintained DKPS Lean source files intended to use the module system have been converted and their dependency relationships are consistent.

Maintain a clear distinction between:

- Fully migrated modules
- Files still requiring conversion
- Files blocked by non-module local dependencies
- Files requiring additional public exposure
- Files requiring special metaprogramming treatment
- Files deliberately left in the older format for a concrete technical reason

There should be no accidental loss of transitive imports, no changes to public mathematical interfaces, and no unresolved visibility or opacity regressions.

Prefer completing an entire dependency-closed cluster over touching every file superficially.

Use the Lean reference documentation for the exact syntax and visibility semantics appropriate to the repository's Lean version:

https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/

**The central principle: migrate visibility and dependency structure, not the mathematics. Make the existing proofs work under the new module semantics by preserving their original public declarations, imports, and required definitional transparency.**
