# Compiled Lean proof-dependency export contract

**Purpose:** Turn the current import-boundary overapproximation into a
constant-level reference graph so that the course's proof prerequisites can
be audited without silently treating whole modules as mathematical lemmas.

## Suggested export format (JSONL)

One record per elaborated declaration, anchored to the exact compiled environment:

```json
{
  "declaration": "MyNamespace.myTheorem",
  "defining_module": "TauCeti.Analysis.SomeModule",
  "kind": "theorem",
  "type_constant_references": ["..."],
  "value_constant_references": ["..."],
  "elaboration_revision": "...",
  "dependency_library": "TauCeti"
}
```

Collect the constants referenced in the **elaborated type** and, separately,
those referenced in the **stored declaration value/proof**. Keep the initial
root set exact (the 29 maintained paper endpoints), and recurse along
referenced declarations with a depth parameter. Mark dependencies unresolved
when a module/constant cannot be located. A declaration used only through an
import should **not** be reported as a theorem-level dependency.

This is an *output contract*, not an untested Lean executable. On the actual
pinned environment, the exporter should:

1. Load the target declarations using Lean's `Environment`.
2. Traverse `Expr` trees and record `Expr.const` references in type and value
   separately, deduplicated by fully-qualified `Name`.
3. Distinguish constants in proof terms from constants present only in types;
   record opaque declarations as a boundary, not silently a leaf proof.
4. Store the exact Lean, TauCeti, Mathlib, and DKPS revisions and declaration
   ownership so the export can be reproduced.
5. Mark direct references separately from transitive closure. The curriculum
   graph will be built from **mathematical** arguments, with the Lean graph as
   supporting evidence; the two DAGs need not coincide.
6. Join the resulting declaration IDs to the existing census for donor origin,
   Spectra ancestry, accepted/independent downstream implementations, and
   deleted source recovery. Never assign origin from the namespace alone.

A snapshot of module imports cannot satisfy this contract. It is sufficient
for the present structural audit only.
