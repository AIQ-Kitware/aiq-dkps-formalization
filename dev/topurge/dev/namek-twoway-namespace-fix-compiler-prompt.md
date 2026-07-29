Inspect the latest commit in `/home/joncrall/code/aiq-dkps-namek`.

The latest change repairs invalid field notation in the shared-foundations
ideal scratch layer. The helper theorems live in the local scratch namespaces,
not in the production structure namespaces, so calls now name the scratch
helpers explicitly and pass the ideal object as the first argument.

Run, in order:

```bash
lake build DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization
lake build DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.OperatorAbsoluteValueComplex
lake build DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.ReflectionTransport
lake build DavisKahan.Experimental.Scratch.SharedFoundations.All
```

Repair any remaining elaboration or API-name problems while preserving all
statements and mathematics. Do not use `sorry`, `admit`, `native_decide`, new
axioms, or proof escapes. Do not move or promote the scratch declarations in
this pass. Report exactly which targets compile and any remaining blockers.
