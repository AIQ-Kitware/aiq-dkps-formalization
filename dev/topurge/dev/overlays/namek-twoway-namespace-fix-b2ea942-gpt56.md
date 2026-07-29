# Namek two-way factorization namespace fix

Base inspected: `b2ea942eabea`

Target working repository for this session:

```text
/home/joncrall/code/aiq-dkps-namek
```

## Problem

`TwoWayFactorization.lean` declares scratch helper theorems under the local
`SharedFoundations.SymmetricNormIdeal` and
`SharedFoundations.RectangularSymmetricIdealFamily` namespaces. Calls such as
`I.mem_of_eq_comp_comp` and `N.gauge_le_of_eq_comp_comp` use structure-field
notation, which instead searches the production type namespaces:

- `ForMathlib.DavisKahanExt.SymmetricNormIdeal`
- `ForMathlib.DavisKahan.Experimental.ExactSinTheta.RectangularSymmetricIdealFamily`

Those declarations do not exist there, so elaboration fails even though the
scratch helper declarations immediately above are present.

## Repair

Use explicit calls to the scratch helper namespaces and pass `I` or `N` as the
first argument. The same repair is applied proactively to the two immediate
ideal-theory dependents.

Changed files:

- `DavisKahan/Experimental/Scratch/SharedFoundations/Ideal/TwoWayFactorization.lean`
- `DavisKahan/Experimental/Scratch/SharedFoundations/Ideal/OperatorAbsoluteValueComplex.lean`
- `DavisKahan/Experimental/Scratch/SharedFoundations/Ideal/ReflectionTransport.lean`

No theorem statements or mathematical hypotheses are changed.

## Verification targets

```bash
lake build DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization
lake build DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.OperatorAbsoluteValueComplex
lake build DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.ReflectionTransport
lake build DavisKahan.Experimental.Scratch.SharedFoundations.All
```

The overlay was statically checked for clean diffs, but Lean was unavailable in
the packaging environment. Do not report it green until these commands pass.
