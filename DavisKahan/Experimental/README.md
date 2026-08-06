# Experimental Davis--Kahan development

This tree contains unfinished work toward both the canonical full-paper theory
and optional extensions. In particular, the Hilbert-space modules are not a
secondary generalization of an already completed finite theory: they contain
major portions of the default Davis--Kahan 1970 objective.

The tree mirrors the mathematical organization of the stable `DavisKahan`
library. A completed cluster can therefore be promoted by moving it to the
corresponding stable path rather than redesigning its module boundary.

That promotion happened at scale on 2026-08-05: every module here whose import
closure had become admission-free moved to the corresponding production path,
namespaces untouched. What follows is what is left, and every entry is left for
one of exactly two reasons — it still carries a `sorry`, or it does not compile.

- `Frontier/` holds the remaining Davis--Kahan 1970 frontier statements — the
  Section 3 classification spine, the infinite-dimensional Section 4
  propositions and the Section 9 analytic model — together with the `sorry`s
  that mark what is still open. Its Section 8 and circle-contour leaves were
  promoted to `DavisKahan/Frontier/`.
- `InfiniteDimensional/Core/` contains provisional spectral, form, and
  operator-angle infrastructure required by the paper's Hilbert-space scope.
- `InfiniteDimensional/Sylvester/` retains the cutoff interface, the legacy
  ordered engine and the unbounded development; the bounded, Fourier-semigroup
  and ordered-semigroup layers are now `DavisKahan/InfiniteDimensional/`.
- `InfiniteDimensional/SinTheta/` retains the canonical, unbounded and
  ideal-interval-exterior obligations; the bounded, continuation and spectral
  bridges moved out.
- `InfiniteDimensional/Ideals/CompactAndSingular.lean` is the remaining
  approximation-number obligation.
- `InfiniteDimensional/{OperatorBlocks/OffDiagonal,Sharpness,DirectRotation}`,
  `MathAhead/HiddenFoundations/` and `Scratch/SharedFoundations/Ideal/` are the
  modules that **do not compile**. They are admission-free only because nothing
  ever elaborated them, which is precisely why they may not be promoted; each is
  named with its reason in `scripts/check_experimental_coverage.py`.

Experimental modules may import stable modules. Stable modules must not import
this tree. Status as experimental means the declarations are not yet accepted
as stable APIs; it does not mean they are outside the main source-fidelity
roadmap.

Build the complete experimental development with:

```bash
lake build DavisKahan.Experimental.All
```
