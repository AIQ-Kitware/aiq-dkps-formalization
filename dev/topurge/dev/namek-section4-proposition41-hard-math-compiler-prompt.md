Work only in `/home/joncrall/code/aiq-dkps-namek`.

Inspect the latest commit and compile the new additive Section 4 scratch theorem:

```bash
scripts/lake_build_report.py --fail-fast \
    DavisKahan.Experimental.Scratch.Section4.InfiniteProposition41
```

The new module supplies the hard infinite-dimensional mathematics for
Davis--Kahan Proposition 4.1.  It replaces a principal-vector argument by a
two-threshold spectral-cutoff/min--max proof for the positive source cosine.
The intended final theorem is:

```lean
proposition4_1_restrictedDisplacement_approximationNumbers_scratch
```

Repair API names, coercions, universe inference, spectral-projection syntax,
and local algebra narrowly.  Preserve the theorem statements and the proof
architecture.  Do not replace the spectral-cutoff proof with the already known
finite-dimensional theorem, and do not weaken to operator norm or finite rank.
Do not use `sorry`, `admit`, `native_decide`, new axioms, or theorem-statement
changes.

Do not edit production `Experimental/Frontier/Section4.lean` or any active
Section 3 file.  Once the leaf compiles, run:

```bash
scripts/lake_build_report.py --fail-fast \
    DavisKahan.Experimental.Scratch.Section4.All
```

Finally check that the main theorem has no admission dependency:

```lean
cat > /tmp/check_prop41.lean <<'LEAN'
import DavisKahan.Experimental.Scratch.Section4.InfiniteProposition41
#print axioms ForMathlib.DavisKahan.Experimental.Scratch.Section4.proposition4_1_restrictedDisplacement_approximationNumbers_scratch
LEAN
lake env lean /tmp/check_prop41.lean
```
