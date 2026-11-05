# Spectral transport novelty tour

## Semantic colors and verified scope

`novelty-tour` is a separate presentation using the manuscript's transport
notation: `U` is the **source**, colored amber (`TRIAL`), and `V` is the
**target**, colored blue (`WANTED`). Its LaTeX uses `\sym{Usource}` and
`\sym{Vtarget}`, and its projection symbols use `ProjSource`/`ProjTarget`.
Do not replace these with historical `\sym{U}`/`\sym{V}`: in the older
sine-theta slides those keys deliberately mean exact wanted `U` (blue) and
trial `V` (amber). Keep both semantic namespaces and the global palette.
Principal angles and optimal phases are magenta (`SINE`), thresholds violet
(`GAP`), and the smoothed objective/optimal cost steel (`CURRENT`).

`novelty-tour` is anchored to the Lean-completed exact finite complex
Charbonnier optimizer, closed uniqueness cutoff, mixed-angle quartic growth,
critical-planar failure of quadratic growth, and commuting-unitary correction.
The scalar worked examples come from `dkvis/novelty_math.py` and have
numeric regression tests. The higher-rank finite complex Schatten `1<p<2`
minimum, complete all-angle optimizer classification, exact simple-angle
counts and no-nonglobal-local-minima theorem **are now Lean-verified** at
source snapshot `427169ce`; include them as certified mathematical results.
Its optimizer Grassmannian decomposition is an algebraic set equivalence,
not a verified topological or smooth parametrization. The unrestricted finite-dimensional real matching theorem for
`1 <= p < 2` is now verified, including the nuclear endpoint. The complex
nuclear minimum, real/complex even-multiplicity equality criterion, real
canonical-value criterion, and exact nearest nuclear correction are also
proved. They are visualized in `N08NuclearMatching`, `N08NuclearParity`,
`N08NuclearCanonical`, and `N08NuclearCorrection`. Do not infer a full
`p=1` optimizer classification, endpoint local-to-global theorem, the
strict-exponent real/complex parity conjecture, or infinite-dimensional
ideal theory from these claims. Unproved sorted-sum formulas, uniform
field-gap estimates and historical-priority claims must remain qualified.

