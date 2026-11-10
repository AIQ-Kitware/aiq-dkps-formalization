# G2 mathematics extensions: resolvent regularization and spectral energies

Four standalone spoken lectures were drafted using the mathematics developed around the project's operator-theory formalizations as a source of topic selection and exact hypotheses. The **spoken region presents only mathematics**, with no mention of source repositories, proof assistants, library names, or authoring process. The display-only appendices record source correspondence without implying that every broader mathematical theorem in the lecture has been formalized.

## New audio lectures

| ID | Title | Mathematical learning target | Primary source correspondence |
|---|---|---|---|
| 091250 | Resolvents and Yosida regularization | Classical dissipative Yosida approximants; symmetric self-adjoint resolvent regularization; domain and norm limits | `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/YosidaApproximation.lean` |
| 091500 | Strong resolvent convergence and spectral limits | Pointwise resolvent convergence; graph approximation; unitary flow convergence; failure of sharp projection convergence at atoms | Spectral-cutoff and Yosida constructions; broader convergence theory as stated |
| 092250 | Hille–Yosida and contraction semigroups | Dissipativity, maximal range, contraction resolvents, semigroup construction, heat equation | Yosida/Stone constructions as guide; classical Hille–Yosida and Lumer–Phillips as broader theory |
| 099500 | Smoothed singular-value energies | Charbonnier rationalization, Hilbert–Schmidt finiteness criterion, limiting trace norm, finite-matrix gradient | `ForTauCeti/Analysis/OperatorIdeal/Charbonnier.lean` and `.../SmoothedPower.lean` |

These additions use unused IDs between original lectures. They introduce **no changes to the existing 150 scripts**, historical review ledgers, or the G3 sequence. All four have non-spoken reference sidecars.

## Scope and mathematical distinctions

- The classical one-sided dissipative Yosida approximant and the symmetric self-adjoint resolvent approximant have different formulas and different geometry. The spoken lecture compares them explicitly.
- The construction of a contraction semigroup through bounded exponentials is broader than the source's unitary-group results. The source correspondence says so.
- Strong resolvent convergence does not imply norm-resolvent convergence or convergence of sharp spectral projections at spectral boundaries carrying mass.
- For every positive smoothing scale, the Charbonnier sum has the Hilbert–Schmidt ideal as its finite-cost carrier; taking the smoothing scale to zero can diverge on Hilbert–Schmidt operators outside trace class.

## Installation and validation

After extracting the overlay into the repository root, run:

```bash
python3 visualizations/tools/integrate_g2_math_extensions.py --write
python3 visualizations/tools/integrate_g2_math_extensions.py --check
python3 visualizations/draft-stages/tts-lectures/reference_metadata.py --check
python3 visualizations/draft-stages/tts-lectures/extract_narration.py --check \
  visualizations/draft-stages/tts-lectures/091250-*.md \
  visualizations/draft-stages/tts-lectures/091500-*.md \
  visualizations/draft-stages/tts-lectures/092250-*.md \
  visualizations/draft-stages/tts-lectures/099500-*.md
(cd visualizations && python3 -m pytest -q tests/test_g2_mathematics_extensions.py \
  tests/test_audio_course_tracks.py tests/test_audio_lecture_library.py \
  tests/test_course_graph.py)
```

The integration tool adds topic assignments and meaningful dependency edges, updates the audio catalog's size label, and removes fixed 150-lecture expectations in the relevant legacy tests. It updates these shared files **in place**, preserving unrelated edits, and is idempotent.

## Further mathematical subjects worth developing

A subsequent G2 sequence could cover spectral approximation of semigroups (including the Trotter–Kato convergence theorems), abstract forms and form-generated semigroups, compact approximation-number inequalities, trace duality and Schatten Hölder bounds, and differentiability of operator spectral functions. These should be selected for substantive new proofs and examples rather than for the number of formalized declarations behind them.

**Presentation state:** Narration and display-only companions only. Dedicated slide decks and synthesized Breeze listening checks remain separate work.
