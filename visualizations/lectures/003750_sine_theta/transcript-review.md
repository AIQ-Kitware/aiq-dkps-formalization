# Sine-theta narration review — 5 November 2026

Reviewed by GPT-6.1-Sol, following the question about matrix norm notation.
The current eighteen core scenes and both Qwen-authored questions were compared
with their scene implementations, numerical models, and the repository's
validated Davis–Kahan source reconstruction. This is an explanatory/source
review, not a new full Lean build or proof-priority audit.

## Findings and corrections

- **Norm notation:** the original operator-norm statement was correct. Bare
  matrix `norm_2` meant the induced Euclidean operator norm, not Schatten 2.
  Use `op` explicitly on the H labels and matrix-residual labels in the shared
  sine-theta scene files. Keep internal numerical API names unchanged. Explain
  Frobenius versus Schatten 2 in the narration.
- **Residual and target selection:** “the angle and residual shrink together”
  described the displayed improvement path but could be read as a general
  guarantee. A Rayleigh residual is zero at an unwanted eigenvector too.
  State that a small residual needs target-selection/separation information.
- **Gap scope:** the theorem and recap must retain the interval/exterior or
  ordered half-line configuration, rather than suggesting arbitrary pairwise
  separation gives a constant-one estimate in every norm. Theorem 6.2 still
  supplies the Hilbert–Schmidt/Frobenius result under pairwise separation;
  Section 5 demonstrates the operator-norm obstruction.
- **Plot semantics:** S11Payoff plots sin(theta), whereas the geometric arc
  displays theta itself. Distinguish them in speech and the inherited notes.
- **Trial scalar:** in the rank-one proof, rho is the trial spectrum itself;
  saying it is “near the trial spectrum” was inaccurate.
- **Scope and definitions:** retain finiteness of the compared ideal norms and
  the unbounded domain hypotheses. In infinite dimension the angle is an
  operator, not necessarily a finite angle list. The domain inner-product
  identity alone expresses symmetry, not full unbounded self-adjointness.
- **Counting:** 29 is the maintained set of counted result statements. Calling
  all 29 “explicitly proved” conflicts with the printed false proposition.
- **Counterexample phrasing:** the two transporters use different invariant
  plane decompositions. The trace norm is the failing norm *among the three
  displayed*; the wording must not exclude failure for other norms.

These passages occur in Qwen's original transcript (`acebd8294`), but several
also reflect inherited presenter notes or slide wording. This is not evidence
that Qwen independently introduced every problem. The operator/Frobenius issue
that prompted this review was ambiguity, not a mathematical error.

Earlier integration corrections already distinguished the scalar error from
its positive sine operator, corrected the general residual interpretation,
and qualified the coincident-plane and rank-one-normalization cases. Those
remain in place; this review does not silently attribute those repairs to Qwen.

## Checked without finding a new mathematical discrepancy

The perturbation and rotating-gap examples agree with `sine_theta_story.py`:
the perturbation has operator norm epsilon, the off-diagonal example tends to
a 45-degree turn as g tends to zero, and the rotating perturbation can sweep
all line directions when epsilon exceeds g/2. The flip is a 90-degree change
of the *leading* line, with matrix difference of operator norm 2 epsilon.

The frame/modulus identities, Rayleigh orthogonality, complementary-plane
picture, residual reduction R = H E0, and the two counterexample singular-value
lists agree with the source/model statements. For the pi/4 witness, the direct
rotation has trace displacement about 3.061, versus 2.828 for the competitor;
operator and Frobenius norms favor the direct rotation. Both quiz answers remain
correct.

Source anchors: `prose/distilled_literature/DavisKahan1970_part_III.tex`,
Section 5, Theorems 6.1/6.2, and Proposition 4.4; the paper-facing sine theorem
in `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean` and its
`SectionTwo.sinTheta` alias; `visualizations/dkvis/sine_theta_story.py`,
`sine_theta_3d.py`, and `prop44.py`. The displayed Lean signature was compared
with the current source-facing hypothesis/conclusion structure; no new kernel
certification is claimed by this prose review.
