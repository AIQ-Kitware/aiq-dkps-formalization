# Comprehensive Davis--Kahan deck

## Intent

One coherent, visually polished collection of the existing Manim/VTK
explanations, with **every distinct scene once**, enough context for a viewer
to follow the mathematics without accompanying live narration.  This is a
long-form narrative with chapter signposts, not a concatenation of the old
seven reference parts.  The completed 21-scene `kitware-talk` is a separate,
stable artifact; it must not inherit exploratory revisions.

The new presentation title and chapter slides are independent of the existing
talk. No extra statements of the artifact's intended audience or distribution
purpose should appear in the presentation itself.

## Narrative order

1. **Motivation and foundations.** Start with the project's orientation and
   self-adjoint operators; move from eigenvectors and spectral gaps to trial
   subspaces and why their movement needs a bound.
2. **The sine-theta theorem.** Introduce principal angles, the literal
   `sinTheta0` operator and its rectangular representative, residuals, the
   certified separation `delta`, the theorem, proof intuition, the Sylvester
   mechanism, and a real Lean signature. Keep original `A`, perturbed `Ahat`,
   and gap `g` distinct from `delta` throughout.
3. **Three-dimensional geometry.** Two planes sharing a hinge, the residual,
   changing tilt and spectral gap, a genuine perturbation, then the underlying
   VTK interactive application. The VTK animated builds remain full-frame;
   accompanying stills must fit their column rather than being cropped by the
   display's edges.
4. **The remaining theorem family.** Common perturbation setup; directed and
   ambient angles; a two-by-two comparison; tan Theta and its one-sidedness;
   sin 2Theta and reflection; tan 2Theta and Jacobi/repulsion; close with the
   four-theorem selection map.
5. **Proposition 4.4.** Printed claim, four-dimensional counterexample, why
   trace norm exposes the failure, explicit numerical witness and the exact
   Lean refutation/Q-norm repair. Do not generalize the refutation beyond its
   actual norm class or confuse this with the three-dimensional sine model.
6. **The formalization and its limitations.** Human/agent workflow, kernel
   check versus source comparison, three differently scoped statements,
   reversals, foundations and retained usage, and careful claims about
   confidence. The formalization's 29 results include one refuted/repaired
   printed proposition; do not claim that Lean proved all printed results true.
7. **Reference, summary and image.** Three symbol-color glossaries as useful
   reference material, then the finished-talk takeaway and exactly one VTK
   video-only finale. The Manim 3D experiment does not belong in either deck.

Keep presentation-specific depth badges out of `comprehensive`. This is a
reference work where all included scenes contribute substantive content.

## Artifacts

From `visualizations/`:

```bash
make comprehensive
```

This uses Manim 1080p/30 FPS by default, `JOBS=2`, and produces:

- `renders/comprehensive.standalone.html`: the single shareable file, with video
  assets embedded;
- `renders/comprehensive.html` and `renders/comprehensive_assets/`: the
  split-media version;
- `renders/comprehensive.pdf` and `renders/comprehensive.handout.pdf`;
- `slides-comprehensive/`: the scene JSONs and generated intermediate videos.

For draft iterations, use `make comprehensive QUALITY=l PDF=0`. A scene-limited
rerender (`SCENES="..."`) requires the other scenes to have already been rendered
for that same deck. The VTK 3D asset-generation step is separate and may be
costly on a cold cache. For the completed short talk use `make kitware`.

## Review discipline

- Numerical visualizations are explanatory specializations, not extra Lean
  theorems. Their input models have tests; preserve those models.
- Keep current centralized symbol roles and colors. Do not reintroduce `U/V`
  aliases for `range(E0)/range(F0)` in the sine-theta sequence.
- Refine overly dense or clipped scenes using rendered output, not arbitrary
  exact-copy tests. Avoid introducing fades solely for decoration.
- Test deck membership, ordering and source paths structurally. Do **not**
  assert literal slide text in automated tests.
- Always inspect a representative PDF/HTML render before asserting visual
  quality; a green Python test suite cannot detect overlap or unreadable type.
