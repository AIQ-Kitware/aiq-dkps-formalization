# Section 9 free-beam campaign (DK-9-model → DK-9.x): design and status

## HANDOFF 2026-08-07 (Opus 5) — supersedes the Fable 5 handoff below

**State: `lake build` 9459 jobs green, `lake build DavisKahan.Experimental Challenge
FinishTanTwoTheta` 9386 jobs green, census CLEAN 48/48 with a 190/190 declaration probe,
everything pushed.**  The whole free-beam chain is now in the DEFAULT build
(`FormMethod/All.lean` imports `BeamFormSpace`, `BeamSpectrum`, `BeamSection9`); before
this session it was reachable only by explicit module name and CI did not cover it.

### What closed

* **DK-9-model → `compiled_exact`**, and the blocker `free-beam-closed-operator` is
  deleted.  The operator exists, the trial subspace is proved to be its kernel, the finite
  moments of `TrialSubspace.lean` are proved to be genuine `L²` integrals against it
  (`inner_centeredAffineLp`, `inner_centeredAffineLp_mul`, `inner_mul_centeredAffineLp_mul`),
  the Ritz matrix of (9.5) and the residual Gram matrix are genuine compressions, and
  `FreeBeamFiniteDataCertificate` is inhabited.  The sorried
  `Experimental/Frontier/Section9Analytic.lean` skeleton is deleted.
* **DK-3.2-cor → `compiled_exact`.**  Its next_action was stale on both counts; the missing
  content was the *angle* half of Corollary 3.2, now `corollary3_2_sinAngleOperator_symm`.
* **Equations (9.1), (9.2), (9.4)** are derived from `beamOperator` rather than assumed:
  `beamSinTheta_le`, `beamSinTwoTheta_lt`, `beamSinTwoThetaSum_lt`.

### The one non-obvious obstruction, and how it was beaten

The `sin 2Θ` and tangent theorems all want form bounds on the *low spectral block* plus
spectrum-avoidance on its complement.  The set-based localization lemmas cannot supply
both: `B ⊆ Icc β α` together with `Bᶜ ∩ Ioo (β−δ) (α+δ) = ∅` forces `(β−δ, α+δ) ⊆ B ⊆ [β,α]`,
which is unsatisfiable for `δ > 0`.  **One of the two hypotheses must come from the
operator.**  The route that works, and that every remaining Section 9 conclusion should
reuse:

1. `realSpectrum_beamOperator_subset_sharp` sharpens the gap to `500.5` using `4.73 < β`
   directly (`4.73⁴ = 500.5466…`) instead of the already-rounded `500`.  Do not skip this:
   it is what makes the *strict* printed inequalities come out.
2. Hence every nonzero point of `Iic 500.5` is a resolvent point, so
   `specProjection (Iic 500.5 \ {0}) = 0` and `beamSpecProjection_lowSet_eq_singleton`
   collapses the low projection onto `{0}`.
3. `beamLow_semiboundedBelow` / `beamLow_semiboundedAbove` then give form bounds `0` and `0`
   through `re_inner_apply_bounds_of_subset_Icc` at `B = {0} ⊆ Icc 0 0`, while the
   complement `Ioi 500.5` discharges spectrum-avoidance from the *set* lemma.

Equation (9.1) takes a different and simpler route (residual form, `A₀ = 0` on the kernel,
selecting set `Ici 500` on the perturbed operator) and needs none of this.

### What remains — all of it Section 9, in increasing order of size

1. **(9.3)**, the last bound on DK-9.1-9.4.  `sinTheta_unbounded_gauge_of_spectrum_gap`
   with exactly the (9.1) data reduces it to
   `a₀ + a₁ ≤ residualTopSingularValue ε + residualBottomSingularValue ε`.  `a₀` is
   `norm_beamPerturbation_comp_trialIncl_le`, done.  `a₁` needs one explicit rank-one
   approximant: in the orthonormal trial basis the top eigendirection of the residual Gram
   matrix is `φ₁ + c φ₂` with `c = −(√75 + √76)`, and the eigenvalue identity collapses to
   `(√75+√76)(√75−√76) = −1`, so the radical arithmetic is clean — the Lean cost is the
   rank-one operator plus `finrank beamTrial = 2` (needed to know `{φ₁, φ₂}` spans).
   **There is no shortcut**: `a₁ ≤ a₀` gives `2·residualTop/500`, which exceeds the printed
   `109/50000 · ε`.
2. **(9.5)–(9.7)**, the tangent refinements.  Same spectral inputs as (9.2); the extra
   ingredient is the Rayleigh–Ritz residual condition of the tangent theorems.
3. **(9.8)**, Weinberger comparison.
4. **(9.9)–(9.11)**, individual eigenvector identification inside the cluster.
   `SchurComplement.lean` and `RankOneCorrection.lean` already compile; this is connective
   algebra plus whichever of the above bounds it consumes.

`TheoremOutputCertificate` still exists in `FullExample.lean` and is still trivially
instantiable — the census blocker `section9-certificate-discharge` says so and it is
correct.  Do **not** close the remaining rows by instantiating it.  The pattern that works
is the one used for (9.1), (9.2) and (9.4): prove a named theorem about `beamOperator`
whose statement is the printed bound, and cite that.

Working rules unchanged: serial; never pipe `lake build` (it masks the exit code); one
build at a time; commit and push every milestone; author as the model actually running;
verify census rows against the build before writing code — TEN rows have proved stale this
week, including DK-3.2-cor and S2-tan-two-theta this session.

## Verdict on the existing skeletons

The abstract form method is COMPLETE and sorry-free:
`CoerciveFormData` (FormMethod/CoerciveFormResolvent.lean) → `associatedOperator`
(self-adjoint closed, via `inverseClosedOperator`), `ShiftedBeamFormData`
(FormMethod/ShiftedBeamRealization.lean) → `beamOperator = shifted − 1` with
self-adjointness, nonnegativity (= bendingEnergy), graph compactness from
`SequentiallyCompactEmbedding`.  The α₃>500 root arithmetic is UNCONDITIONAL:
`Classical.five_hundred_lt_pow_four_of_characteristic_eq_zero`
(FreeBeamRootLocalization.lean; root exclusion on (0,4.73] is proved).
`characteristic_eq_zero_of_freeBoundary` classifies nontrivial free modes.
Do NOT build `SobolevTraceFoundation` / `FourthOrderTraceModel` — they demand traces and
maximal domains no consumer needs (memory: check-what-the-consumer-needs).  Inhabit
`CoerciveFormData` directly.

## The concrete model

H := Lp ℂ 2 (volume.restrict (Set.Ioc (0:ℝ) 1)).  Inner products = ∫ x in 0..1 via
`intervalIntegral.integral_of_le`.

V := closed submodule of `WithLp 2 (H × H)` of pairs (u,w) with w the weak second
derivative of u, encoded by the COUNTABLE test family
  φₖ(t) = t²(1−t)²·tᵏ  (k : ℕ):     ∀k, ∫₀¹ u·φₖ'' = ∫₀¹ w·φₖ.
Each constraint is a continuous linear functional ⇒ V closed ⇒ complete.
V's inner product IS the shifted form ⟨u,v⟩+⟨w,z⟩, so `formOperator := id`,
coercivity constant 1, `form_selfAdjoint` trivial.  embed := fst∘subtype (CLM).
bendingEnergy (u,w) := ‖w‖².

## The four hard bricks (Fable does these)

1. REPRESENTATION (the foundation): (u,w) ∈ V ⇒ u =ᵃᵉ a + b·t + (Kw) where
   (Kf)(x) := ∫₀¹ max(x−s,0)·f(s) ds.
   Proof: (a) Fubini on the triangle gives ∫ (Kw)·φₖ'' = ∫ w·φₖ (inner integral:
   ∫ₛ¹(x−s)φ''(x)dx = φ(s) using φ(1)=φ'(1)=0 — pure IBP of smooth fns).
   (b) h := u − Kw has ∫ h·φₖ'' = 0 ∀k.  (c) ψₖ := φₖ'' = (k+2)(k+1)tᵏ −
   2(k+3)(k+2)tᵏ⁺¹ + (k+4)(k+3)tᵏ⁺² is triangular with nonzero leading coeff ⇒
   monomials tᵐ (m≥2) ∈ span{1, t, ψ₀..ψ_{m−2}} by induction.  (d) pick a,b with
   h₀ := h − a − b·t ⊥ {1,t} (2×2 Gram solvable); affine ⊥ ψₖ (boundary IBP);
   ⇒ ∫ h₀·p = 0 for ALL monomials ⇒ (Bernstein/Weierstrass + continuous dense in L²)
   h₀ = 0 a.e.  Corollaries: uniqueness of w given u; (affine, 0) ∈ V; kernel of the
   beam = affine.

2. COMPACTNESS of embed (Rellich, no weak topology): embed = [(u,w) ↦ u − Kw]
   (range in 2-dim affine span ⇒ finite rank, via brick 1) + K∘proj₂.
   K is a norm-limit of finite-rank operators: partition [0,1] into n cells,
   K_n f x := Σᵢ 1_{cellᵢ}(x)·(Kf)(xᵢ); ‖K−K_n‖ ≤ 1/n since the kernel is 1-Lipschitz
   in x, L²-uniformly in s.  Use `isCompactOperator_of_tendsto`,
   `TauCeti.isCompactOperator_of_finiteDimensional_range` (ForTauCeti FiniteRankCompact).
   Then R := embed∘embed† (formOperator=id ⇒ resolvent R = j∘j*) is compact self-adjoint
   injective.  Bridge to `SequentiallyCompactEmbedding` only if the assembly needs it.

3. SPECTRUM: realSpectrum(beam B) ⊆ {0} ∪ {β⁴ : characteristic β = 0} ⊆ {0} ∪ (500,∞).
   Operator algebra: λ ∈ realSpectrum(B) ∧ λ ≠ eigenvalue ⇒ contradiction via
   S := (1 − (1+λ)R)⁻¹ (Fredholm: `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`,
   Mathlib Compact/FredholmAlternative.lean): u := R∘S∘f solves (B−λ)u = f; left inverse
   by S,R commuting.  Eigenvector Ru = μu (μ=(1+λ)⁻¹≠0) ⇒ u ∈ range R = dom(B+1),
   Bu = λu.  So positive spectrum ⊆ positive point spectrum, then brick 4 classifies.
   0 ∈ spectrum via the affine kernel; nonnegativity from bendingEnergy.

4. EIGENMODE REGULARITY + CLASSIFICATION: Bu = λu (λ>0) ⇒ weak form
   ∀v∈V: ⟨u₂,v₂⟩ = λ⟨u,v⟩ (from `variational_identity` with formOperator=id).
   (a) Test with (φₖ, φₖ'') ⇒ u₂'' = λu weakly ⇒ brick 1 twice ⇒ u has a C³
   representative with AC third derivative, u'''' = λu, then continuity bootstraps to
   C⁴ classical.  (b) Natural BCs: v := cubic polynomials (arbitrary endpoint jet, in V);
   classical IBP leaves boundary form [u''v̄' − u'''v̄]₀¹ = 0 ∀cubic ⇒ the four free BCs.
   (c) ODE uniqueness: real functions, u'''' = β⁴u with jet matching a `mode` at 0
   (jet map (a,b,c,d)↦jet invertible for β≠0: u(0)=a+c, u'(0)=β(b+d), u''(0)=β²(c−a),
   u'''(0)=β³(d−b)); difference has zero jet, Gronwall on E = d²+d'²+d''²+d'''²
   (`norm_le_gronwallBound_of_norm_deriv_right_le`) ⇒ 0.  Apply to Re u, Im u.
   ⇒ u is a mode with FreeBoundary and nontrivial coefficients ⇒
   `characteristic_eq_zero_of_freeBoundary` ⇒ λ = β⁴ root ⇒ > 500.

## STATUS 2026-08-07 (mid-campaign)

DONE, pushed, axiom-clean:
- `ForTauCeti/MeasureTheory/IntervalWeakSecondDeriv.lean` (brick 1: representation theorem
  `eq_affine_add_secondPrimitive_of_forall_integral_bumpD2`, moment density, bump calculus,
  `unitIocMeasure`+`secondPrimitive` exposed with `_def` lemmas, kernel eval lemmas,
  probability instance).  cff73418.
- `DavisKahan/Sources/DavisKahan1970/Section9/FreeBeamModeUniqueness.lean` (brick 4c:
  `exists_mode_eqOn_of_fourth_deriv` global + `_within` interval version).  a87426fc, a49005a7.
- `ForTauCeti/MeasureTheory/IntervalSecondPrimitiveCompact.lean` (brick 2:
  `secondPrimitiveCLM`, `isCompactOperator_secondPrimitiveCLM`; also `secondPrimitiveEval`
  functionals, `integral_norm_coeFn_le` L¹≤L², `coeFn_lp_finsetSum`).  7ec36919.
- `ForTauCeti/MeasureTheory/IntervalSecondPrimitiveDeriv.lean` (brick 4a:
  `hasDerivAt_secondPrimitive` = firstPrimitive, `hasDerivWithinAt_firstPrimitive_of_continuous`
  FTC within `[0,1]`, `firstPrimitive_congr_ae/_eq_intervalIntegral`).  56cb7a84.

FURTHER DONE 2026-08-07 (later), all pushed, axiom-clean:
- `DavisKahan/SpectralTheory/FormMethod/BeamFormSpace.lean`: V inhabited, coercive +
  shifted form data, `beamOperator` self-adjoint nonneg, `isCompactOperator_beamEmbed`,
  `denseRange_beamEmbed`, `beamOneLp/beamIdLp`, `contToLp`, `pairingCLM`, `contPair_mem`.
- `DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean`: variational eigen-identity,
  affine kernel both directions (`beamOperator_affine_mem_and_zero`,
  `exists_affine_of_beamOperator_eq_zero`), `eigen_pairing_integral`, cubic test family,
  `boundary_form_eq_zero`, **`exists_characteristic_of_eigen`** (THE BOOTSTRAP) and
  **`eigenvalue_gt_five_hundred`** (alpha_3 > 500 for the actual operator).

REMAINING (design fixed in item 4 below; mechanical-to-medium):
- Fredholm bridge: realSpectrum(beamOperator) ⊆ {0} ∪ {β⁴} ⊆ {0} ∪ (500,∞).  All
  ingredients present: R := beamCoerciveFormData.resolvent = j∘j† compact
  (isCompactOperator_beamEmbed + comp lemmas), Mathlib Fredholm alternative, the eigen
  classification above, S := Ring.inverse (1 − (1+λ)R) commutation algebra, and the
  realResolventSet two-sided-inverse witness RS.  Negative λ and λ ∈ (0,500] both
  excluded because {β⁴} ⊆ (500,∞) and eigenvalues of R are {1} ∪ {(1+β⁴)⁻¹}.
- Then wire DK-9-model: build `FreeBeamFiniteDataCertificate` etc. from this operator
  (moments↔integrals identification; the `RepresentsFreeBeamProblem`-style Prop can now
  be stated concretely against `beamOperator`), replace Section9Analytic sorries or
  retire that skeleton in favour of the Model namespace, and update the census.

OLD PLAN (kept for the detailed designs referenced above):
1. BeamFormSpace: H := Lp ℂ 2 unitIocMeasure, P := WithLp 2 (H × H); constraint functionals
   pairingCLM (W ↦ ∫ ⇑W·g for continuous g, mkContinuous with sup-bound like
   `secondPrimitiveEval`); V := ⨅ k, ker(constraint k) closed ⇒ complete; embed := fst∘subtypeL.
   - embed_injective: u = 0 ⇒ ∫ w·bumpₖ = 0 ∀k ⇒ moments of w·t²(1−t)² all vanish ⇒
     `ae_eq_zero_of_forall_integral_pow_eq_zero` ⇒ w =ᵐ 0 (t²(1−t)² ≠ 0 a.e.).
   - dense range: pairs (real polynomial q, q'') ∈ V by two IBPs against the bump family
     (bump+bumpD1 vanish at both endpoints; `Polynomial.hasDerivAt`); then bounded-continuous
     density as in File 1's Weierstrass argument.  adjoint_injective from dense range.
   - CoerciveFormData: formOperator := 1, coercivity 1, ShiftedBeamFormData with
     bendingEnergy p := ‖p.2‖², decomposition via WithLp prod inner + Submodule.coe_inner.
   - Compact embed: embed = (finite-rank part: range ⊆ span{toLp 1, toLp t} by brick 1)
     + secondPrimitiveCLM ∘ sndCLM; resolvent R = j∘j† (formOperator=1 ⇒ Ring.inverse 1 = 1)
     compact via comp lemmas.  ‖j‖ ≤ 1.
2. Kernel identification: (affine,0) ∈ V (moments ∫ψₖ = ∫tψₖ = 0); j†(affine) = (affine,0) by
   ext_inner; R(affine) = affine ⇒ affine ∈ dom, B(affine) = 0.  Conversely Bu = 0 ⇒
   bendingEnergy = 0 (`beam_quadratic_eq_bendingEnergy`) ⇒ w = 0 ⇒ u affine (brick 1, w=0).
   Kernel = span{toLp 1, toLp id}, dim 2 (1,t independent via moments).
3. Bootstrap (eigen classification): B u = λu, λ > 0, u ≠ 0 ⇒ λ = β⁴, characteristic β = 0:
   variational identity gives (†) ∀(v₁,v₂) ∈ V: ⟪p₂, v₂⟫ = λ⟪u, v₁⟫ (p = (u,p₂) ∈ V).
   Test with (bumpₖ, ψₖ) + conjugate (λ real) ⇒ (p₂, λu) in bump relation ⇒ brick 1 twice ⇒
   continuous reps ū = a+bt+K w̄₂, w̄₂ = c+dt+λK ū (exact equations); chains via brick 4a
   (global K' = firstPrimitive; FTC within Icc); mode classification `_within` on Re/Im with
   β := λ^(1/4) (rpow, β⁴ = λ).  Natural BCs: test (†) with Hermite cubic pairs
   (q,q'') ∈ V, integrate by parts classically (interior two-sided derivatives via
   `HasDerivWithinAt.hasDerivAt (Icc_mem_nhds)`) ⇒ boundary form [w̄₂q′ − ū₃q]₀¹ = 0 for the
   four Hermite cubics q₁=(1−t)²(1+2t), q₂=t(1−t)², q₃=t²(3−2t), q₄=t²(t−1) ⇒
   w̄₂(0)=w̄₂(1)=ū₃(0)=ū₃(1)=0 ⇒ FreeBoundary for the mode ⇒
   `characteristic_eq_zero_of_freeBoundary` (u ≠ 0 gives a nontrivial Re or Im part).
4. Spectrum: realSpectrum(B) ⊆ {0} ∪ {β⁴ : characteristic β = 0} ⊆ {0} ∪ (500,∞) (last step
   `Classical.five_hundred_lt_pow_four_of_characteristic_eq_zero`).  For λ outside the set:
   1+λ ≠ ... if 1+λ = 0 then I − (1+λ)R = I invertible; else (1+λ)⁻¹ ∉ spectrum(R): R compact
   (⇒ Fredholm `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`), eigenvalues μ ≠ 0 of R
   satisfy B x = (μ⁻¹−1)x with μ⁻¹−1 ≥ 0 (B nonneg) ⇒ ∈ {0} ∪ β⁴-set (bootstrap) ⇒
   μ ∈ {1} ∪ {(1+β⁴)⁻¹} ∌ (1+λ)⁻¹.  Then S := inverse(I − (1+λ)R) commutes with R and
   RS is the two-sided inverse of B − λ demanded by `realResolventSet` ((B−λ)(RSf) = f via
   (B+1)Ry = y; left leg via u = Rx and S(I−(1+λ)R)x = x).
5. Wire into DK-9-model row: the operator + kernel + spectrum facts replace the
   `thirdEigenvalue`/`RepresentsFreeBeamProblem` sorries' role; build
   `FreeBeamFiniteDataCertificate` with third_eigenvalue := any spectral point... NO — take
   third_eigenvalue := 500.5-free formulation: the certificate only *stores* a scalar; derive
   it from the spectrum theorem applied to the model.  Then census updates.

## Files

- ForTauCeti/MeasureTheory/IntervalWeakSecondDeriv.lean  (brick 1 + K def + brick 2 core)
  [generic; glob-built, warningAsError]
- ForTauCeti/Analysis/Calculus/FourthOrderODEUniqueness.lean  (brick 4c, pure ODE)
- DavisKahan/SpectralTheory/FormMethod/BeamFormSpace.lean  (V, CoerciveFormData/
  ShiftedBeamFormData instances, kernel identification)
- DavisKahan/SpectralTheory/FormMethod/BeamSpectrum.lean  (bricks 3 + 4 assembly)
- then: Section9 model wiring (FreeBeamFiniteDataCertificate from the model), and #51.

Perturbation for #51: Ā := beamOperator.addBounded (ε·M_t), M_t = mulLp with clamped
symbol max 0 (min t 1) (a.e.-equal to t on Ioc 0 1); ‖M_t‖ ≤ 1.  Trial space = affine
kernel.  Residual data = moments (TrialSubspace.lean, proved) — needs the integration
lemma identifying CenteredAffine.inner/tInner/tSqInner with actual L² integrals
(EASY, leave for smaller model, as with census/markdown regeneration chores).

## Easy parts explicitly left for a smaller model

- Moments↔integrals identification (∫₀¹ tⁿ, products of affine × t-weights).
- Census row updates + regenerate .md after each theorem lands.
- `SequentiallyCompactEmbedding` bridge lemma if wanted for the record.
- DK-3.2-cor promotion (#54), DK-10.1 note, S2-tan-two-theta next_action fix (#55).
