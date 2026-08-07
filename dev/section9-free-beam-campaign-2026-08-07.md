# Section 9 free-beam campaign (DK-9-model → DK-9.x): design and status

Written 2026-08-07 (Fable 5).  Edward's directive: hardest parts first; leave easy parts
for a smaller model.  This file records the design so any session can continue.

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
