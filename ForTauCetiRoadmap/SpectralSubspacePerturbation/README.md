# Roadmap: spectral subspace perturbation — Sylvester equations, the Rosenblum theorem, and the Davis–Kahan sin Θ theorems

Perturbation theory for self-adjoint operators asks how an invariant subspace moves
when the operator does.  Davis and Kahan (1970) answered in the form the subject has
used since: the displacement of a spectral subspace is the operator `sin Θ` built
from the two orthogonal projections, and a spectral gap `δ` between the parts of the
spectrum forces `δ · ‖sin Θ‖ ≤ ‖B − A‖` — in the operator norm, the Frobenius norm,
and every unitarily invariant norm, with **constant one** under interval/exterior or
ordered separation and the **sharp constant `π/2`** under arbitrary two-sided
separation.  The engine is the Sylvester equation `A X − X B = C`: spectral
separation makes it uniquely solvable with an a-priori bound, and the `sin Θ`
theorems are that bound read through projection geometry.  Its qualitative limit is
**Rosenblum's theorem** (an operator intertwining two self-adjoint operators with
disjoint spectra is zero — for unbounded operators, the case that matters); its
statistical variant (**Yu–Wang–Samworth**) moves the gap hypothesis from the
perturbed spectrum to the unperturbed one, which is what a random sample covariance
allows.  Mathlib has the static operator-theory stack but none of this layer: no
operator angles, no Sylvester equations, no spectral-subspace perturbation theory,
no statistical variant.

The goal is to **build the reusable theory of these objects**, not to race to the
named theorems.  The bar for "done": a researcher in operator theory or statistics
finds Sylvester equations with solvability and a-priori estimates at every relevant
generality (bounded and domain-aware, operator norm through arbitrary unitarily
invariant norms, constant one and `π/2`), the `sin Θ` family as consequences of that
developed theory, and the statistical variant stated the way its consumers use it.
A PR that proves a headline theorem but leaves the surrounding objects without their
basic API is not yet what we want.  This roadmap is the **endpoint of the
six-roadmap operator-theory program**: it consumes all four of
FiniteDimensionalOperators, MajorizationAndAngles, OperatorIdeals, and
SpectralTheory (see *Dependency ordering*).  That transitive depth is the honest
cost of submitting Davis–Kahan as reusable mathematics rather than as one paper's
formalization — every object the theorems quantify over must exist first.

Suggested homes (paper-facing correspondence material lives in a source-facing
layer and does not dictate the generic namespaces; `Suggested.lean` gives
representative prototype signatures — the markdown stays definitive):

```text
TauCeti/Analysis/Fourier/HaagerupZsido/
TauCeti/Analysis/Operator/Sylvester/
TauCeti/Analysis/Operator/Perturbation/
TauCeti/Analysis/InnerProductSpace/OperatorAngle/   (shared with MajorizationAndAngles)
```

## Generality bar (decide these up front; do not silently specialize)

- **Scalar fields, rectangular shapes.**  Algebraic and finite statements over
  `[RCLike 𝕜]`; complex-calculus results over `ℂ` with explicit real descent.  The
  `π/2` bound holds verbatim over `ℝ` and `ℂ` — the real case a theorem (via the
  doubled-phase certificate, Part B), not a remark.  Estimates run between two
  different Hilbert spaces with independent universes; endomorphisms are diagonal.
- **Unbounded statements are canonical.**  The domain-aware forms — the Sylvester
  equation `SylvesterEquation A B X C` on `LinearPMap` with domain transport as
  data, spectra via the SpectralTheory roadmap's `resolventSet` complement — are
  primary; bounded operators enter through `T.toLinearMap.toPMap ⊤`, finite
  dimension through restriction.  Bounded/finite theorems are *specializations*.
- **Norms: one statement per family.**  State results for an arbitrary
  (rectangular) unitarily invariant seminorm — subadditive, absolutely homogeneous,
  two-sided unitarily invariant, definiteness deliberately unbundled — with
  operator, Frobenius, Ky Fan, Schatten forms as instantiations.  Ky Fan prefixes
  plus Fan dominance is the pinned lifting route.
- **Gap predicates and angles stay distinct.**  Ordered (`λ + δ ≤ μ`),
  interval/exterior (one spectrum in `[a,b]`, the other outside `(a−δ, b+δ)`), and
  pairwise (`δ ≤ |λ − μ|`) separation carry constants one, one, `π/2`; none is
  silently strengthened, and `tan 2Θ` needs *ordered* internal separation
  (interlacing spectra satisfy pairwise separation while an off-diagonal
  perturbation produces a quarter turn).  One interval/exterior gap controls the
  directed sine `P_{V^⊥} ∘ P_U` in every unitarily invariant norm; the symmetric
  sine `|P_U − P_V|` needs the gap in both orientations (Proposition 6.1); only the
  operator norm erases the difference, under equal ranks.  Both angles are API.
- **Rosenblum without a Borel functional calculus.**  Both Cayley spectra contain
  `1` once both operators are unbounded, so no continuous symbol separates them —
  but `1` is a **null point for every diagonal spectral measure**, so continuous
  symbols damped at `1` separate in the limit and dominated convergence finishes.
  A reviewer should check the null claim rather than the proof: if it failed, the
  argument would be wrong, not merely different.
- **The constant `π/2`, honestly.**  Part A's kernel *attains* `π/2`; that no
  admissible kernel beats it is a literature citation, not a target, and module
  documentation must say so.  What *is* proved in Lean: every **real, undoubled**
  interpolation certificate for the two-by-two obstruction data has coefficient
  mass at least `5/3 > π/2` — so the real-field `π/2` theorem goes through the
  doubled-phase certificate, never a real kernel.
- **Kernel conventions (Part A).**  The real kernel `ℝ → ℝ` and the complex kernel
  `ℝ → ℂ` (`k = −i·k_ℝ`) **both stay**: mass and positivity use the real one, the
  Fourier identity states cleanly with the complex one.  The Laplace transform
  integrates over `Set.Ioi 0` (`integrableOn_Ici_iff_integrableOn_Ioi` bridges).
  The Fourier identity is a bare integral against `exp(i t x)` — the form an
  operator is substituted into — with an explicit bridge to the `2π`-normalized `𝓕`.
- **Population gaps in the statistical variant.**  Part D's hypothesis is a gap in
  the spectrum of **one** designated (population) operator, the perturbed block
  selected by *corresponding ordered eigenvalue indices*, not an arbitrary reducing
  subspace.  Pinned so nobody "simplifies" it back to a two-sided gap.

## What Mathlib already has (consume, and connect to)

- **For Part A:** `𝓕` with inversion (⚠ the `2π` convention), the Bochner integral,
  `Integrable`, `ExpDecay`, Poisson summation, `Real.tanh`, `Analysis/PSeries`.
- **Operators and geometry:** `ContinuousLinearMap`, adjoints, `IsSelfAdjoint`,
  `LinearMap.IsSymmetric`, `spectrum`, `cfcHom` of a star-normal element, Urysohn's
  lemma; `LinearPMap` with `adjoint` and `IsSelfAdjoint`;
  `Submodule.starProjection`, `OrthonormalBasis`,
  `LinearMap.IsSymmetric.eigenvectorBasis`/`eigenvalues`, `Module.finrank`,
  `WithLp 2 (E × F)`, `lp`.
- The spectral predicates, norms, angle operators, Hilbert–Schmidt space, and
  unbounded spectral theory come from the sibling roadmaps itemized under
  *Dependency ordering*.  Before implementing, search Zulip and open Mathlib PRs
  for newly landed overlap; follow what is in motion rather than duplicating it.

Everything below is absent upstream.  Four parts, in submission order:

## Part A — the Haagerup–Zsidó kernel and its Fourier transform

**Topic T12 of the candidate design** — independently submittable, no prerequisites.

This part exists for a constant, and says so.  There is an explicit integrable
`k : ℝ → ℂ` whose Fourier integral reproduces the reciprocal on the whole exterior
region `1 ≤ |x|`, and whose total mass is exactly `π/2`.  Any kernel with the first
property yields, on substituting a separated pair of self-adjoint operators for `x`,
a Sylvester solution bound with constant `‖k‖₁`; a kernel with the right transform
and worse mass proves a weaker Part B, so both halves — identity and mass — are
milestones.  The mathematics is due to Haagerup and Zsidó, specified intrinsically.

**Objects.**  A four-definition chain: `weight y = tanh (π y / 2)`;
`weightLaplaceTransform t = ∫ y in Ioi 0, weight y · e^{−|t| y}`;
`realKernel t = (sin t / 2) · weightLaplaceTransform t`;
`reciprocalKernel t = −i · realKernel t` (the rotation lands the transform on `1/x`).

**API to develop.**
- Parity, nonnegativity of the weight and its transform, continuity, measurability;
  the kernel is odd, so the two-sided identity follows from `1 ≤ x` by reflection.
- The scalar integral layer, each piece independently reusable: the two-sided
  exponential (oscillatory Laplace transform, its `𝓕`, `=o[cocompact ℝ]` decay); the
  closed-form Laplace transform of `|sin|` by periodic decomposition; Poisson
  summation against the Cauchy kernel and the odd-pole expansion
  `weight y / y = (4/π) ∑' n, (y² + (2n+1)²)⁻¹`; elementary Cauchy-type integrals.
- One **product-integrability certificate** on `Ioi 0 × ℝ` licensing both the
  Tonelli exchange in the mass computation and the later Fourier exchange; the
  generic lemmas (absolute-sine periodicity, even-function integrability via
  `Ioi 0`) placed generically, so a reviewer can take them without the topic.

**Milestone A1 — the exterior identity and the exact mass.**

```lean
theorem reciprocalKernel_fourier (x : ℝ) (hx : 1 ≤ |x|) :
    (∫ t : ℝ, reciprocalKernel t *
        Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))) = 1 / (x : ℂ)

theorem integral_norm_reciprocalKernel :
    (∫ t : ℝ, ‖reciprocalKernel t‖) = Real.pi / 2
```

The mass is not an estimate: Tonelli gives
`½ ∫_{y>0} weight y · (∫ |sin t| e^{−y|t|} dt) dy`, the inner integral is
closed-form, and its product with `tanh(π y/2)` collapses — **the weight is chosen
to make that cancellation exact** — leaving `∫_{y>0} (1+y²)⁻¹ = π/2`.  That is the
one sentence a reader should take away about why `tanh(π y/2)` appears at all.

**Milestone A2 — the normalization bridge** to Mathlib's `𝓕` (per the generality
bar), so users mixing the two conventions have a lemma, not a warning.
**Acceptance examples**: the identity at a concrete `x`; the mass bounding one
concrete convolution; documentation stating `π/2` is attained and minimality
cited, not proved (the Lean-proved obstruction is Part B's `5/3`).

## Part B — Sylvester equations and the Rosenblum theorem

**Topic T16 of the candidate design** — the hinge: consumes Part A and all four
external roadmaps; Part C consumes it.

The headline is qualitative — an operator intertwining two self-adjoint operators
with **disjoint** spectra is zero, `A` and `B` unbounded.  The quantitative
companions — a-priori bounds on `‖X‖` when the spectra are **separated** by `δ` —
are what Part C actually consumes.

**Objects.**  The Sylvester operator `X ↦ A X − X B` on rectangular maps; the gap
taxonomy of the generality bar; the domain-aware `SylvesterEquation` on `LinearPMap`
(consumed from SpectralTheory, which owns the transport statement and excludes the
estimates to here); the **Sylvester flow** `W t Z = U_A(t) ∘ Z ∘ U_B(t)⋆` on the
Hilbert–Schmidt space.

**API to develop.**
- Finite core: injectivity under positive separation, the canonical eigenbasis
  solution, the coordinate equation `(αᵢ − βⱼ) Xᵢⱼ = Cᵢⱼ`.
- **Dimension-free operator-norm bounds**, integral-free, on arbitrary Hilbert
  spaces, both orientations `A X ± X B = Y`: the coercive (Lyapunov) form
  `‖X‖ ≤ ‖Y‖ / (2δ)` and the separated form `‖X‖ ≤ ‖Y‖ / g`, by shifting both
  operators to the midpoint and solving for `‖X‖`; the operator-level Lax–Milgram
  lemma making a coercive operator a unit.
- **Interval/exterior separation, constant one, every rectangular unitarily
  invariant norm**: polar absorption (shift the interval to its midpoint, replace
  the exterior operator by its modulus, absorb the polar partial isometry into the
  unknown), reverse orientation by adjoint transport.
- **Pairwise separation, constant `π/2`**: the analytic root is a *simultaneous
  Ky Fan prefix estimate* — one finite family of left/right unitaries realizing the
  reciprocal multiplier on every coordinate matrix unit at once with mass at most
  `π/2`, by finite Fourier interpolation against Part A's kernel (the `π/2` is
  Part A's mass, not an unspecified constant); Fan dominance lifts it to every
  unitarily invariant norm, orbit convexity packages the scaled solution as a
  barycenter of the defect's unitary orbit, and the **Frobenius norm loses
  nothing** (constant one, dividing the coordinate equation and summing squares).
  The interpolation layer is internal, not public surface.
- **The flow route to the unbounded theory**: the flow is a one-parameter unitary
  group on the Hilbert–Schmidt space — unitarity from the OperatorIdeals
  conjugation; strong continuity is the analytic content (the columns must go to
  zero *together*; the energy split is carried in `ℝ≥0∞` so no finiteness side
  conditions appear).  Stone's theorem hands back a self-adjoint generator,
  **identified** — not defined, or nothing about Sylvester equations would be
  proved — as `Z ↦ A Z − Z B`, domain membership a conclusion; separated spectra
  force a generator gap at every Hilbert–Schmidt vector.  Unbounded endpoints
  across a pairwise gap `δ`: `δ · ‖X‖₂ ≤ ‖C‖₂` (constant one) and
  `δ · ‖X‖ ≤ (π/2) · ‖C‖` for bounded solutions of the domain-aware equation.

**Milestone B1 — the a-priori bounds.**

```lean
theorem opNorm_le_div_of_comp_sub_comp_eq
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric) (hB : (B : F →ₗ[𝕜] F).IsSymmetric)
    {c g : ℝ} (hg : 0 < g)
    (hAc : ∀ x, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hBc : ∀ v, RCLike.re ⟪B v, v⟫_𝕜 ≤ c * ‖v‖ ^ 2)
    (hXY : A ∘L X - X ∘L B = Y) : ‖X‖ ≤ ‖Y‖ / g

theorem uiNorm_sylvester_le_of_spectralDistance
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F) … (hδ : 0 < δ)
    (hgap : SpectraSeparated A ⊤ B ⊤ δ) (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ (Real.pi / 2) * N C
```

**Milestone B2 — Rosenblum's theorem** (`A`, `B` self-adjoint `LinearPMap`s):

```lean
theorem eq_zero_of_intertwines_of_disjoint_spectrum
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {X : F →L[ℂ] E}
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y))
    (hdisj : Disjoint (spectrum A) (spectrum B)) : X = 0
```

**Acceptance examples.**  The two-by-two obstruction data (`α = (−1,1)`, `β = (0,2)`,
gap one) is admissible yet forces mass `≥ 5/3` on every real undoubled certificate;
a bounded pair as total partial maps recovers bounded uniqueness; the coercive bound
on a concrete multiplication pair.

## Part C — the Davis–Kahan sin Θ theorems

**Topic T17 of the candidate design** — consumes Part B; the acceptance suite is
Davis–Kahan Part III.

The `sin Θ` family is Part B read through projection geometry.  Two statement
shapes, both API: the **residual** form (the numerical analyst's — an approximate
invariant subspace with residual `R = A X − X M` is tilted by at most `‖R‖/δ`) and
the **perturbation** form (the operator theorist's — invariant subspaces of `A` and
`B` are tilted by at most `‖B − A‖/δ`), each for every relevant unitarily invariant
norm, with the interval, spectral-projector, and concrete-norm corollaries.

**Objects.**  Consumed from MajorizationAndAngles: `sinThetaMap U V = P_{V^⊥} ∘ P_U`,
the symmetric sine `|P_U − P_V|`, principal angles.  Built here: the trial-map layer
— the compression `X⋆ A X` along a trial map (isometric or not), its residual, the
Ritz residual (Rayleigh–Ritz makes it Frobenius-minimal), sine and cosine embeddings
with their singular-value identifications; reduced extensions (a block operator
extended by a scalar on the complement — the device turning spectral hypotheses into
coercivity); graph subspaces, projection and gap formulas, angular operators.

**API to develop.**
- **Dimension-free first.**  On arbitrary Hilbert spaces, from B1 alone: the directed
  bound `‖P_V ∘ P_U‖ ≤ ‖B − A‖ / g` for invariant subspaces with quadratic-form
  separation, and its projector-difference companions.
- **Finite spectral forms.**  Spectral coercivity bridges convert eigenvalue
  hypotheses into form bounds, giving: the residual theorem in every rectangular
  unitarily invariant norm; the perturbation theorem in every square one (transport
  across the subspace's isometric inclusion); canonical spectral-subspace and
  spectral-projector statements with no eigenbasis in the API; the equal-rank bridge
  `‖P_U − P_V‖ = ‖sinThetaMap U V‖`; Frobenius and Ky Fan corollaries; the `π/2`
  two-sided form; the symmetric sharp theorem under the two-orientation gap.
- **Double-angle and tangent theory.**  Davis's `sin 2θ` in per-eigenvector product
  and angle forms; the one-sided `sin 2Θ` map `2 P_{U^⊥} P_V P_U` in unitarily
  invariant norms; tangent estimates on the acute branch from Ritz residuals
  (equal-rank and lower-rank); the sharp `tan 2θ` with vanishing-pinch (off-diagonal)
  hypotheses and the quarter-turn conclusion, under *ordered* internal separation.
- **Domain-aware forms.**  The unbounded `sin Θ` surface over SpectralTheory's
  closed-operator layer: residual identities extended from a graph core to the full
  domain; common-domain and common-core variants; bounded-residual and lower-frame
  formulations; interval/exterior and pairwise-gap forms in the supported unitarily
  invariant norms, the Hilbert–Schmidt case through Part B's flow; the bounded and
  finite theorems as specializations.
- **Graph subspaces and Riccati.**  The graph-reduction/Riccati equivalence (a graph
  subspace is invariant iff its angular operator solves the Riccati equation);
  existence, bounds, and uniqueness for contractive solutions under the gaps above.

**Milestone C1 — the perturbation family** (with the canonical spectral-projector
corollary `δ · ‖P_{spec A [a,b]} − P_{spec B [a,b]}‖ ≤ ‖B − A‖` under equal ranks):

```lean
theorem sinTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hU : ∀ x ∈ U, A x ∈ U) (hV : ∀ x ∈ V, B x ∈ V)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hAin : SpectrumIn A U (Set.Icc a b))
    (hBout : SpectrumIn B Vᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * N (sinThetaMap U V) ≤ N (B - A)
```

**Milestone C2 — the two-sided `π/2` form**: under `SpectraSeparated A U B Vᗮ δ`
alone, `δ * N (sinThetaMap U V) ≤ (π/2) * N (B − A)`.  **Milestone C3 — the
domain-aware `sin Θ` theorem**, in the canonical unbounded form of the generality
bar, with the finite statements as its specializations.

**Acceptance suite — Davis–Kahan Part III.**  A source-facing layer recording the
correspondence between the paper's statements and the reusable declarations, in real
and complex forms: the generalized (trial-map) and ordinary `sin Θ` theorems;
equal-rank and lower-rank Ritz-residual `tan Θ`; `sin 2Θ` in unitarily invariant
norms; the sharp operator-norm `tan 2Θ` with the quarter-turn conclusion; the
projector-difference companions; the paper's printed counterexample and sharpness
statements; equality models of arbitrary finite multiplicity; explicit statements of
what is *not* claimed.  Cross-checks between projection, singular-value,
column-energy, and tensor formulations on small matrix models complete it.

## Part D — the Yu–Wang–Samworth statistical variant

**Topic T18 of the candidate design** — consumes Part C; a leaf.

Davis–Kahan hypothesizes a gap in the spectrum of one of the two operators — in
practice the perturbed one.  That is the wrong shape for statistics: the perturbed
operator is a *sample* covariance and its spectrum is random; what one can assume is
a gap in the **population** spectrum.  Yu–Wang–Samworth is the variant stated that
way — the one thing a reader coming from Part C will not expect — and the substance
of this part is exactly that hypothesis change.  Its probabilistic inputs live in
the MatrixStatistics roadmap; this part is the deterministic inequality they
compose with.

**Objects.**  `PopulationGap A U Δ` (the population operator's internal gap across
the selected block); `CorrespondingEigenblock` (blocks of the two operators selected
by the *same ordered eigenvalue indices*); the Frobenius sine distance
`sinThetaFrobenius U V`; the residual columns `(S − λⱼ(T)) uⱼ(S)` in the population
eigenbasis; for rectangular data, left and right singular subspaces via the Gram
operators and the Hermitian dilation `[[0, A⋆], [A, 0]]` on `WithLp 2 (E × F)`.

**API to develop.**
- The **complement identity**: the Frobenius sine of two equally indexed eigenblocks
  equals the square root of the cross-block overlap sum
  (`‖V₁ᵀ V̂‖_F = ‖sin Θ(V̂, V)‖_F`).  Every bound of the paper is proved as
  cross-block energy and read back as an angle; this bridge is public API.
- The **residual sandwich**, for an **arbitrary index block** (leading-only would
  not cover the interval case): `Δ² · overlap ≤ ∑ⱼ ‖Rⱼ‖²` from the population gap
  below, `∑ⱼ ‖Rⱼ‖² ≤ 4 ‖S − T‖²_F` above (each column splits into a perturbation
  piece and a Hoffman–Wielandt eigenvalue piece); the operator-norm branch
  `∑_{j∈s} ‖Rⱼ‖² ≤ 4 |s| ε²` via Weyl.
- The **aligned-basis (Procrustes) surface**: orthonormal bases of the two blocks
  with `√(∑ ‖vᵢ − uᵢ‖²) ≤ √2 · ‖sin Θ‖_F` — the usable form when eigenbases are
  determined only up to rotation, i.e. in every application.
- The **singular-subspace transfer**: the symmetric theorem applied to `A⋆A` and
  `A A⋆`, the Gram perturbation bounded by `(‖Â‖ + ‖A‖) · ‖Â − A‖`, the
  Hermitian-dilation form controlling both sides at once (its arbitrary-set gap
  supports `π/2`, not constant one).

**Milestone D1 — the population-gap theorem and its single-vector form.**

```lean
theorem yuWangSamworth_sinTheta_le … (hcorr : CorrespondingEigenblock hA hB U V)
    (hrank : finrank 𝕜 U = d) {Δ : ℝ} (hΔ : 0 < Δ) (hgap : PopulationGap A U Δ) :
    sinThetaFrobenius U V ≤
      2 * min (Real.sqrt d * ‖B - A‖) (frobeniusNorm (B - A)) / Δ

theorem yuWangSamworth_eigenvector_le … :
    ∃ c : 𝕜, ‖c‖ = 1 ∧ ‖c • v - u‖ ≤ 2 * Real.sqrt 2 * ‖B - A‖ / Δ
```

**Acceptance examples.**  A spiked model where the sample gap closes but the
population gap does not; consistency — when a two-sided gap does hold, Part C's
constant-one bound is stronger; a non-square matrix through the Gram route.  Cite
and cross-check, never vendor, the related endpoints in
`YuanheZ/lean-stat-learning-theory` and `facebookresearch/atlas-lean` (the latter
statement comparison only; incompatible repository terms).

## Dependency ordering

**Internal.**  Part A is independent and independently submittable — this roadmap's
cheapest first contact with review.  Part B consumes Part A (the constant); Part C
consumes Part B; Part D consumes Part C.  Within Part B the finite core, the
dimension-free bounds, and the flow can proceed in parallel once their external
inputs exist; within Part C the dimension-free layer precedes the finite spectral
forms, and the domain-aware forms come last.

**External.**  FiniteDimensionalOperators: spectral subspaces, gap predicates,
modulus, singular values (Parts B–D).  MajorizationAndAngles: the unitarily
invariant norm structures with Fan dominance, principal angles, the angle
operators, aligned bases, Weyl perturbation (Parts B–D).  OperatorIdeals: the
Hilbert–Schmidt space, energy calculus, unitary conjugation (Parts B–C).
SpectralTheory: unitary groups and Stone, the `LinearPMap` resolvent/spectrum layer
with the Cayley transform and intertwining chain, the spectral measure and support,
the domain-aware `SylvesterEquation` (Parts B–C).  Nothing here waits on
MatrixStatistics.  The Tau Ceti OneParameterSemigroups roadmap pins the same
representation decision (generators as `LinearPMap`); Part B's flow material builds
against the SpectralTheory unitary-group API, which coordinates with that roadmap.

## References

- C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), 1–46 — the principal worked source.
- C. Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal. Appl.
  6 (1963), 159–173 — the `sin 2θ` theorem.
- M. Rosenblum, *On the operator equation BX − XA = Q*, Duke Math. J. 23 (1956),
  263–269.
- R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and
  solution of linear operator equations*, Linear Algebra Appl. 52/53 (1983), 45–67.
- U. Haagerup and L. Zsidó — the extremal kernel attaining `π/2`; followed through
  the Albeverio–Makarov–Motovilov reconstruction of the `π/2` provenance chain (see
  the provenance section).
- R. Bhatia, *Matrix Analysis*, GTM 169, Ch. VII.2 — Part B's separated bound is
  the half-line case of Theorem VII.2.3 by an integral-free proof.
- Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis–Kahan theorem for
  statisticians*, Biometrika 102 (2015), 315–323 (arXiv 2014).

## Provenance and decision record

*This section is secondary; a reader of the mathematics above can skip it.*

**Staged implementation.**  All four parts are fully staged in this repository's
`ForTauCeti/` tree (40 modules, no placeholders): T12 (8 modules), T16 (18), T17
(11), T18 (3); `python3 scripts/check_tauceti_roadmap_topics.py --topic T12` (etc.)
lists them and validates the DAG.  The staged results still require Tau Ceti review
and migration; this roadmap is their specification.  Staged namespaces:
`TauCeti.HaagerupZsido` (Part A), `TauCeti.ContinuousLinearMap` (dimension-free
bounds), `TauCeti.LinearPMap` (unbounded layer), `TauCeti.DavisKahanTheory` (finite
`sin Θ`/YWS — a source-flavored name integration should dissolve into canonical
namespaces per `dev/tauceti/public-api-integration-review.md`).

**Origin and licensing.**  Human-directed, mostly AI-authored (Davis–Kahan/DKPS
formalization, Kitware, Inc., Apache-2.0).  The T16/T17 lineage contains material
adapted from Spectra at upstream revision
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63` (plus a recorded compatibility patch);
integration must preserve licensing, identify copied/adapted/generalized/new
material, and coordinate with the Spectra author or discuss publicly before reuse.
T12 carries `Spectra influence: none`.  Before integration: coordinate with
Tau Ceti maintainers on overlap, register intentions once PR boundaries are stable,
re-search for newly landed APIs.  The `π/2` provenance chain follows the distilled
Albeverio–Makarov–Motovilov reconstruction in `prose/distilled_literature/`; the
correspondence layers map to the Davis–Kahan 1970 Part III and Yu–Wang–Samworth
2014 digests in `prose/core-arguments/`.

**Decision records from the superseded one-topic drafts** (this directory replaces
`HaagerupZsidoKernel/`, `SylvesterRosenblum/`, `YuWangSamworth/`, and the earlier
draft here, whose `Suggested.lean.md` sketch is superseded by `Suggested.lean`):

- The T12 modules were written under lane ROADMAP-WRITE (2026-07-29); module paths
  reflect the PLACE-SYLV reorganization of the kernel aggregate.
- The reciprocal-multiplier development was split 2026-07-29 from one 2887-line
  module into four along its mathematical seams; no statement, signature, proof,
  attribute, or declaration name changed.
- An earlier route through an explicit entrywise multiplier `(αᵢ − βⱼ)⁻¹` was
  abandoned for the simultaneous Ky Fan prefix estimate; the coordinate-equation
  lemma's documentation records this so the kernel's actual entry point (the
  finite interpolation certificate) is not misattributed.
- The YWS complement identity was `private` until 2026-07-29 (item
  `YWS-S1-complement-identity`); public API by decision, per Part D.  YWS signature
  audits: the eigenblock correspondence (`hcorr`) was added to exclude arbitrary
  reducing subspaces at `B = A`; the Hermitian-dilation conclusion was corrected
  from constant one to `π/2`.
- The old T17 draft also scoped approximation numbers, Hilbert–Schmidt models, and
  the closed-operator layer into this roadmap; the consolidation moved those to
  OperatorIdeals and SpectralTheory, consumed here as external needs.  Its claim
  that the repository "completes the source-general sine-theta surface" refers to
  the wider DKPS tree: the *staged* T17 surface is the dimension-free bounded layer
  plus the complete finite-dimensional family, and Part C's domain-aware milestone
  C3 remains genuinely open in staging.
