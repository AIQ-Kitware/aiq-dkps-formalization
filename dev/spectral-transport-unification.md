# Spectral subspace transport: structure and mathematical provenance

Research checkpoint, 27 October 2026. This note joins the current proved
theory to the real signed-root converse proved in this campaign. It is not
a manuscript or a claim of historical priority. The accompanying
[research plan](schatten-transport-research-plan.md) and
[handoff](schatten-research-handoff-2026-10-26.md) give the continuation point.
Earlier priority evidence remains in the
[supplied historical review](historical-priority-review-2026-10-26.md) and
[novelty review](../papers/dk_formalization_journal/MATHEMATICAL_NOVELTY_REVIEW_2026-10-24.md).
The theorem-family map below supplements those records with exact mathematical
relationships; it does not replace the upstream proof-provenance ledger.

## Mathematical thesis and the common problem

The cohesive object is the ambient transport fiber

\[
\mathcal T(P,Q)=\{U:U^*U=UU^*=I,\ UPU^*=Q\},\qquad
D_f(P,Q)=\inf_{U\in\mathcal T(P,Q)}\operatorname{Tr}f(|I-U|).
\]

The scalar field is part of the data. Over the reals the competitors are
orthogonal operators. The cost is **extrinsic displacement**, not Grassmann
path length or the norm of a logarithm. In finite dimension the trace is an
ordinary spectral sum. In arbitrary Hilbert dimension it is the extended
positive trace, possibly infinite and defined without a separability assumption.
Finite-cost feasibility, attainment, and classification of all minimizers are
separate statements. An empty fiber and a nonempty fiber on which all costs are
infinite can have the same extended infimum.

The geometric ingredients are classical: two projections, principal angles,
their difference, a direct rotation, and stabilizers. Once a transporter R has
been chosen, every transporter is RZ for a unitary Z commuting with P. This is
a description of the feasible set, not a proof that an optimizer preserves
individual principal planes. The central research thesis is that **the penalty
and scalar field select the compatible spectral symmetries inside this fiber**.
The nuclear root description and the finite active corrections at strict
exponents are two different realizations of that selection.

Use closed subspaces K,L, their projections P,Q, and balanced crossed defects
`K ∩ Lᗮ` and `Kᗮ ∩ L`. The Hilbert theorems use an actual isometric defect
equivalence D; finite ideal feasibility constructs it from equality of the
finite defect dimensions. Write

\[
\Delta=P-Q,\quad S=|\Delta|,\quad C=\sqrt{I-S^2},\quad
J=2P-I,\quad R=\text{completed direct rotation},\quad
V=\text{nuclear transport dual}.
\]

Here C is the established `section3CosAngleOperator`; V has its established
action on the exceptional sectors, rather than being defined by dividing by S.
This distinction matters on zero and right-angle sectors.

| Penalty | Finite-cost feasibility | Proved optimization scope |
| --- | --- | --- |
| `t^p`, `1<p<2` | `Delta ∈ S_p` and balanced defects, either field | Complete complex Hilbert classification; every optimizer is canonical off a finite active sector. Finite real matching gives the value and attainers. |
| `t` | `Delta ∈ S_1` and balanced defects, either field | Complete complex signed-root classification. All real finite-bound attainers now have signed-root certificates; equality attainment has an exact numerical parity criterion. |
| `sqrt(tau^2+t^2)-tau`, `tau>0` | `Delta ∈ S_2` and balanced defects, either field | Complete complex Hilbert classification and finite active correction. |
| `t^p`, finite `p>=2` | `Delta ∈ S_p` and balanced defects | Canonical global attainment over both fields. This is not an assertion of uniqueness or an all-optimizer classification. |

The strict Schatten and Charbonnier active sectors are finite because their
positive activation thresholds exclude a neighborhood of zero from a compact
angle spectrum. At the nuclear endpoint no such positive threshold remains:
infinitely many nonzero eigenspaces can carry optimizer freedom. The compiled
nuclear product theorem describes that freedom in operator norm, and its
trace-class displacement family is compact in every native Schatten-q norm,
q>=1. Operator norm and these ideal norms are not interchangeable.

## The new real bridge

### Finite block theorem and construction

Let H be a finite-dimensional real Hilbert space, G*=-G,
`G^2=-c^2 I`, c nonzero, and let J*=J, J²=I, JG=-GJ. Then

\[
\exists E=E^*=E^2:\ EG=GE,\quad EJ+JE=J
\quad\Longleftrightarrow\quad 4\mid\dim_{\mathbb R}H.
\]

This is Lean-verified as
`TauCeti.exists_spectral_sign_projection_iff_four_dvd_finrank_real` in
[`RealSpectralSignExistence.lean`](../ForTauCeti/Analysis/InnerProductSpace/RealSpectralSignExistence.lean).
The zero-dimensional block is included. The hypothesis c nonzero is essential;
the right-angle construction below does not invoke this theorem with c=0.

For the sufficiency proof set K₀=G/c, P₊=(I+J)/2 and M=ran P₊.
K₀ exchanges the two J eigenspaces isometrically, so dim H=2 dim M.
If dim H is divisible by four, M admits a skew-adjoint orthogonal complex
structure U, by the existing `AlmostComplexStructure` criterion. Extend it
by zero to H, obtaining H₀ with H₀²=-P₊. Then

\[
A=K_0H_0+H_0K_0,\qquad E=(I+A)/2.
\]

Direct operator algebra gives A*=A, A²=I, AK₀=K₀A, AJ=-JA, hence the desired
projection equations. Necessity reuses the previously compiled obstruction:
commutation with G makes ran E even dimensional, and J exchanges ran E with
ker E. The dimension pairing is independently available as
`TauCeti.finrank_eq_two_mul_positive_eigenspace_real`.
These are classical linear-algebra constructions; the exact projection
formulation is a local derivation, without a first-priority claim.

### Actual spectral blocks, including the exceptional angles

For compact Delta and a chosen balanced-defect completion D, let
`N_s=ker(S-sI)`, s nonzero. Each N_s is finite dimensional even when the
ambient space and the pair have infinite rank. The new theorem

`TauCeti.DavisKahan.finrank_sine_eigenspace_eq_two_mul_source_side_real`

proves the literal identity

\[
\dim_{\mathbb R}N_s=2\dim_{\mathbb R}(K\cap N_s).
\]

In Lean the source side is `K.comap N_s.subtype`. It is the J-fixed half
of N_s. This is an intrinsic multiplicity statement, not a dimension count
in an assumed planar model. For finite pairs, classical principal-angle
geometry identifies this half with the multiplicity of arcsin s. A new literal
Lean equality with the labelled `Fin` angle-count expression has **not** been
added; the previously compiled finite matching theorem already states its own
parity criterion directly on those accepted principal angles.

On `0<s<1`, actual restrictions `g=(VC)|N_s` and `j=J|N_s` satisfy all the
finite-block hypotheses, with c=sqrt(1-s²). The block theorem gives
`nuclearSignedSineSpectralFactors_nonempty_iff_four_dvd_real`.
On s=1, g=0, so the commutation equation disappears. The restriction
v=V|N₁ is a skew-adjoint orthogonal complex structure anticommuting with j;
`(I+vj)/2` supplies a factor. This is
`nuclearSignedSineSpectralFactors_nonempty_one_real`. Thus right angles need
defect balance but no additional even principal-side multiplicity. At s=0 the
root must vanish and there is no free factor. Outside [0,1] the eigenspaces
are zero, because S is a positive contraction.

### Infinite assembly and attained transport

The existing independent spectral product theorem now gives the new equivalences

\[
\begin{split}
\{\text{real signed roots}\}\ne\varnothing
&\Longleftrightarrow
\forall\,0<s<1,\quad4\mid\dim_{\mathbb R}N_s\\
&\Longleftrightarrow
\forall\,0<s<1,\quad\dim_{\mathbb R}(K\cap N_s)\text{ is even}.
\end{split}
\]

The exact Lean declarations, in
[`NuclearRealRootCriteria.lean`](../DavisKahan/Geometry/Polar/NuclearRealRootCriteria.lean), are
`nuclearSignedSineParameters_nonempty_iff_four_dvd_real` and
`nuclearSignedSineParameters_nonempty_iff_even_source_multiplicity_real`
(namespace `TauCeti.DavisKahan`). Compactness and D are hypotheses of both.
Arbitrary infinite families are assembled using the existing product theorem;
there is no finite-rank assumption or new summation construction.

The roots are precisely the bounded operators A satisfying

\[
A=A^*,\qquad |A|=S,\qquad [A,VC]=0,\qquad JAJ=-A.
\]

The established generic formula `Z=C+VA`, `T=RZ*` constructs an actual
transporter. The new `exists_real_nuclear_transport_of_sine_parity` proves

\[
TP T^*=Q,\qquad \|I-T\|_1=\|P-Q\|_1
\le\|I-W\|_1\quad(W\in\mathcal T(P,Q)).
\]

The statement is extended-valued. It supplies a finite global minimum when
Delta is trace class; for merely compact non-trace-class Delta the equality
may read infinity=infinity. It does not settle a meaningful finite optimization
problem in that latter case.

This explains finite matching parity through a real complex-structure
obstruction and extends it to arbitrary rank. The equality-certificate
continuation now proves necessity over **both fields**. The shared
`ContinuousLinearMap.re_nuclearTrace_eq_nuclearENorm_iff_isPositive` and
`nuclearTransportDual_trace_calibration` use a real/complex compact Gram
identity and Hilbert--Schmidt columns. Their trace identities are classical.
The original complex theorem names remain specialized corollaries.

`nuclear_eq_projection_sub_iff_certificate` applies to any actual transporter
with trace-class Delta and D: attaining the projection bound is equivalent
to finite displacement cost, fixation of the full common sector, and positive
relative dual displacement. `nuclear_eq_projection_sub_signed_sine_parameters`
extracts its independent root without any invariant-plane hypothesis.
`nuclearSignedSineEquivProjectionBoundAttainers` is an explicit bijection
between roots and **all** equality attainers, over either field.

Consequently, for real trace-class pairs with D,
`exists_real_nuclear_transport_eq_projection_sub_iff_even_source_multiplicity`
proves that the finite projection bound is attained iff every acute source
multiplicity is even. The full-dimension form is
`exists_real_nuclear_transport_eq_projection_sub_iff_four_dvd`.
`nuclear_projection_sub_lt_transport_of_sine_dimension_real` shows that a
violating block forces the cost of **each** real transporter strictly above
the bound. This is not a uniform positive gap for the infimum. No
infinite-dimensional real matching formula or classification of minimizers
above the bound follows. Those are not prerequisites for the publication core.

## A common scalar transition principle

The following is a conventional analytic derivation, **not a new generic Lean
theorem**. It identifies a reusable sufficient condition satisfied by both
existing strict-regime scalar proofs. Those proofs remain separately compiled.

Fix `0<theta<pi/2` and `g(t)=f(2 sin(t/2))` on [0,2 theta]. Assume g is
continuous there and C² on (0,pi), with `a=g'>0` on (0,pi) and
`lim_(t downarrow 0) a(t)=0`. For `0<=delta<theta` put

\[
L_\theta(\delta)=\log a(\theta+\delta)-\log a(\theta-\delta),\qquad
F_\theta(\delta)=g(\theta+\delta)+g(\theta-\delta).
\]

Then `L(0)=0`, `L(delta) -> +infinity` as delta approaches theta, and

\[
F_\theta'(\delta)=a(\theta-\delta)(e^{L_\theta(\delta)}-1).
\]

A sufficient shape condition is
`L'(delta)=w(delta) H(delta)`, where w is positive on [0,theta), and H
is continuous and strictly increasing. This condition concerns logarithmic
curvature, not the desired minimizer itself. If H(0)>=0, L is strictly
positive away from zero and zero is the unique minimizer on [0,theta].
If H(0)<0, L first decreases; its infinite endpoint limit forces exactly one
turn, followed by exactly one positive zero. F decreases to that zero and
then increases, giving a unique positive minimizing phase. The closed
critical case H(0)=0 still has unique zero phase. No uniform quadratic growth
follows; the known critical quartic behavior is consistent with this argument.

Both penalties have precisely this shape. Write c=cos theta, d=cos delta.

* For `1<p<2`,
  `L'=sin(theta)[p c-(2-p)d]/(d^2-c^2)`.
  Its increasing numerator changes sign at the established threshold
  `cos(theta)=(2-p)/p`.
* For Charbonnier put `B=tau^2+2>2`. Its derivative is
  `L'=2 sin(theta) N(d)/[(d^2-c^2)(B^2-4Bcd+4(c^2+d^2-1))]`, where
  `N(d)=-B d^3+6c d^2-3B c^2 d+c(B^2+2c^2-4)`.
  Both denominator factors are positive. Moreover
  `N'(d)=-3[B(d^2+c^2)-4cd]<0`, so N(cos delta) strictly increases, and
  `N(1)=(B-2c)(Bc-c^2-1)`.
  With `eta=(tau+sqrt(tau^2+4))/2`, the threshold is c=eta^(-2), agreeing
  with the established smoothed transition.

These are sufficient conditions, not a minimal characterization of every
possible penalty. At theta=pi/2 the endpoint derivative argument changes
because a(pi)=0; the established right-angle formulas handle it separately.
At p=1, a(0+)=1, so the stated shape theorem does not apply: for positive
acute theta the nuclear phase cost decreases to the boundary delta=theta.
At p=2, `F=4-4 cos(theta)cos(delta)`; zero is uniquely minimizing for acute
theta and the right-angle cost is flat.

Local curvature alone is insufficient for general nonnegative penalties.
For example take `g(t)=(175/2)t^2-17t^4+t^6`, which is nonnegative since
`g(t)=t^2[(t^2-17/2)^2+61/4]`. At theta=1,
`F(delta)-F(0)=delta^2-4delta^4+2delta^6`: zero is a strict local minimum
but the boundary delta=1 is better. Defining
`f(s)=g(2 arcsin(s/2))` on [0,2] gives a continuous nonnegative spectral
penalty with this behavior. This example refutes a curvature-only principle;
it does not refute the stronger shape condition, or impose monotonicity on f.

To pass from scalar phases to the unrestricted complex transport fiber one
still needs the existing stationarity, no-mixing and gradient-kernel analyses,
the exceptional-sector classification, and a global spectral lower bound plus
feasible attainment. In infinite dimension ideal control and tail arguments
are also required. Scalar calculus does not supply these conclusions, and
the real matching results rule out a field-independent planar reduction.

## Limits of regimes: a proved obstruction and the remaining claims

Finite-dimensional exponent continuity and closedness of the minimizer graph
are already compiled in `SchattenExponentContinuity.lean`; the scalar minimum
is continuous in p by `continuousOn_phaseMinimum_exponent`. These give limits
of minimum values and closed limits of convergent optimizer selections on a
fixed compact fiber. They do not show that every endpoint optimizer is a limit.

Two new scalar statements in `SchattenPhaseMinimum.lean`, namespace
`TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition`, make this
distinction formal:

* `phasePower_two_right_angle`: every real phase has quadratic right-angle
  cost four.
* `not_tendsto_zero_of_right_angle_subquadratic_minimizers`: on any nontrivial
  filter, exact scalar minimizers with `1<=p<2` and `delta ∈ [0,pi/2]` cannot
  tend to zero. The existing equality theorem forces delta=pi/2 eventually.

In particular, choose p tending to two from below: minimum values converge
to four, but the quadratic-optimal zero phase is not approximated by these
scalar minimizers. This is explicitly a scalar optimizer-set obstruction;
no unrestricted ambient set-limit assertion is smuggled into it.

For a finite n-dimensional fiber, elementary uniform penalty bounds give
useful conventional limiting statements:

\[
0\le t-f_\tau(t)\le\tau,\qquad
0\le t^2-2\tau f_\tau(t)
=\frac{t^4}{(\sqrt{\tau^2+t^2}+\tau)^2}\le\frac4{\tau^2}
\quad(0\le t\le2).
\]

Thus nuclear versus smoothed minimum values differ by at most n tau as
tau decreases to zero; rescaled smoothed versus quadratic minima differ
by at most 4n/tau² as tau tends to infinity. Compactness implies every
convergent selection of minimizers has an endpoint-optimal limit. These
specific smoothing-limit assertions are not newly Lean-certified here.
They say nothing about approximation of every endpoint optimizer.

For infinite trace-class pairs, pointwise penalty limits and the already
proved ideal compactness are starting ingredients, not an automatic theorem
about optimizer families. The compactness theorem controls nuclear optimizers,
not arbitrary varying-p optimizers. In particular, p down to one activates
increasingly many finite sectors while the limiting nuclear family may carry
independent freedom on infinitely many sectors. The exact upper/lower set
limits, selected-optimizer convergence and endpoint surjectivity remain open.

## General spectral-penalty feasibility without a new abstraction

The generic compiled input already exists:
`InfiniteDimensional.schatten_transport_iff_projection_sub_ne_top_and_defect_balance`
and `gauge_nonacuteDirectRotation_ne_top_iff_projection_sub`. It would be
duplication to rebuild their ideal transport argument for another penalty.

Here is the precise conventional corollary. Suppose q>=1, f is continuous
on [0,2], f(0)=0, f(t)>0 for t>0, and for some epsilon>0 and constants
0<a<=b one has `a t^q <= f(t) <= b t^q` on [0,epsilon]∩[0,2]. Compactness
and positivity away from zero extend this to global positive comparison
constants on [0,2]. Positive functional calculus and the extended trace then
give finite f-cost iff `I-U ∈ S_q`. The existing feasibility theorem yields
existence of a finite-cost transporter iff `P-Q ∈ S_q` and the finite crossed
defects balance, over either field. This argument gives feasibility only,
not the form of any optimizer. The comparison-to-trace corollary has not been
packaged as a new Lean theorem.

The positivity-away-from-zero hypothesis cannot simply be dropped. The
continuous nonnegative penalty `f(t)=min(t^2,(2-t)^2)` agrees with t² near
zero but vanishes at two. On an infinite-dimensional space, U=-I transports
P to itself with cost zero, although I-U=2I is not compact or Schatten.
Thus a near-zero comparison alone does not even characterize finite cost
of a fixed displacement. Charbonnier with fixed positive tau is globally
comparable to t² on [0,2]; the nuclear and Schatten penalties select their
own exponents. No new generic penalty framework is necessary for these cases.

## Verified sources and authentication boundaries

Locators below were checked on 27 October 2026 unless explicitly marked
otherwise. A primary-source confirmation means the identified statement was
read in the original work or an author-hosted version; it does not establish
earliest historical priority. Source statements are paraphrased. Paper
wrappers can formalize classical assertions using a different proof: that is
not evidence that the source proof was adapted.

* **S1 — Jordan (1875),** *Essai sur la géométrie à n dimensions*, BSMF 3,
  103–174. The [Numdam primary scan](https://www.numdam.org/item/10.24033/bsmf.90.pdf),
  §§46–50, pp. 134–136, exhibits canonical forms and angular invariants,
  including zero/right-angle cases. This supports principal-angle ancestry;
  it does not identify a modern optimal transport theorem or settle all
  earlier priority questions.
* **S2 — Davis (1958),** *Separation of two linear subspaces*, Acta Sci. Math.
  19, 172–187, [primary archive](https://acta.bibl.u-szeged.hu/38578/1/math_019_fasc_003_004.pdf),
  printed pp. 183–186 (PDF pages 37–40). Theorem 7.1 gives operator-norm
  displacement minimality; Theorem 7.3 treats the Hilbert–Schmidt norm;
  Theorem 7.4 gives finite-dimensional Schatten p>=2 minimality. Its proof
  establishes squared-displacement UI-norm comparison. Page 186 already
  discusses failure below two near a right angle. The p>=2 sign was checked
  visually on printed p. 185, since extracted text loses it.
* **S3 — Davis–Kahan (1970),** *The Rotation of Eigenvectors by a Perturbation.
  III*, SIAM J. Numer. Anal. 7, 1–46,
  [publisher record](https://doi.org/10.1137/0707001), Proposition 4.3,
  Examples 4.1–4.2, Proposition 4.4. The maintained
  [distributable source reconstruction](../prose/distilled_literature/DavisKahan1970_part_III.tex)
  preserves squared-displacement minimality, the real and complex phase
  counterexamples, and the printed real short-angle assertion. **Confidence:
  existing repository source audit, not fresh original-paper authentication**;
  the publisher endpoint did not expose the original article in this review.
  Do not count access to its abstract as verification of those propositions.
* **S4 — Bolotnikov–Li–Rodman (2001),** *Minimal distortion problems for classes
  of unitary matrices*, ELA 8, 26–46,
  [official primary PDF](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117).
  Problem 1.1 and (1.6), pp. 26–28, formulate the ambient transport distortion
  problem and its block-diagonal formulation. Theorem 3.1, pp. 33–35, proves
  Q-norm block minimality; Lemmas 3.2–3.3, pp. 35–36, treat planar power costs,
  including a subquadratic right-angle example. The introduction explicitly
  says the proofs apply over the reals. These precede the problem formulation,
  the Q-norm regime and special subquadratic phenomena; they are not evidence
  of the present exact matching or Hilbert all-optimizer classifications.
* **S5 — Qiu–Zhang–Li (2006),** *Unitarily invariant metrics on the Grassmann
  space*, SIMAX 27, 507–531,
  [author-hosted primary version](https://cklixx.people.wm.edu/metric.pdf),
  §5, PDF p. 20: distinguishes restricted, squared and full displacement
  assertions; its full-displacement paragraph repeats the real pi/3 claim.
  Theorem 6 concerns a logarithmic objective, which the displacement
  counterexample does not refute. **Zhang–Qiu (2010),**
  [published primary version](https://eeqiu.people.ust.hk/wp-content/uploads/2021/04/From-Subadditive-Inequalities-of-Singular-Values-to-Triangle-Inequalities-of-Canonical-Angles.pdf),
  §4, p. 1615, explicitly states trace-norm nonminimality and Frobenius
  optimality. Their canonical-angle metric work is not the present extrinsic
  power-cost optimizer classification.
* **S6 — Avron–Seiler–Simon (1994),** *The index of a pair of projections*,
  JFA 120, 220–237,
  [author-hosted primary scan](https://phsites.technion.ac.il/avron/wp-content/uploads/sites/3/2013/05/J_Func_Anal_120_220_1994_index_pair.pdf).
  Theorem 2.1 and Corollary 2.2, p. 222, give the anticommuting projection
  difference identities; p. 223 gives Kato's polar intertwiner. Proposition
  3.1, p. 224, identifies the relative index with the difference of the
  crossed-defect dimensions. Theorem 3.3, p. 226, characterizes zero index
  by a unitary simultaneously exchanging the two projections. It is not
  verbatim the near-identity Schatten-feasibility theorem.
* **S7 — Li (1995),** *New perturbation bounds for the unitary polar factor*,
  SIAM J. Matrix Anal. Appl. 16, 327–332. The
  [author's technical preprint](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1994/CSD-94-852.pdf),
  Theorem 1, printed p. 4, proves for nonsingular square matrices the
  UI-norm estimate `||Q_A-Q_B|| <= 2||A-B||/(sigma_min(A)+sigma_min(B))`.
  This confirms a classical conditioning ingredient, not priority for
  projection-commuting optimizer corrections or their exact closed threshold.
* **S8 — Massey–Rios–Stojanoff (2018),**
  [*Local Lidskii's theorems for unitarily invariant norms*](https://arxiv.org/html/1806.11436),
  Theorems 3.5 and 3.12: local-to-global statements on fixed eigenvalue or
  singular-value orbits with strict convexity assumptions. Those orbits are
  different feasible sets; a transport-fiber theorem requires its own argument.
  **Contino–Giribet–Maestripieri (2017),**
  [*Weighted Procrustes problems*](https://arxiv.org/pdf/1610.00558), Theorem
  4.5, PDF p. 13, minimizes a weighted Schatten residual over bounded X.
  Its unconstrained variable is not an orthogonal/unitary transport constraint.
* **S9 — Classical foundations with incomplete fresh authentication.**
  Halmos (1969), [*Two subspaces*](https://doi.org/10.1090/S0002-9947-1969-0251519-5),
  is the established generic-position decomposition attribution, but the AMS
  full-text endpoint was inaccessible; exact theorem-by-theorem comparison
  remains pending here. Sz.-Nagy's 1947 projection intertwining and Kato's
  early work are historical predecessors; their original statements were
  not freshly authenticated. S6 directly verifies the polar construction
  and explicitly credits Kato. No first-contributor claim is made for it.
  Bhatia's *Matrix Analysis* (1997), IV.2, and *Perturbation Bounds for Matrix
  Eigenvalues*, [Chapter 2](https://epubs.siam.org/doi/10.1137/1.9780898719079.ch2),
  are classical UI-norm references; the latter's publisher description was
  checked, but exact book theorem statements were not independently obtained.
  S2 and S5 supply directly checked primary comparison results; do not invent
  an exact Bhatia theorem number or infer proof adaptation from subject overlap.
* **S10 — Unauthenticated exercise lead.** Aubrun–Szarek, *Alice and Bob Meet
  Banach*, Exercise B.12: the previous review's limitation persists. An
  authoritative printed-edition statement was not checked. Its precise
  hypotheses and priority implications remain unresolved. The supplied
  external-agent report and third-party reproductions are not primary confirmation.
* **S11 — Kaftal–Loreaux (2017),** *Kadison's Pythagorean Theorem and essential
  codimension*, [author-hosted primary version](https://www.siue.edu/~jloreau/papers/essential-codimension-kl.pdf),
  Proposition 2.7(ii), preprint p. 8. On a separable infinite-dimensional
  complex Hilbert space, for a proper operator ideal J and projections with
  p-q in J, zero essential codimension is equivalent to conjugacy by a unitary
  in I+J. The proof uses a completed generic rotation and finite defect
  matching; (2.9) identifies the index condition with equal finite defects.
  This is an exact classical predecessor of ideal transport feasibility,
  beyond merely related restricted-Grassmann geometry. The present real and
  nonseparable scope should be stated explicitly, without claiming discovery
  of the underlying criterion.
* **S12 — Charbonnier–Blanc-Féraud–Aubert–Barlaud (1997),** *Deterministic
  edge-preserving regularization in computed imaging*, IEEE Trans. Image
  Processing 6, 298–311,
  [author-hosted published primary PDF](https://webcms.i3s.unice.fr/Michel_Barlaud/sites/mbarlaud/files/2023-11/IEEE_IP_1997.pdf),
  Table I, p. 301. Visually checked: the potential labelled HS is
  `phi(t)=2 sqrt(1+t^2)-2`. Our `f_tau(t)=(tau/2) phi(t/tau)` is its rescaling.
  This attributes the penalty, not the transport problem or optimizer
  classification. The table cites earlier work by the same authors; earliest
  priority within that sequence was not separately audited.

## Source-to-Lean provenance map

Namespace abbreviations in this table are exact: **D** = `TauCeti.DavisKahan`,
**F** = `TauCeti.DavisKahan.FiniteDimensional`, **I** =
`TauCeti.DavisKahan.InfiniteDimensional`. Append the displayed suffix literally.
File links give the maintained declaration homes. Dependencies identify
mathematical ingredients, not an assertion that the corresponding source proof
was copied. For actual formal-proof ancestry, retain the existing Lean headers
and [upstream contribution ledger](tauceti/dkps-upstream-contribution-census.md),
including its pre-DKPS/Spectra ancestry and independent-work distinctions.

| ID / exact formal result and source | Essential mathematical statement | Attribution and verified locator | Relationship | Confidence | Specific dependencies | Novelty boundary |
| --- | --- | --- | --- | --- | --- | --- |
| **T1** `TauCeti.AlmostComplexStructure.exists_skew_unitary_iff_even_finrank_real`, [OrthogonalComplexStructure](../ForTauCeti/Analysis/InnerProductSpace/OrthogonalComplexStructure.lean); `TauCeti.exists_spectral_sign_projection_iff_four_dvd_finrank_real`, [new block theorem](../ForTauCeti/Analysis/InnerProductSpace/RealSpectralSignExistence.lean) | Orthogonal complex structures exist in even finite real dimension; the G/J-compatible projection exists iff the full dimension is divisible by four, with all G/J hypotheses above. | Classical complex-module dimension and orthonormal-pair construction. Accepted Tau Ceti `AlmostComplexStructure.even_finrank_real` supplies necessity; its documentation cites McDuff–Salamon §2.1, not freshly authenticated here. | Classical construction formally verified; local projection consequence derived here. | Accepted upstream proof checked; exact external projection predecessor unresolved. | Accepted almost-complex module/Hermitian API; existing orthogonal-complex-structure converse; `four_dvd_finrank_of_spectral_sign_projection_real`. | No novelty claim for parity of complex structures. The transport application is T8. |
| **T2** `TauCeti.singularValues_starProjection_comp_starProjection`, [PrincipalAngles](../ForTauCeti/Analysis/InnerProductSpace/PrincipalAngles.lean); `D.compact_transport_iff_compact_projection_sub_and_defect_balance`, [DirectRotationIdeal](../DavisKahan/Geometry/Polar/DirectRotationIdeal.lean) | Orthonormal frames recover principal cosines; in arbitrary complete real/complex Hilbert space a compact displacement transporter exists iff projection difference is compact and crossed defects balance. | S1 angular ancestry; S6 Proposition 3.1 and Theorem 3.3 for relative index; S11 Proposition 2.7(ii) for exact complex separable restricted-unitary feasibility. S9 for early source-authentication limits. | Classical geometry and index ingredients; derived exact transport feasibility. | Direct primary S1/S6/S11; complex separable predecessor confirmed. | Accepted principal-angle/singular-value API; `Submodule.finite_crossedDefect_balance_of_compact_transport`; direct rotation factorization and Fredholm index. | Ambient unitary equivalence alone is weaker; S6's simultaneous swap is not silently substituted for near-identity feasibility. |
| **T3** `F.directRotation_displacementSquare_uiNorm`, [Majorization](../DavisKahan/FiniteDimensional/DirectRotation/Majorization.lean); `F.directRotation_fullDisplacement_qnorm`, [QNorm](../DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean) | Squared displacement is UI-norm minimal; full displacement is minimal for Q-norms over either field without a short-angle bound. | S2 Theorem 7.4 and proof, p. 185; S3 Proposition 4.3; S4 Theorem 3.1 and Lemma 3.2. | Classical result formally verified; source-claim repair by a classical consequence. | Direct primary S2/S4; S3 existing source audit. | Ky Fan/majorization comparison; UI norm monotonicity; Q-norm square identity. | Do not claim Q-norm optimality, the p>=2 regime or its derivation as new mathematics. |
| **T4** `F.SmallAngleCounterexample.arbitrarilySmall_fullDisplacement_refuted`, [SmallAngleCounterexample](../DavisKahan/FiniteDimensional/DirectRotation/SmallAngleCounterexample.lean) | A real four-dimensional trace-norm counterexample exists below every positive principal-angle threshold. | S3 printed Proposition 4.4 and its adjacent examples; S5 repeats the real threshold assertion. Earlier norm failures: S2/S4/S5. S10 remains unauthenticated. | Historical correction; explicit formal counterexample strengthening the absence of a positive repair threshold. | Lean proof direct; printed 1970 wording relies on existing source audit; S5 repetition directly checked. | Actual canonical rotation identification, four-dimensional orthogonal competitor and exact singular values. | General nonminimality is classical; historical priority for this exact correction remains unresolved. |
| **T5** `I.SchattenPhaseTransition.schatten_transport_isMin_iff_canonical_tail_phase_and_defect_complex`, [Schatten classification](../DavisKahan/InfiniteDimensional/DirectRotation/SchattenOptimizerClassification.lean); `I.SmoothedPhaseTransition.charbonnier_transport_isMin_iff_canonical_tail_phase_and_defect_complex`, [Charbonnier classification](../DavisKahan/InfiniteDimensional/DirectRotation/CharbonnierOptimizerClassification.lean) | For feasible native finite-cost pairs, every complex optimizer is canonical on the inactive tail and has the exact finite active phase/defect structure; `1<p<2` or `tau>0`, respectively. | Classical ambient problem S4 Problem 1.1; special planar phenomenon S4 Lemma 3.3; classical smoothing penalty S12 Table I. No equivalent full classification located in the examined sources. | Potentially novel derivations/extensions. | Primary predecessors verified; exact historical priority unresolved. | Separate scalar transition proofs, no-mixing and gradient-kernel lemmas, unrestricted spectral lower bounds, ideal tail and attainment theorems. | Not a universal planar-penalty theorem, real classification, or infinite-cost local-minimum statement. |
| **T6** `D.nuclearSignedSineEquivOptimizers_complex`, [NuclearRootClassification](../DavisKahan/Geometry/Polar/NuclearRootClassification.lean); `D.exists_nuclear_optimizer_spectral_homeomorph_complex`, [NuclearRootSpectralFactors](../DavisKahan/Geometry/Polar/NuclearRootSpectralFactors.lean) | Trace-class complex pairs with D: all ambient nuclear optimizers are exactly independent signed roots, and their operator-norm topology is the independent nonzero-eigenspace projection product. | Trace-norm nonminimality is already S3 Example 4.2 / S5 p. 1615. Spectral decomposition, polar factors and trace duality are classical ingredients. No equivalent complete parametrization located. | Potentially novel complete parametrization and constrained product application. | Primary S5; S3 source-audit evidence; parametrization priority unresolved. | `nuclear_eq_projection_sub_iff_relative_certificate_complex`, generic root construction, `SignedModulusProjection`, `CompactModulusSymmetryFactors`. | No novelty claimed for the spectral theorem or noncanonical phases; T8 gives the shared real/complex equality-attainer classification. |
| **T7** `F.RealTransport.realTransportPowerMinimum_eq_matching` and `exists_minimizing_real_schatten_transport_matching_of_one_le`, [RealNuclearMatching](../DavisKahan/FiniteDimensional/DirectRotation/RealNuclearMatching.lean); `realTransportPowerMinimum_one_eq_sine_sum_iff_even_multiplicities`, [RealNuclearFieldEquality](../DavisKahan/FiniteDimensional/DirectRotation/RealNuclearFieldEquality.lean), same namespace | Finite real `1<=p<2` exact matching value with an actual attainer; nuclear equality with the complex sine sum iff all strictly acute accepted angle multiplicities are even. | S4 is a predecessor for the problem and special planar costs, not a located exact matching formula. | Potentially novel unrestricted real matching/equality derivation. | Primary predecessor verified; equivalent theorem not located, priority unresolved. | Real stationary spectral decomposition, orthogonal complex structures, finite matching combinatorics, compact exponent continuity to p=1. | Values plus constructed attainers are not classification of all real optimizers. |
| **T8** `D.nuclearSignedSineEquivProjectionBoundAttainers`, [NuclearRootClassification](../DavisKahan/Geometry/Polar/NuclearRootClassification.lean); `D.exists_real_nuclear_transport_eq_projection_sub_iff_even_source_multiplicity` and `nuclear_projection_sub_lt_transport_of_sine_dimension_real`, [NuclearRealRootCriteria](../DavisKahan/Geometry/Polar/NuclearRealRootCriteria.lean) | Trace-class Delta and actual D: all real/complex lower-bound attainers are exactly signed roots. Real equality attainment iff all acute source multiplicities are even; a violating block forces pointwise strict cost. | Classical block ingredient T1 and trace ingredients T14; earlier internal predecessors T6/T7 and the compact root product. No exact external equality/parity classification located. | Structural extension; potentially novel transport consequences. | Compiled, with external priority unresolved and source-authentication limits recorded. | Field-independent dual calibration and positivity equality; actual full/half spectral dimension; independent factor assembly and root reconstruction. | Complete classification of equality attainers, not all real optimizers above the bound; pointwise strictness is not a uniform infimum gap. |
| **T9** `D.isCompact_nuclear_optimizer_displacements_schatten_complex`, [NuclearRootIdealCompactness](../DavisKahan/Geometry/Polar/NuclearRootIdealCompactness.lean); `D.nuclear_optimizer_schatten_profile_complex`, [NuclearRootProfile](../DavisKahan/Geometry/Polar/NuclearRootProfile.lean) | Entire complex nuclear displacement family compact in each native S_q, q>=1, with a common exact Schatten moment profile. | Classical compact spectral decomposition and dominated ideal convergence; exact constrained-family conclusions not located in S1–S9. | Potentially novel application/extension; classical proof ingredients. | Compiled; precise external priority unresolved. | T6 weighted spectral product; `CompactModulusIdeal`; `Family.SchattenConvergence`; root spectral identities. | Not compactness of varying-exponent optimizers, nor a newly asserted singular-value sequence identity. |
| **T10** `I.schatten_transport_iff_projection_sub_ne_top_and_defect_balance`, [SchattenFeasibility](../DavisKahan/InfiniteDimensional/DirectRotation/SchattenFeasibility.lean); `I.charbonnier_transport_iff_schatten_two_and_defect_balance`, [CharbonnierFeasibility](../DavisKahan/InfiniteDimensional/DirectRotation/CharbonnierFeasibility.lean) | Exact finite-cost feasibility, either field, in S_p for Schatten, and S_2 for fixed-positive Charbonnier smoothing. | S11 Proposition 2.7(ii) is the exact complex separable ideal criterion; S6 supplies the relative index; Charbonnier specializes quadratic membership. | Formalization/extension of a classical criterion and penalty specialization. | Direct primary S6/S11; real and nonseparable scope stated separately. | T2; `OperatorIdealFamily.gauge_projection_sub_le_unitary_displacement`; `gauge_nonacuteDirectRotation_ne_top_iff_projection_sub`; Charbonnier quadratic comparison. | Feasibility is separate from optimality and from arbitrary ambient equivalence. |
| **T11** `I.SchattenPhaseTransition.schatten_isMin_of_isLocalMinOn_complex`, [SchattenLocalGlobal](../DavisKahan/InfiniteDimensional/DirectRotation/SchattenLocalGlobal.lean); `I.SmoothedPhaseTransition.charbonnier_isMin_of_isLocalMinOn_complex`, [CharbonnierLocalGlobal](../DavisKahan/InfiniteDimensional/DirectRotation/CharbonnierLocalGlobal.lean) | Finite-cost complex local minima are global in the stated strict/smoothed regimes. | S8 local Lidskii results are related predecessors on different orbits, not direct source-identical transport results. | Potentially novel transport-specific derivation. | Primary neighboring theorem checked; priority unresolved. | T5 finite active classification; finite local descent; tail analysis. | Real analogue is refuted; nuclear and arbitrary infinite-cost statements do not follow. |
| **T12** `I.SchattenPhaseTransition.norm_nearest_schatten_corrections_sub_le_at_closed_critical_commutator`, [SchattenCorrectionDataStability](../DavisKahan/InfiniteDimensional/DirectRotation/SchattenCorrectionDataStability.lean) | In the native-ideal feasible closed canonical regime, nearest projection-commuting corrections have operator-norm data stability, including constant p/(2-p) at the closed threshold. | S7 Theorem 1 is a classical polar-conditioning ingredient; S8 weighted Procrustes is a different constraint. | Transport/correction application and exact threshold extension; polar perturbation ingredient classical. | Primary ingredients checked; exact application priority unresolved. | T5 uniqueness; `canonical_correction_eq_diagBlock_factorThru_modulus`; polar-factor perturbation estimate. | Operator-norm data stability, not objective-excess distance in an ideal norm. Critical quartic growth excludes an automatic quadratic excess estimate. |
| **T13** `F.SchattenPhaseTransition.phasePower_two_right_angle` and `not_tendsto_zero_of_right_angle_subquadratic_minimizers`, [SchattenPhaseMinimum](../DavisKahan/FiniteDimensional/DirectRotation/SchattenPhaseMinimum.lean) | Quadratic right-angle phases are all optimal, but subquadratic exact scalar minimizers cannot converge to phase zero. | Elementary consequence of the existing right-angle phase formula; S4 Lemma 3.3 is a classical special-phase predecessor. | New formal endpoint obstruction; no independent novelty claim for the elementary scalar observation. | Compiled; exact earlier endpoint wording not located. | `phaseChord_add_sq`; `phasePower_right_angle_eq_minimum_iff`; uniqueness of limits. | Refutes scalar endpoint approximability, not by itself a full ambient optimizer-set limit theorem. |
| **T14** `ContinuousLinearMap.nuclearENorm_adjoint_comp_self_eq_hilbertSchmidtEnergy`, `re_nuclearTrace_eq_nuclearENorm_iff_isPositive`, `nuclearTrace_mul_comm`, [Nuclear/Trace](../ForTauCeti/Analysis/OperatorIdeal/Nuclear/Trace.lean); compact reduction in [CompactGram](../ForTauCeti/Analysis/OperatorIdeal/Nuclear/CompactGram.lean) | Over either field, arbitrary Hilbert dimension: nuclear Gram gauge equals Hilbert--Schmidt energy, including infinity; finite trace saturates its norm bound iff positive; finite trace is cyclic. | Classical Hilbert--Schmidt/trace-ideal ingredients, proved directly from the accepted column, Parseval and compact spectral APIs. An exact external theorem/page for the positivity equality is not newly authenticated. | Classical proof ingredients formally verified and generalized from the former complex API. | Pinned formal sources and full build checked; exact external trace locator remains pending. | Tau Ceti Hilbert--Schmidt columns and compactness; compact positive eigenvalue-multiplicity sum; square-root polar factorization; Cauchy--Schwarz equality. | No novelty claim for trace identities. The new mathematical application is T8; no parallel real trace definition is introduced. |

Unresolved source work is substantive, not a request to add a checker: obtain
the authoritative Exercise B.12 statement; authenticate the original 1970
propositions against the maintained reconstruction; inspect the original
Sz.-Nagy/Kato and exact Halmos/Bhatia statements; pursue the real Procrustes and
optimizer-classification citation chains for the exact hypotheses of T5–T9.
S11 now supplies a directly verified ideal-feasibility predecessor for T10. Absence of
an equivalent in the sources examined is evidence for a **candidate**, never
proof of historical novelty. No new theorem is attributed to the whole author
list of a classical field merely by keyword overlap.

## Theorem organization for a future mathematical treatment

1. **Geometry and feasibility.** State the ambient fiber, classical projection
   geometry, defect index and exact ideal feasibility before any cost formula.
2. **Penalty-dependent phase selection.** Give the scalar shape principle
   with its exceptional endpoints, then the separately justified unrestricted
   complex lifting theorems. Include the real obstruction to a universal lift.
3. **Complete complex regimes.** Present strict Schatten/Charbonnier finite
   active classifications beside the qualitatively different nuclear root
   product. Separate values, all optimizers and their native topologies.
4. **The real bridge.** Present finite matching, its equality parity, the
   G/J-compatible projection theorem, and arbitrary-rank root existence.
   Include the now-proved field-independent certificate necessity and exact real equality-attainment criterion.
5. **Limits and corrections.** Distinguish value convergence from optimizer
   set limits; include the right-angle obstruction. Then state the proved
   commuting-correction and stability applications at their exact thresholds.

This organization supports a coherent contribution without claiming a common
unrestricted optimizer formula for arbitrary penalties or a complete real
Hilbert matching theory. The new bridge is T8; the next mathematical step is
the unified spectral-penalty theorem. Real equality necessity is now proved;
full real optimizer topology and exhaustive limiting classifications are
secondary to the publication core.

## Completed compiler validation

After `lake exe cache get`, the full default `lake build` passed **21,427 jobs**
with warnings as errors. This includes the new block and real spectral criteria,
scalar endpoint obstruction, and all maintained consumers after replacing the
local complex-dimension necessity proof with the accepted Tau Ceti declaration.
The final log is `/tmp/dkps-unification/real-certificate-full.log`.
The shared trace target passed 6,438 jobs and the generic calibration target
passed 7,160 jobs before the full consumer build. These certify
the formal statements; they do not certify historical novelty or turn this
note's conventional analytic derivations into Lean theorems.
