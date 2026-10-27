# Publication core: spectral penalties, field compatibility and ideals

Assessment at mathematical checkpoint `ff3c1657d`, 27 October 2026.
The full default build passed 21,427 jobs with warnings as errors.
The success criterion is a coherent central theory and defensible attribution,
not completion of the research backlog. This assessment is research planning;
the proposed abstract below is not a manuscript edit.

## Central thesis and present decision

**Spectral penalties determine optimal phase selection; the scalar field
determines compatibility constraints on those phases; and operator-ideal
geometry determines infinite-dimensional feasibility and attainment.**

The newly completed real equality-attainer theorem makes this a structural
statement at the nuclear endpoint: the same signed-root certificate works
over both fields, while its real solvability is an even-multiplicity condition.
The complex strict-Schatten and Charbonnier classifications explain two regular
phase-selection regimes. Finite real matching explains how real compatibility
changes the value when complex phases cannot be realized.

The strongest next organizing theorem is finite-dimensional complex
decoupling for the smoothed-power family, followed by the reusable Hilbert
lifting argument. Start with this family rather than requiring a formal theorem
for every C² penalty. The wider derivative-shape criterion remains worthwhile,
but adds a generic spectral differentiation obligation that the concrete family
can avoid. No counterexample to the fragment's decoupling assertion was found
in this examination; it is still a candidate theorem, not a verified result.

## Five principal statements

### C1. Complex spectral-penalty decoupling — candidate central theorem

Let H be finite-dimensional complex Hilbert space, P,Q orthogonal projections
of equal rank, and theta_j their source-indexed principal angles, including
zeros and right angles. For a nonnegative increasing penalty rho with rho(0)=0,
put `phi(t)=rho(2 sin(t/2))` and
`m_rho(theta)=min_(0<=delta<=theta)[phi(theta+delta)+phi(theta-delta)]`.
The proposed conclusion is

\[
\min_{UPU^*=Q}\operatorname{Tr}\rho(|I-U|)
=\sum_j m_\rho(\theta_j),
\]

with an actual independent-plane attainer fixing the unused common directions.
A basis-independent structural conclusion would pair gradient eigenspaces and
force the high-phase projections to satisfy AB=0 in every nonzero two-phase
block of any minimizer. That is the optimizer mechanism to prove alongside
the value formula; a complete family-wide parameter classification is separate.

A sufficient hypothesis proposed in the unverified fragment is: rho convex
and C¹, rho'(0)=0, rho'>0 on (0,2], rho C² away from zero, and phi' strictly
increasing up to one interior peak and strictly decreasing afterward, with
phi'' strictly negative on the decreasing branch. The relevant domain is
[0,2]; extension of rho outside it is immaterial to unitary displacement.

The proposed proof passes from stationarity to paired gradient eigenspaces.
Equal positive gradient levels have two phases a<b. The shared variation
`X=AB+BA` of their high-phase projections has zero low-phase compressions;
its Hessian is negative if AB is nonzero. This is the substantive no-mixing
step. After excluding overlap, an angle budget gives the planar lower bounds;
convexity controls the zero-gradient reflection sector.

**Status:** not a compiled generic theorem. The fragment's claim is a minimum
formula plus existence of an attainer; it does not itself classify every
optimizer. The Hessian identity needs a proved spectral differentiation
argument under the stated regularity, and all exceptional gradient levels,
common directions and multiplicities must be retained. Existing Schatten and
Charbonnier no-mixing proofs separately certify those cases.

### C2. One phase-transition surface for smoothed powers — derived scalar law

For `1<=p<=2`, tau>=0, define

\[
\rho_{p,\tau}(s)=(\tau^2+s^2)^{p/2}-\tau^p.
\]

In the regular subquadratic regimes (tau>0, `1<=p<2`, or tau=0,
`1<p<2`), the candidate complete scalar law is: for `0<theta<pi/2`
the minimizing absolute phase is unique; it is zero at and below the critical
angle and positive above it, where

\[
\cos\theta_c=
\frac{\tau^2+2-\sqrt{(\tau^2+2)^2-4p(2-p)}}{2p}.
\]

This formula is the correct curvature threshold. A common logarithmic-derivative
shape argument also supplies a conventional proof of the global scalar law;
the algebra and inequalities are in the
[unification note](spectral-transport-unification.md#the-smoothed-power-family-a-common-scalar-mechanism).
Thus the proposed transition is supported by more than a local curvature test.

At tau=0, p=1 the derivative-at-zero hypothesis fails and the nuclear optimum
is the boundary phase delta=theta. At p=2 the cost is quadratic for every tau:
zero phase is uniquely optimal at acute angles and every scalar phase is
optimal at a right angle. For p<2, the right-angle minimum is instead at
delta=pi/2. These boundary assertions agree with the existing proved formulas;
they are not an assertion that all endpoint optimizers are limits of interior ones.

**Status:** existing strict-Schatten, nuclear and Charbonnier scalar instances
are Lean-verified; the two-parameter statement and shared scalar proof are
conventional derivations awaiting formalization. C1 is additionally needed
to promote the scalar law to an unrestricted ambient optimum.

### C3. Nuclear signed roots and exact real compatibility — formally proved

Let H be a complete real or complex Hilbert space, K,L orthogonally
complemented subspaces, Delta=P_K-P_L trace class, and D an actual isometric
equivalence of the crossed defects. Set S=|Delta|, J=2P_K-I, C the canonical
cosine, R the completed direct rotation and V its established nuclear dual.
Then **every** transporter attaining `||I-T||_1=||Delta||_1` corresponds
bijectively to a bounded operator A satisfying

\[
A=A^*,\quad |A|=S,\quad [A,VC]=0,\quad JAJ=-A.
\]

The relative unitary is `Z=C+VA`, and `T=RZ*`. Over the reals, the equality
fiber is nonempty iff each `0<s<1` has even source multiplicity
`dim_R(K ∩ ker(S-sI))`, equivalently `4 | dim_R ker(S-sI)`.
The full/half dimension identity is proved for actual eigenspaces. Right-angle
blocks require no extra parity; the zero block has no root freedom.
In the complex case these are all global nuclear optimizers. When real parity
fails, each real transporter has strictly larger cost than the finite bound;
a uniform gap for the infimum is not asserted.

**Evidence:** `nuclearSignedSineEquivProjectionBoundAttainers`,
`nuclear_eq_projection_sub_iff_certificate`,
`exists_real_nuclear_transport_eq_projection_sub_iff_even_source_multiplicity`
and `finrank_sine_eigenspace_eq_two_mul_source_side_real` in the polar modules.
No separability or finite-rank hypothesis is imposed.

### C4. Real matching and finite field dependence — formally proved

For finite-dimensional real H, equal-rank K,L and `1<=p<2`, the unrestricted
orthogonal Schatten-power minimum is the exact matching functional on the
accepted principal angles, with an actual ambient attainer. At p=1 its value
equals the complex lower value `2 sum sin(theta_j)` iff every strictly acute
positive angle multiplicity is even. The matching theorem concerns all
orthogonal competitors, including mixing and both determinant classes.

**Evidence:** `RealTransport.realTransportPowerMinimum_eq_matching`,
`exists_minimizing_real_schatten_transport_matching_of_one_le` and
`realTransportPowerMinimum_one_eq_sine_sum_iff_even_multiplicities`.
It is a value/attainment theorem, not an all-real-optimizer classification.
C3 now explains its parity by complex structures on spectral half-spaces.
A new literal equality between the finite labelled angle counts and C3's
intrinsic multiplicity has not yet been added; both exact formulations compile.

### C5. Finite-to-Hilbert lifting and the ideal boundary — partly formal

A useful reusable lower-bound principle is available in proof form: let f be
continuous, increasing and nonnegative on [0,2], f(0)=0, finite f-cost imply
compact displacement, and m(theta) be continuous with m(0)=0. If every finite
complex transport satisfies the angle-sum lower bound for (f,m), the same
lower bound holds for arbitrary Hilbert-space transports, including infinite
costs. This is not an assumption of the infinite-dimensional conclusion.

For finite-cost U, the existing finite-rank unitary approximants U_n converge
in operator norm and have displacement singular values pointwise bounded by
those of U. Restrict U_n to its existing finite reducing transport section,
apply the finite theorem to **moving targets** U_n K, pass each
finite angle prefix to the limit, and take the supremum of prefixes. The
approximants need not preserve the original target L. This resolves a genuine
gap in a naive fixed-fiber compression argument.

Attainment requires another construction. If the scalar canonical regime
contains `[0,theta_c]` with theta_c>0, compact Delta has only finitely many
active sectors. Balanced defects and the finite attainer give an actual finite
correction of R. At the nuclear endpoint theta_c=0, use infinite signed-root
assembly instead. Classification of every Hilbert optimizer additionally
requires tail rigidity; it does not follow just from a finite formula.

**Evidence/status:** the lower-bound, finite correction and full classification
instances for strict Schatten and Charbonnier are compiled. Their common
abstract lifting principle is not yet packaged as a Lean theorem. For the
family, tau>0 gives quadratic near-zero comparison and hence S_2 feasibility;
tau=0 gives S_p feasibility. Both require zero relative defect index. The
ideal criterion is classical; the general family application remains to be
certified after C1. Explicit comparison constants appear in the unification note.

## Dependency diagram

Solid mathematical dependencies are shown; status labels are part of each node.

```mermaid
flowchart TD
  G[Classical projection geometry and transport fiber: proved] --> D[Gradient pairing and overlap descent: known instances proved]
  S[Family scalar shape and critical surface: derived, not formalized] --> F[C1 family finite decoupling: candidate]
  D --> F
  F --> L[C5 Hilbert lift and finite active attainment: candidate family; known instances proved]
  I[Classical ideal membership and defect index: proved] --> L
  U[Compact unitary approximation: proved] --> L
  T[Shared trace calibration: proved] --> R[C3 signed-root equality-attainer classification: proved]
  J[Orthogonal complex structures and spectral half dimensions: proved] --> P[Real parity criterion: proved]
  R --> P
  M[C4 unrestricted finite real matching: proved] --> E[Finite field-equality parity: proved]
  P --> X[Structural explanation of field compatibility]
  E --> X
```

## Closest published results and the contribution boundary

The [source-to-Lean map](spectral-transport-unification.md#source-to-lean-provenance-map)
contains exact declarations and authentication limits.

| Predecessor | Verified comparison | What could extend it here |
| --- | --- | --- |
| Jordan (1875), §§46–50; Davis (1958), Theorems 7.1, 7.3, 7.4 | Classical angular geometry and canonical operator/Hilbert--Schmidt/Schatten p>=2 extremal theory. | Exact subquadratic phase selection and its field compatibility, not invention of angles or direct rotation. |
| Davis–Kahan (1970), Propositions 4.3–4.4 and examples | Squared displacement, norm-scope failure and the printed real short-angle assertion. Original wording here relies on the repository's prior source audit. | Formal correction with exact scope, followed by an optimization theory beyond the false assertion. |
| Bolotnikov–Li–Rodman (2001), Problem 1.1; Theorems 3.1, 4.2, 4.5; Lemma 3.3 | The ambient distortion problem, Q-norm theory, complete Frobenius minimizers and a special subquadratic phase example. Theorem 4.5's chain compatibility condition is automatic for a single subspace pair. | The subquadratic/smoothed solution theory and C1 if proved. The optimization problem itself is prior art. |
| Qiu–Zhang–Li (2006), §5; Zhang–Qiu (2010), §4 p. 1615 | Grassmann/logarithmic objectives and explicit trace-norm nonminimality. | Exact extrinsic optimizer classifications, not a new discovery that direct rotation can fail for the trace norm. |
| Avron–Seiler–Simon (1994), Proposition 3.1; Kaftal–Loreaux (2017), Proposition 2.7(ii) | Relative index and exact proper-ideal restricted-unitary feasibility on separable complex Hilbert space. | Formal real/nonseparable scope and a penalty-specific optimizer solution above those classical ingredients. |

The BLR statements above were rechecked in the
[official primary paper](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117).
Positive-smoothing costs are nonhomogeneous, so Q-norm minimality alone
does not supply their transport formula.
The exact matching, equality-attainer and classification claims remain
**potentially novel**, with no equivalent found in the sources actually examined.
This is not evidence of first priority. Authenticate Aubrun–Szarek Exercise B.12
and resolve the remaining exact predecessor comparisons before making a strong
novelty claim. Halmos and early Sz.-Nagy/Kato attributions retain the recorded
original-source authentication limitations.

## Proposed abstract, supported by the current proved core

We study unitary and orthogonal transport between spectral subspaces by
minimizing spectral penalties of the ambient displacement. For complex Hilbert
spaces we give exact optimizer descriptions for subquadratic Schatten powers,
the nuclear endpoint and smoothed nuclear penalties. The regular regimes
select phases on a finite active angle spectrum, while nuclear equality
attainers admit an independent signed-root parametrization in arbitrary rank.
This parametrization works over both scalar fields. Over the reals its
solvability is equivalent to even multiplicity on every strictly acute
source-side sine eigenspace, explaining the parity condition in the finite
orthogonal matching problem. Operator-ideal membership and balanced crossed
defects specify finite-cost feasibility. The results connect penalty-dependent
phase selection, real compatibility and infinite-dimensional attainment within
one transport-fiber variational problem.

This abstract claims the proved regimes. C1/C2 across the full two-parameter
family would strengthen its central assertion after verification.

## Theorem-level outline and the next proof decision

1. **Classical geometry and the variational fiber.** Definitions, angle data,
   Q-norm boundary, source correction, ideal feasibility and attribution.
2. **Penalty selection.** C1 finite decoupling, C2 family phase law and exact
   boundary regimes. Keep the ambient and scalar theorems distinct.
3. **Field compatibility.** C3 nuclear equality geometry and C4 finite real
   matching; explain the real complex-structure obstruction.
4. **Infinite-dimensional assembly.** C5 lower-bound lift, finite active
   corrections and the different nuclear infinite-product mechanism.
5. **Consequences and boundaries.** Include only consequences needed to explain
   the theory; state real above-bound and endpoint set-limit limitations.

The verified narrower nuclear/strict-Schatten/Charbonnier core is mathematically
self-contained and cohesive enough to organize a paper. Further unrestricted
real classification, topology or broad stability is not a publication gate.
Historical comparison still needs resolution, and a paper claiming C1 or the
full smoothed-power law needs further proof.

**Next campaign:** formalize C1 for the concrete family using one shared
gradient/overlap argument, and C2 using the shared scalar shape calculation.
Then package the already-used C5 lower-bound lift and instantiate the family.
For tau>0 the phase-gradient extension is analytic near the unit circle; for
tau=0 the existing strict-exponent treatment handles the identity singularity.
Use continuity of finite minima to include the nonsmooth nuclear value, with
C3 supplying its optimizer geometry. Prove these organizing statements before
adding optional consequences. A fully generic C²-penalty theorem can follow
if it simplifies this proof rather than becoming a separate prerequisite.
Write the family theorem signatures first, then add only the scalar and
operator lemmas needed for those public conclusions.
