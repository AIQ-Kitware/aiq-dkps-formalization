# How far can an eigenvector turn?

A standalone, TTS-ready transcript for the numbered `sine-theta-lecture`
edition of the eighteen-scene `sine-theta-short` reference talk. The expanded
narration runs longer than the fifteen-minute live presentation. The two
closing study questions live in `quiz.yaml` and are included by the common
lecture/video pipeline.

The deck presents the Davis-Kahan sin Theta theorem — its statement, the
mechanism behind it, and its exact Lean form — plus another project
result: an agent-assisted counterexample to the Proposition four point
four claim in the 1970 paper.

The audience is a specialist who knows linear algebra and basic numerical
eigenvalue problems and wants the theorem statement, the mechanism behind
it, the exact Lean form, and what the formalization changed. A local
notation refresher appears on the second slide, so no earlier video is
needed.

Mathematical sources: C. Davis and W. M. Kahan, "The rotation of
eigenvectors by a perturbation. III," SIAM J. Numer. Anal. 7 (1970); the
Lean formalization in this repository (`DavisKahan/`, `ForTauCeti/`); the
journal article in `papers/dk_formalization_journal/`.

Notation used throughout: A hat is the operator under study; in the
perturbation specialization, A hat equals A plus H, with A the original
operator and H the perturbation. E zero is the trial frame and A zero the
trial-coordinate operator; F zero is the exact wanted frame, F one the
exact unwanted frame, and Lambda one the exact unwanted block, with
A hat F one equal to F one Lambda one. R, defined as A hat E zero minus
E zero A zero, is the residual. delta is a certified spectral
separation, not a generic eigengap; g is the original eigengap in the
perturbation example. In finite dimensions, Theta zero records the principal angles; in the
Hilbert-space statement it is an angle operator, not necessarily a finite
list. Sin Theta zero is its positive directed sine on trial coordinates. Star is transpose in the real case and conjugate
transpose in the complex case. U and V appear only in the Proposition
4.4 slides, where that statement itself uses them for the two
subspaces.

Authoring provenance: this transcript was authored on 5 November 2026 by
`qwen3.8-27b-dbirks-hyperqwen-long` (served through the local LiteLLM
proxy; pi agent) from the presenter narration embedded in the frozen
reference scenes: fifteen of the eighteen scenes in
`dkvis/slides_sine_theta.py` (last touched by commit `595e6a9fb`,
4 November 2026), `D01Planes` in `dkvis/slides_sine_theta_3d.py` (same
commit), and `P01Claim`/`P02Counterexample` in `dkvis/slides_prop44.py`
(last touched by `bcfe89afb`, 8 October 2026). The deck composition is
the frozen reference `SHORT` deck in `dkvis/decks/reference.py` (last
touched by `a3358dd63`, 9 October 2026). The numbered edition uses those existing visual bodies with an adapter that
binds each authored beat to its corresponding animation build. Its title has
a short spoken opening and the shared robot/model disclosure. The original
reference composition retains its own visual and presenter-note behavior.
The integration and the corrections listed in `provenance.yaml` were authored
by GPT-6.1-Sol; Qwen's transcript and quiz authorship are retained separately.

## S00TitleShort: How far can an eigenvector turn?

Why: Name the single question that organizes the whole talk.
Recall: No notation is needed on the title slide.

How far can an eigenvector turn?

## S00bSetting: The setting: self-adjoint operators

Why: Fix the class of operators before measuring angles.
Recall: A hat is the operator under study; in the perturbation slides A is the original operator.

First, the setting. Everything here is about self-adjoint operators:
the inner product of A x with y equals the inner product of x with A y
for vectors in the domain. For an unbounded operator, self-adjointness
also requires the operator and its adjoint to have the same domain; the
inner-product identity alone expresses symmetry.
For a real matrix that is just a symmetric matrix, the innermost box on
the slide.

<!-- beat -->

For a finite-dimensional symmetric or Hermitian matrix, the spectral
theorem gives real eigenvalues and orthogonal eigendirections: a pure
stretch along perpendicular axes. In infinite dimensions the
corresponding object is a decomposition into spectral subspaces;
eigenvectors need not span the space. The class grows outward: complex
Hermitian matrices, bounded operators on a Hilbert space, possibly
infinite-dimensional, and unbounded ones like differential operators.

<!-- beat -->

The sin Theta pictures in this talk live in the innermost box: two-by-two
and three-by-three real symmetric matrices, and the Proposition four point four
counterexample at the end lives in R four. Davis and Kahan, and our Lean
theorem, cover the outermost box, on separable Hilbert spaces. And these
objects are everywhere: covariance matrices, graph Laplacians, quantum
Hamiltonians.

## S01Ellipse: Picturing a symmetric matrix

Why: Build a geometric picture of a symmetric operator before perturbing it.
Recall: A is the original operator in this example, drawn in tan; its eigenvectors are the thick tan arrows.

Picture a symmetric matrix by what it does to the unit circle. This is
a worked example: the matrix is positive definite, with eigenvalues two
and one. The grey arrows are arbitrary unit vectors. The thick tan
arrows are the two eigenvectors, tan being the color of the original
operator A.

<!-- beat -->

Apply A. Generic vectors are stretched and turned. The eigenvectors are
only stretched: A f equals lambda f.

<!-- beat -->

So the ellipse's axes point along the eigenvectors, and in this example
the semi-axis lengths are the eigenvalues, two and one. For a general
symmetric matrix the semi-axes are the absolute values of the
eigenvalues. An eigenbasis gives a compatible choice of axes; repeated
absolute eigenvalues can hide the individual eigendirections in the
ellipsoid picture. In n dimensions the picture is an ellipsoid.

## S02Perturb: Perturb the matrix

Why: Turn the picture into the talk's question: eigenvalues are stable under small perturbations, eigenvectors are not obviously so.
Recall: A is the original operator, drawn in its own eigenbasis; A hat equals A plus H, with H small and symmetric.

Start from the same ellipse, drawn with its axes, written in the
eigenbasis of A: A is diagonal with entries two and one, and H is
epsilon times the off-diagonal matrix, with epsilon equal to zero point
one two.

<!-- beat -->

The ellipse of A hat is almost the same ellipse: the eigenvalues barely
move. Weyl's inequality, in the footnote, says that after sorting the
eigenvalues of A and of A hat, each one moves by at most the operator
norm of H, written with the subscript op: the most H stretches any unit
vector. The Frobenius norm instead takes the square root of the sum of
squared singular values; it is also called the Schatten two norm. It holds for every
symmetric A, with no gap needed. Eigenvectors get no such guarantee.
And indeed the axes turn, by an angle theta.

<!-- beat -->

That boxed sentence is the question of the talk: how far can the
eigenvectors, or more generally an invariant subspace, turn? Eigenvalue
perturbation is easy, thanks to Weyl. The eigenvector question is the
one that needs a theorem.

## S03bWanted: Which eigenvectors do we want?

Why: The error being measured must be attached to a chosen part of the spectrum, not to all of it.
Recall: F zero is the exact wanted frame, F one the exact unwanted frame; E zero is a trial frame to be compared against F zero.

Before measuring errors: which eigenvectors are we even after? Rarely
all of them. For a small dense matrix we could compute every
eigenvector, but many applications produce enormous sparse matrices,
often by discretizing a differential operator, so eigensolvers compute
only the few modes the application asks for: the lowest vibration modes
of a structure, the lowest-energy states of a quantum Hamiltonian, the
smallest Laplacian modes in spectral clustering, the leading directions
in PCA.

<!-- beat -->

Those chosen eigenvalues are the wanted ones, shown in blue; their exact
eigenvectors, collected as columns, are F zero. Everything else is
unwanted, in cyan; those exact eigenvectors are F one. For a vibrating
string, for example, the lowest modes are wanted. The next step is to
compare a trial frame E zero against the exact wanted frame F zero.

## S03NoGap: How far can an eigenvector turn? It depends if there is a gap

Why: Show that without a spectral gap, eigenvector stability fails even for a fixed small perturbation.
Recall: g is the original eigengap of A; H is fixed with norm zero point one two; theta is the turn of the top eigenvector of A hat.

Set up the experiment. The tan dashed ellipse is the original A; its
eigenvectors are drawn as the lines they span, because an eigenvector
only matters up to sign and length, and the dots where the ellipse
crosses them mark the corresponding eigenvalue scales in this positive example. Below, the same two eigenvalues on a
number line; the violet bracket is the gap g between them. The solid
steel ellipse is A hat, that is A plus H, for a fixed small H of size
zero point one two; its top eigenvector, in blue, is turned by theta. On
the right, theta as a function of the gap.

<!-- beat -->

Now make A more and more round: its two eigenvalues slide together and
the gap closes. The blue and cyan ticks, the eigenvalues of A hat,
never move more than zero point one two from the tan dots, the
eigenvalues of A: that is Weyl. But the wanted eigenvector of A hat
swings toward forty-five degrees, however small H is. The same small H
throughout: the eigenvalues move by at most the norm of H, while the
eigenvector turns further and further as the gap closes.

## S03cUnstable: Without a gap, an eigenvector can point anywhere

Why: At zero gap a single eigenvector is not a meaningful object; the stable object is the eigenspace.
Recall: g is the original gap; H of phi is a perturbation of fixed size zero point one two whose direction rotates.

Two copies of the same experiment. Left: A has a clear gap. Right: A is
almost round. Both use the same rotating perturbation H, whose size
stays zero point one two while its entries change; the live matrix
shows them. Watch the two wanted eigendirections rotate at the same
time.

<!-- beat -->

With a gap, the top eigenvector of A hat moves only slightly; its
traced fan is narrow. With almost no gap, it can turn in every
direction, and the same rotating H produces both outcomes. The
eigenvalues in either panel still move by at most zero point one two.

<!-- beat -->

Here is a concrete flip, as matrices: one, epsilon over epsilon, one,
versus one, minus epsilon over minus epsilon, one. Their difference has
operator norm two epsilon, yet their leading eigendirections are the two
diagonals, ninety degrees apart, for every epsilon greater than zero. In this two-by-two example
the switch happens when the size of H passes half the gap: below it the
eigenvector only wobbles, above it some H of that size points it
anywhere.

<!-- beat -->

With A exactly round, A is a multiple of the identity, and every line
is an eigenvector: there is no "the" eigenvector to be stable. What is
stable is the whole eigenspace. So Davis and Kahan work with subspaces:
all the eigenvectors of an isolated cluster of eigenvalues. That is the
object the theorem measures.

## S04Angle: Measuring the error from two frames

Why: Define the error quantity the theorem bounds, from the two frames alone.
Recall: E zero is the trial frame, F zero the exact wanted frame, F one the exact unwanted frame; sin Theta zero of E zero, F zero is the directed sine of the principal angles between their ranges.

The perturbation model, A hat equals A plus H, was one way to obtain two
subspaces. The general sin Theta theorem does not require an original A
or any H. It starts with an operator A hat and a comparison frame E
zero. The comparison frame might be a numerical guess, or the true
eigenspace of a latent A in a perturbation application. The exact
wanted invariant frame F zero of A hat is the reference for the
conclusion. Either way, we want to compare the ranges of E zero and F
zero. How should we measure their error?

<!-- beat -->

In this one-dimensional picture, project the trial column E zero onto
the exact wanted line spanned by F zero. The part left outside that line
has length sin theta. In this one-dimensional case, the error is the norm of
(I minus F zero F zero star) E zero, which equals sin theta: F zero F
zero star is the projection onto range F zero, star being transpose in
the real case and conjugate transpose in the complex case. The formula
already has the same algebraic form as the operator used in the
theorem.

<!-- beat -->

Move the trial frame around, and the pink leg is the error: it vanishes
when the two ranges agree, and reaches one when they are orthogonal. The
same definition works for the frames themselves, without ever giving the
ranges separate names.

<!-- beat -->

For k columns, E zero and F zero determine k principal angles, and the
directed sin Theta zero operator is a function of those two frames
alone. The rectangular blocks (I minus F zero F zero star) E zero and F
one star E zero have the same singular values, because F one F one
star is I minus F zero F zero star; so they take the same value in
every unitarily invariant norm, and a proof may compute with either
block.

<!-- beat -->

That is the error we seek to bound. In a computed residual problem E
zero can be known, while in a latent-truth perturbation problem E zero
can be unknown; the formula for the angle applies to both. Next we will
study the invariance defect, or residual.

## S05Residual: A computable signal: the residual

Why: The error needs the exact frame we do not have; the residual does not.
Recall: v is a trial unit vector, the one-dimensional frame E zero is its single column, rho is its scalar trial operator, and F zero is the exact wanted frame, unknown.

The information model is the point. A hat is the operator we are
studying. The trial vector v is ours; in one dimension it is the single
column of E zero. The exact frame F zero is what we do not know, so the
true angle is not available directly.

<!-- beat -->

So ask something testable: if v were an exact eigenvector of A hat, then
A hat v would point along v. The failure of that statement is the
residual.

<!-- beat -->

For this eigensolver-style example, the Rayleigh quotient rho, equal to
v star A hat v, is the natural scalar action on the trial line; other
applications can supply the trial operator A zero differently. Split A
hat v into the best scaling, rho v, plus the leftover r. Computing r
needs A hat and v, but no F zero. That is why residuals are useful as a
posteriori information from an eigensolver.

<!-- beat -->

Along the improvement toward the wanted direction shown here, both
quantities shrink. A small residual alone does not identify that wanted
direction: the unwanted exact eigenvector also has zero Rayleigh residual.
We can monitor the residual, but selecting the target requires spectral
information as well as a small residual.

<!-- beat -->

For several columns, replace v by the trial frame E zero and rho by the
small trial operator A zero: the residual is R equals A hat E zero
minus E zero A zero. With the Rayleigh-Ritz choice, A zero is E zero
star A hat E zero; in the perturbation application, A zero instead
comes from the exact wanted eigensystem of the original A. In either
case, R measures how well the trial frame and its chosen operator satisfy
A hat E zero equals E zero A zero. The
theorem asks whether a small, directly formed R, together with spectral
separation, certifies a small angle to the exact frame F zero.

## S06Gap: The spectral separation delta

Why: State the second hypothesis of the theorem: a certified clearance between the trial spectrum and the exact unwanted spectrum.
Recall: A zero is the trial-coordinate operator with spectrum inside the interval [beta, alpha]; Lambda one is the exact unwanted block, A hat F one equals F one Lambda one.

The number line is the real axis of eigenvalues. In amber: the
eigenvalues of the trial matrix A zero, inside an interval from beta to
alpha.

<!-- beat -->

Widen that trial-spectrum interval by delta on each side: the violet
window. F one is the exact unwanted frame of A hat, and Lambda one is
the operator on those unwanted coordinates: A hat F one equals F one
Lambda one. The hypothesis says that the exact unwanted spectrum stays
out of the window. delta is a certified lower separation, the theorem
needs a certificate rather than the exact value, and the roles of A
zero and Lambda one may also be exchanged.

<!-- beat -->

Two distinctions to keep clean. First, delta is not the original
eigengap g from the perturbation example: g measures the original
operator A, while delta measures a clearance between the trial spectrum
and the exact unwanted spectrum. Second, the hypothesis is an interval,
not "every pair of eigenvalues is delta apart": if the two spectra
merely interleave with pairwise separation, the bound with constant one
is still guaranteed in the Hilbert-Schmidt, or finite-dimensional
Frobenius, norm, as in Davis-Kahan Theorem six point two. Pairwise
separation alone does not guarantee it in operator norm; Section five of the paper
gives an explicit two-by-two example.

## S07Theorem: The sin Theta theorem

Why: State the main result and read it as an information flow.
Recall: sin Theta zero of E zero, F zero is the directed sine of the principal angles; R equals A hat E zero minus E zero A zero; delta is the certified separation.

Now the relationship becomes useful. E zero and A zero are the trial
data, F zero is the exact wanted frame, and R is the residual, A hat E
zero minus E zero A zero. Under the stated interval/exterior separation, or its ordered half-line
versions, with positive delta, Davis-Kahan bounds the unknown angle
to F zero: delta times the norm of sin Theta zero of E zero, F zero, is
at most the norm of R, in every unitarily invariant norm where
the compared norms are finite. The unbounded version also retains the
domain and bounded-residual hypotheses shown in the Lean statement.

<!-- beat -->

Read this as an information-flow statement. The target error needs F
zero, the exact frame we usually do not have. The residual is formed
directly from A hat, E zero, and A zero. delta is different: it is a
spectral-separation certificate that must be established separately.

<!-- beat -->

Rearranged: the subspace error is at most the residual norm divided by
the spectral separation, error at most residual over separation. Notice
what is absent: there is no original A and no perturbation H in the
theorem itself. A hat is simply the operator whose exact wanted frame F
zero we want. After explaining the residual mechanism, we add the perturbation
structure, A hat equals A plus H.

## S08Why: Why it is true

Why: Give the one-dimensional mechanism behind the theorem.
Recall: f zero is an exact wanted eigenvector, f one an exact unwanted eigenvector, lambda zero and lambda one their eigenvalues, rho the trial scalar, delta the separation certificate.

Why should a small residual force a small angle? In the one-dimensional
exact split, call the wanted eigenvector f zero and an unwanted one f
one. Split the trial vector v into those exact directions. The pink
unwanted component has length sin theta: how much of v points the wrong
way.

<!-- beat -->

Now the residual. A hat minus rho, applied to v, multiplies each exact
eigendirection by its eigenvalue minus rho. So the unwanted component
becomes (lambda one minus rho) sin theta. The separation certificate
says that factor has magnitude at least delta: lambda one is at least
delta from rho, which is the trial spectrum in this rank-one example.

<!-- beat -->

The whole residual may also have a wanted component along f zero, since
rho need not equal lambda zero; that can only make it longer. So the
length of r is at least its f one component, which is at least delta sin
theta: the part of v pointing the wrong way always shows up in the
residual, scaled by at least delta, whenever the unwanted spectrum is
separated. For whole subspaces the same spectral-separation idea becomes
a Sylvester equation, and getting the sharp constant for every
unitarily invariant norm is the technical part of the full theorem.

## S11Payoff: Back to perturbations: where H enters

Why: Specialize the general theorem to the perturbation application of the opening example.
Recall: A hat equals A plus H; E zero and A zero come from the exact wanted eigensystem of A; g is the original eigengap of A; delta is the theorem's separation, a different quantity from g.

Now add the perturbation relationship: A hat equals A plus H. In a
statistical application, A is the latent true matrix and A hat is the
observed estimate. E zero is a true eigenframe of A, even if we do not
know it, and F zero is the eigenframe calculated from A hat. The proof
uses A E zero equals E zero A zero, whether or not those objects are
observable. Then R, which is A hat E zero minus E zero A zero, reduces
to H E zero; because E zero has orthonormal columns, right-multiplying
H cannot increase a unitarily invariant norm, so the norm of R is at
most the norm of H, and the norm of sin Theta zero of E zero, F zero is
at most the norm of H over delta, where delta separates the spectrum of
A zero from the spectrum of Lambda one.

<!-- beat -->

Back to the two-by-two example with epsilon equal to zero point one
two. The pink curve is the sine of the angle between range E zero, the
original wanted frame, and range F zero, the exact wanted frame of A hat.
The pink arc on the ellipse shows the angle itself. Green dashed
is the general residual-over-separation bound. The horizontal variable
g is a different quantity: the original eigengap of A.

<!-- beat -->

Keep g and delta separate. Here g compares the wanted and unwanted
eigenvalues of the original A; delta compares the spectrum of A zero,
the old wanted block, with the spectrum of Lambda one, the new unwanted
block of A hat. In this example those behave differently as g
collapses.

## D01Planes: The same picture in three dimensions

Why: See the subspace, not just vector, formulation in a concrete geometry.
Recall: F zero spans the exact wanted plane, F one the exact unwanted direction, Lambda one the one-by-one block holding lambda three; R equals A hat E zero minus E zero A zero.

Same story, one dimension up. This A hat has positive eigenvalues, so it
maps the unit sphere of R three to an ellipsoid. The exact wanted frame
F zero, with columns f one and f two, spans the plane of the two short
axes. F one, the single column f three, spans the exact unwanted
direction, and Lambda one is the one-by-one block containing its
eigenvalue, lambda three.

<!-- beat -->

Now range E zero is a trial plane, tilted by theta about a line lying in
range F zero. Two distinct planes through the origin in R three meet in a line, so the
principal angles between them are (theta, zero).

<!-- beat -->

So the directed sine has at most one nonzero singular value. Its operator
norm, equal to the operator norm of F one transpose E zero, is sin theta, the pink drop from the
tilted trial direction down to range F zero. Other unitarily invariant norms use the same singular-value list; with
rank-one normalization, they also give sin theta.

<!-- beat -->

With the Rayleigh-Ritz trial matrix, A zero equals E zero transpose A
hat E zero, we get E zero transpose R equals zero: the residual of each
trial vector sticks straight out of the trial plane, at right angles.

<!-- beat -->

The whole configuration, orbiting. This is a VTK render of the live
demo; it loops.

## S12Lean: What we formalized: the full Lean theorem

Why: Connect the spoken theorem to the exact object the proof checker accepted.
Recall: Lean's A is this talk's A hat; the talk's original A and perturbation H exist only in the perturbation specialization.

This is the actual Lean statement of the sin Theta theorem, complete:
the real object the proof checker accepted. Nobody should read it token
by token; the point is its shape.

<!-- beat -->

Reading it: real or complex scalars; separable Hilbert spaces, finite-
or infinite-dimensional; unitarily invariant norms on their domains of finiteness; possibly
unbounded self-adjoint operators; the paper's residual, spectral
decomposition, and separation hypotheses; and the conclusion that delta
times the norm of sin Theta zero of E zero and F zero is at most the
norm of R. The statement is shown with instance-binder names dropped
and lines re-broken; the directed sine is spelled in the Lean source as
source directed sin theta operator of E zero, F zero. The highlighted
labels translate Lean's ambient A into this talk's A hat without
changing the Lean source text.

## P01Claim: A second result: Proposition four point four is false

Why: Introduce the printed claim that the formalization refuted, in the same geometric language as the first result.
Recall: U and V are the two subspaces of this statement; W is an orthogonal map; I minus W is the displacement.

Now turn to another result from the project. Take two subspaces, U and V. Many
orthogonal maps carry U onto V. Davis and Kahan single out the direct
rotation: it turns by exactly the principal angles and does nothing
else.

<!-- beat -->

A reflection across the bisector also carries U onto V, but it moves the
other direction across the plane. The pink segments show how far each
vector moved.

<!-- beat -->

Proposition four point four, as printed, says: over the reals, if every principal
angle is at most pi over three, then among all orthogonal W with W of U
equal to V, the direct rotation minimizes the norm of I minus W, in
every unitarily invariant norm. A norm turns I minus W, the
displacement matrix, into a measure of size; different norms combine
motion across directions differently, and the printed claim says the
direct rotation wins for every one. In the plane this is right, which
makes it believable.

<!-- beat -->

But as printed it is false, and the formalization can exhibit the
counterexample.

## P02Counterexample: The counterexample in R four

Why: Exhibit the explicit maps and the norm in which the printed claim fails.
Recall: R is the direct rotation, W the competitor; both are orthogonal, both carry U onto V, and both principal angles are pi over four.

Here are both maps, each shown in its own invariant-plane decomposition.
These are different decompositions for the two maps. The direct
rotation turns two planes by forty-five degrees each. The competitor
turns one plane by ninety degrees and leaves the other fixed. Both
carry U onto V, and both principal angles are forty-five degrees,
inside the claimed sixty-degree limit. Measure each map by the norm of
I minus T, the size of its displacement; norms differ in how they
combine motion across directions.

<!-- beat -->

A plane turned by an angle alpha contributes two equal singular values
of I minus T: the chord, two sin(alpha over two). The trace norm adds
all four chord lengths. The direct rotation has four chords of about
zero point seven six five; the competitor has two chords of about one
point four one four, plus two zeros.

<!-- beat -->

The operator norm looks at the worst single displacement, the
Frobenius norm at the root sum of squared displacements, and the trace
norm at their sum. The first two norms favor the direct rotation; the
choice of norm matters.

<!-- beat -->

The highlighted trace-norm row is where the printed proposition fails:
three point zero six one is greater than two point eight two eight. The
competitor moves space less by that measure, even though both maps carry
U onto V with the same principal angles. The claim that the direct
rotation minimizes for every unitarily invariant norm is therefore false
as printed.

## S14Summary: What to take away

Why: Close with the three lessons the project supports, with their mathematical qualifications.
Recall: the subspace error is the norm of sin Theta zero of E zero, F zero; R is the residual; delta is the certified separation; a Q norm is a norm whose square is a unitarily invariant norm of the squared modulus.

Three takeaways. First, LLMs can formalize substantial mathematics: of
the twenty-nine counted result statements in Davis and Kahan’s
nineteen seventy paper, twenty-eight are formalized in Lean, and the remaining
proposition was refuted as printed and repaired; the work is Hilbert-
space functional analysis, including infinite-dimensional and unbounded
operators. Second, sine theta gives an error bound: under the stated interval/exterior or ordered half-line gap
hypotheses, with positive delta and the required domain and norm conditions, the subspace error, the norm of sin Theta zero of E
zero, F zero, is at most the residual norm divided by that separation;
it limits how far the trial eigenspace can deviate, even if the exact
one is unknown. Third, a classical statement was too broad: LLM-assisted
review found a counterexample to Proposition four point four's claim
for every
unitarily invariant norm. The impact is limited: the direct rotation is
still optimal for acute pairs and Q norms, including the operator and
Frobenius norms, over the reals or the complex numbers, without the
paper's sixty-degree cutoff.
