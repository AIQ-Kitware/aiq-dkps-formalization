# Rayleigh–Ritz: trial spaces, compression, and residuals

Authored by GPT-6.1-Sol. Mathematical and Lean correspondence: `sources.md`.

## RrTitle: Rayleigh–Ritz

Why: A smaller eigenproblem may give useful information about the full one.
Recall: A trial space is a candidate search space.

Rayleigh–Ritz: trial spaces, compression, and residuals.

## RrSetup: How can a smaller problem help?

Why: The subspace, its coordinates, and the small operator have different jobs.
Recall: An orthonormal frame has mutually perpendicular unit columns.

How can a small eigenproblem tell us something reliable about a much larger one? Solving fewer equations sounds attractive, but why should their answers say anything about the original operator? We will investigate that question through one approximation. The possible starting point is a small space of candidate directions. The questions are what action we can represent there, what its eigenvectors mean in the full space, and what error remains. Our setting is a real symmetric matrix A; the same matrix argument uses adjoints for complex Hermitian matrices. What does choosing a space of candidates actually give us?

## RrQuestion: Why search in fewer directions?

Why: A restricted search can be affordable even when the full problem is not.
Recall: Eigenvectors satisfy A u equals lambda u.

What could we do if applying A were affordable, but solving its entire eigenproblem were too expensive? An eigenvector is a direction that A only scales. Perhaps some useful directions can be found among combinations of a much smaller set of vectors. The large array represents A. The amber array represents the smaller problem we hope to build from those candidates. Its size would make it easier to solve, but size alone tells us nothing about its reliability.

<!-- beat -->

What should connect that small problem to the original one? It should preserve a meaningful measurement of the allowed directions, and its proposed eigenvectors should come with a check in the full space. Rayleigh’s work on vibration and Ritz’s variational approximation method are historical landmarks behind this strategy. Our route follows those two needs: a meaningful restricted search, then a check of what it misses. The first question is what vectors that search allows.

## RrSpace: What does a trial space allow?

Why: The name describes a role, not an accuracy theorem.
Recall: A subspace contains every linear combination of its vectors.

If two promising directions are available, why search only along those two arrows? Their combinations may contain a better candidate. The amber sheet shows all combinations of q one and q two. Changing the coefficients moves the trial vector around this plane. This whole collection is the trial space: it specifies the candidates our smaller problem is allowed to consider. Higher-dimensional trial spaces serve the same purpose.

<!-- beat -->

Does having a trial space already make the approximation good? We have only chosen where to search. A might send vectors out of the plane, and the plane might miss the spectral space we want. Invariance would mean that A always stays inside it; accuracy would require a comparison with our exact target. Neither follows from the choice alone. To investigate what A does to these candidates, how could we describe them with only two numbers?

## RrFrame: How do two numbers describe a trial vector?

Why: We need a way to move between a small vector and its ambient representative.
Recall: Q has orthonormal columns: Q transpose Q equals the small identity.

How can the smaller problem describe an ambient vector without storing all its coordinates? The two coefficients along our orthonormal trial directions are enough. Q turns those coefficients into the ambient vector u equals Q y. The moving dots represent the same vector in its two descriptions. Both have norm one; the right circle looks flattened only because the trial plane is drawn in perspective. Q preserves lengths because its columns are orthonormal. That will let a small-space calculation retain the geometry of its trial vectors.

<!-- beat -->

What if A produces a vector that lies outside the plane? The cyan vector v illustrates that possibility. Q transpose reads its coefficients along the trial directions. Lifting those coefficients back gives the point underneath v in the plane, its orthogonal projection. Thus P equals Q Q transpose. We now have a way to lift a small input and a way to read the trial part of any output. Could those two operations turn A into a useful small model?

## RrCompress: What action can the small model represent?

Why: A trial vector can leave the search space when A acts on it.
Recall: P equals Q Q transpose; Q transpose Q is the identity.

What should a two-coordinate model do with a trial input? Ideally, it would reproduce A’s output. But its answer must be another pair of coordinates, so after lifting, it must lie in the trial plane. The question is whether A’s action can be described that way at all. The amber arrow is q one, one of our allowed inputs. What happens when A acts on it?

<!-- beat -->

Applying A gives the cyan arrow, which leaves the plane. So an exact description of every full output is already impossible using only the two trial directions. What information is still available to a small model? The component along those directions can be recorded. The perpendicular part cannot. Our coordinate reader Q transpose suggests a way to separate them.

<!-- beat -->

What if we read the trial coordinates of the full output? Q transpose gives the trial coordinates of A Q y. The resulting map is Q transpose A Q, which we name B. Each factor now answers a need: Q places the candidate in the full space, A acts on it, and Q transpose records the part our small model can express. This construction is called compression. It was forced by asking which part of the output our chosen coordinates can retain.

<!-- beat -->

What does that answer mean back in the original picture? Its lift Q B y is P A Q y, the amber projected output. The green arrow completes the trip from that output to the cyan one. B describes the in-plane action, while green records what it leaves out. This explains how B was constructed. To justify using its eigenproblem, we still need to know whether it preserves a meaningful measurement of our candidates.

## RrQuotient: Which measurement does compression preserve?

Why: The small eigenproblem needs to represent A’s directional measurements.
Recall: For a unit vector u, the Rayleigh quotient is u transpose A u.

Does the small model judge trial directions the same way as A? For a unit vector u, the Rayleigh quotient u transpose A u measures the component of the output along the input. In our example, B has diagonal entries two and off-diagonal entries one. What if we compare this measurement as the candidate direction changes? The unit coordinate vector turns around the trial plane, and the graph records the original quotient. It reaches three in the sum direction and one in the difference direction. Would the small calculation trace the same curve?

<!-- beat -->

The two descriptions u equals Q y give a way to answer that without testing directions one by one. Substitution turns u transpose A u into y transpose Q transpose A Q y, exactly y transpose B y. The full and compressed calculations give the same curve on every trial direction. Compression therefore preserves the entire directional measurement over our chosen search space. Finding its extremes with B really does solve the restricted variational problem for A.

<!-- beat -->

Can B also be treated as a symmetric eigenproblem? Symmetry is preserved too: transposing B replaces A by A transpose, which equals A. Its extremal eigenvectors therefore identify the highest and lowest points of that quotient curve. We now have a reason to solve the small eigenproblem. But does a direction that B only scales remain such a direction when the full operator acts?

## RrSolve: Does a small eigenvector solve the full problem?

Why: Small eigenvectors describe combinations of the trial directions.
Recall: B y equals theta y is a k-dimensional eigenproblem.

What can an exact eigenvector of B tell us about A? The difference direction, with coordinates one and minus one divided by square root of two, is an eigenvector of our small matrix with eigenvalue one. That eigenvalue is called a Ritz value, written theta. The small equation is solved exactly. The remaining question is what that solution says about the corresponding ambient direction.

<!-- beat -->

Could its lift be an eigenvector of A? The amber arrow u equals Q y is the lifted vector, called a Ritz vector. It has norm one. Lifting the small equation gives P A u equals one times u. Thus the projected output lands on the input arrow with scale one. This is encouraging, but the equation has only checked the part of A’s output inside the trial plane.

<!-- beat -->

What did that projection leave unchecked? The full operator gives the cyan output outside the plane. The green difference is r equals A u minus theta u, the full eigenpair residual. It measures precisely the failure of the candidate to satisfy the original eigenvector equation. A small eigenproblem can be solved perfectly and still leave this error. Is there a way to capture that discarded output for every allowed input at once?

## RrGeometry: How can we record every discarded output?

Why: The residual matrix collects the perpendicular output for every trial input.
Recall: R acts on trial coordinates; its columns come from the trial basis inputs.

How could we measure the error of the whole small model, rather than just one Ritz vector? For a general coordinate input y, the true output is A Q y and the model predicts Q B y. Their difference is linear in y, so a single matrix R equals A Q minus Q B describes it for every input. The green residual we just saw is one value of this map. What would its columns mean in the picture?

<!-- beat -->

What happens to the first basis input? Its discarded output is the upward green arrow, with ambient coordinates zero, zero, one. Those entries form the first column of R. One column is therefore a concrete output difference, not an arbitrary collection of error numbers.

<!-- beat -->

What changes for the second basis input? Its green arrow points the other way: zero, zero, minus one. That gives the second column. Since the map is linear, any combination of the two inputs produces the same combination of these discarded outputs. The columns let us predict the error of every candidate from two known cases.

<!-- beat -->

Could two individually escaping outputs cancel? Equal positive input coordinates make the two normal components cancel, and the green arrow disappears. The difference direction reinforces them instead. For a small eigenvector y, its eigenpair residual is R y. This suggests that one Ritz vector might be exact even though the entire trial plane is not invariant. Do the entries of our example confirm that prediction?

## RrExample: Can one Ritz vector be exact while another is not?

Why: A small eigenproblem combines candidate directions and reveals different residuals.
Recall: The trial space is the span of the first two coordinate directions.

Can a space that allows output to escape still contain an exact eigenvector? Here is the symmetric operator behind our pictures. The amber top-left block is the compression to the first two coordinate directions. The green entries couple that plane to its normal direction, producing the opposite residual columns. The question is how those two contributions combine for the eigenvectors of B.

<!-- beat -->

What happens in the sum direction, whose Ritz value is three? After lifting, its two normal contributions cancel. The cyan true output and amber retained output coincide in the plane, so r plus is zero. This particular Ritz vector is an exact eigenvector of A. Its exactness follows from the cancellation, even though neither basis input had zero discarded output.

<!-- beat -->

Does the difference direction have the same property? Its Ritz value is one, and subtracting the two input contributions reinforces the normal output. The residual is square root of two times e three. Thus one exact direction does not make the whole plane invariant. How can we express this distinction for larger trial spaces, where a drawing of two arrows is no longer enough?

## RrBlock: How do blocks describe where the output goes?

Why: Each output has a trial component and a perpendicular component.
Recall: Q spans the trial space; Q perpendicular completes an orthonormal basis.

How could a matrix remember the two destinations already visible in the picture? Each trial input has an output within the trial space and an output perpendicular to it. Q gives coordinates for the first destination. An orthonormal frame Q perpendicular could give coordinates for the second. This would describe the same output in two parts, rather than introduce a new assumption about A. What would the perpendicular coordinates be in our example?

<!-- beat -->

The two green arrows supply them: the upward coefficient is one and the downward coefficient is minus one. Together they form C, the row shown here. Lifting those normal coordinates gives R equals Q perpendicular C. The first block column now has a meaning: B records the retained output of trial inputs, and C records their escaping output. Completing the matrix adds D for the normal-to-normal action and, by symmetry, C transpose for the opposite coupling. The blocks organize output destinations we already know.

<!-- beat -->

What would make the entire trial space invariant? Every perpendicular output would have to vanish, which is exactly C equals zero. A cancellation for one input is insufficient. In our example C is nonzero even though the sum direction has zero residual. We can now recognize invariance from the blocks. Can we also verify directly, without introducing complementary coordinates, that every Ritz residual is perpendicular to the trial space?

## RrOrthogonality: Why is every Ritz residual perpendicular?

Why: The defining small model removes every residual component inside the trial space.
Recall: B equals Q transpose A Q, and Q transpose Q equals I.

Why should the green part always be perpendicular, rather than only in our drawing? Q transpose reads a vector’s trial coordinates. If every residual really lies outside the plane at a right angle, applying Q transpose to R should give zero. The definitions R equals A Q minus Q B and B equals Q transpose A Q let us test that prediction directly.

<!-- beat -->

What do the two terms become? Q transpose A Q is B by construction. Q transpose Q B is also B, because Q has orthonormal columns. Their difference is zero. This proves Q transpose R equals zero, usually called Galerkin orthogonality. The cancellation explains why the error has no component in any trial direction; it does not assume that the full error is small.

<!-- beat -->

What does this tell us about possible improvements? R equals I minus P, applied to A Q, so it is exactly the output that projection removes. For a small eigenvector y the full residual is R y. We have located the error, but perhaps a different small matrix could predict A’s action better. Could changing the model while keeping the same search space cancel any of this perpendicular error?

## RrModel: Could another small model reduce the error?

Why: Rayleigh–Ritz makes a particular model choice after the trial space is fixed.
Recall: M is any k by k proposed action on trial coordinates.

Could a different small matrix improve on B without adding any new search directions? Any replacement M still predicts an output in the range of Q. For one trial input, the cyan arrow represents the full discrepancy A Q minus Q M. Comparing this with the known compression may reveal where a different prediction can help. What if we add and subtract Q B?

<!-- beat -->

The difference splits into the green residual R and the amber term Q times B minus M. Green is perpendicular to the trial space, while amber lies inside it. The right-angle triangle answers the cancellation question: an in-plane correction cannot cancel an out-of-plane error. Changing M can remove its own internal discrepancy, but it cannot remove the part caused by the chosen space.

<!-- beat -->

Does that geometry give a precise best-model statement? Pythagoras, applied to each column and then summed, gives the displayed Frobenius identity. Q preserves lengths, so the extra squared error is exactly the squared Frobenius norm of B minus M. Its unique minimum occurs at M equals B. Compression is the best model for the space already chosen, in this sense. The error R can remain large. What can its size tell us about the original eigenproblem?

## RrQuality: What does a small residual certify?

Why: Accuracy of an eigenpair and identification of a wanted spectral target are different questions.
Recall: A is symmetric and the Ritz vector u has unit norm.

If a Ritz pair has a small residual, must its Ritz value be close to an exact eigenvalue? The white dots are the exact eigenvalues of our example; the amber marker is the Ritz value one. An exact orthonormal eigenbasis gives a way to reason about their distance. Writing the unit Ritz vector in that basis gives coefficients c j whose squared magnitudes add to one. This basis is for the argument; the approximation algorithm need not compute it.

<!-- beat -->

What does the residual look like in those coordinates? Applying A minus theta multiplies each coefficient by lambda j minus theta. Orthogonality gives the displayed sum for its squared norm. If every eigenvalue were farther from theta than the residual norm, every term would contribute too much to that weighted average. That is impossible.

<!-- beat -->

So what is certified? The green interval, of radius equal to the residual norm, contains at least one exact eigenvalue. Here the radius is square root of two. It does not identify which spectral target that eigenvalue belongs to; that needs separation information. Our Ritz value three is exact, yet would be the wrong answer if we wanted the smallest eigenvalue. If the chosen space gives an inadequate approximation, what does allowing more directions guarantee?

## RrMinmax: What improves when the search space grows?

Why: A larger search space improves extremal variational estimates.
Recall: The trial spaces are nested and nonzero; the symmetric matrix is fixed.

Would a larger trial space necessarily give a better extremal estimate? The smallest Ritz value is the minimum of the original Rayleigh quotient over the allowed unit vectors. A larger search space retains every old candidate and adds new ones. Its minimum therefore cannot increase. The nested picture compares a coordinate line, the trial plane, and the full space for the same operator.

<!-- beat -->

How does this play out in our example? The smallest Ritz value moves from two to one, then to three minus square root of six, the exact smallest eigenvalue. The number-line marker follows those values. The largest Ritz value moves in the opposite direction as the space grows. These are monotone extremal bounds, not a convergence rate for arbitrary spaces. We now have two distinct ways to discuss improvement: optimize a model within a fixed space, or improve the space itself. How does that distinction appear in the more general trial-residual framework?

## RrPaper: Where does Rayleigh–Ritz fit in the residual framework?

Why: The general residual framework includes Rayleigh–Ritz as a specific choice.
Recall: The operator under study is written A-hat in the residual theorem.

Does a trial residual always come from Rayleigh–Ritz compression? In the Davis–Kahan notation, the trial frame is E zero, the proposed small operator is A zero, and R equals A-hat E zero minus E zero A zero. The range of E zero is the trial subspace. Our Q and B are one particular choice of this pair: the Rayleigh–Ritz model sets A zero equal to E zero adjoint A-hat E zero.

<!-- beat -->

Why allow other models? In a perturbation problem, an old operator’s invariant subspace and its old small model can provide candidates for a new operator. That pair still has a meaningful residual, although it need not be perpendicular to the trial space. For unbounded operators, trial vectors must also lie in the operator’s domain, with the domain and bounded-residual assumptions required by the theorem. Our matrix geometry explains the special Ritz choice without removing those requirements. We can now ask both which space was chosen and which model was used. What answers did the whole construction give us?

## RrSummary: What did the smaller problem actually answer?

Why: The small problem answers some questions and leaves others open.
Recall: Trial space is a search choice; Ritz residual measures the discarded output.

How much did the small eigenproblem tell us about the large one? The trial space specified the candidates, Q supplied their coordinates, and the need to record A’s trial output led to compression. Its eigenproblem found directions that solve the projected equation. Lifting them and measuring the full residual revealed what that equation had left unchecked.

<!-- beat -->

Which guarantees did we earn? Compression preserves the restricted Rayleigh quotient and gives the best fixed-space model in the Frobenius sense. Its residual is perpendicular to the trial space. Neither a good choice of target nor a sufficiently accurate search space was automatic; those need further information. Three identities capture the construction, the location of its error, and the limit of changing the small model. How do those same facts appear in a formal proof?

## RrFacts: Which identities explain the construction?

Why: The definitions explain the error decomposition.
Recall: Q is isometric, B is the compression, and R equals A Q minus Q B.

Which formulas would let us reconstruct this reasoning in another proof? B equals Q adjoint A Q answers how the small model is built. Q adjoint R equals zero answers where its error lies. A Q minus Q M equals R plus Q times B minus M answers what a different model changes. Together they explain why an internal correction cannot cancel the perpendicular error. The next Lean cards express these same identities through accepted Tau Ceti APIs for bounded Hilbert-space operators.

## RrLean: Lean: how is the small operator defined?

Why: The abstract operator definition represents the same small model.
Recall: X in Lean is the isometric trial map Q on the slides.

How does Lean express the compression that our picture motivated? Its continuous linear maps act between a trial-coordinate space F and an ambient space E. X is our Q, and adjoint X is Q adjoint. A dot compression X is the small operator B. The displayed equality unfolds that definition into the same lift, act, and read composition. Defining it needs no self-adjointness assumption; symmetry matters when it becomes a Hermitian eigenproblem. Does the formal residual then satisfy the same orthogonality identity?

## RrLeanOrthogonal: Lean: why does the projected residual vanish?

Why: The isometry hypothesis makes the projected residual vanish.
Recall: A dot sylvester M X means A X minus X M.

What hypothesis makes the projected residual vanish in Lean? A dot sylvester M X denotes A X minus X M. Here the small model is the compression, so this is our R. Composing with adjoint X gives zero under the hypothesis h X that X is an isometry. That hypothesis supplies the identity Q adjoint Q equals I used in our cancellation. The accepted theorem thus says precisely that the error has no trial-coordinate component. What changes if another model M replaces the compression?

## RrLeanSplit: Lean: what can another model change?

Why: Changing the small model adds a component inside the trial space.
Recall: M is an arbitrary small bounded operator.

Can the same distinction between internal and escaping error be expressed without coordinates? The last card splits every model residual into the Ritz residual plus X composed with the difference between the compression and M. This algebraic identity needs no symmetry or isometry assumption. With X isometric, the two output pieces are orthogonal, giving the Pythagoras argument we used to compare models. That completes the mathematical explanation. The bonus asks how an implementation obtains the same objects before we turn to the study questions.

## RrComputation: How is the small problem built numerically?

Why: This bonus concerns implementation, after the exact mathematical construction.
Recall: The working basis must be orthonormal for the formulas used above.

What does an implementation need in order for this geometry to survive computation? The formulas used orthonormal trial coordinates, so a stable orthogonalization such as QR is a natural starting point. Applying A to those columns provides both the compression Q adjoint A Q and the full residual after the small eigenproblem is solved. A sparse matrix or operator interface can supply that action without storing a dense matrix. What if the working basis V is not orthonormal? Its Gram matrix V adjoint V records the missing coordinate geometry, giving V adjoint A V y equals theta V adjoint V y. Replacing the Gram matrix by the identity would change the problem. Numerical orthogonality checks and recomputed full residuals therefore test the assumptions behind the construction. Krylov and subspace iteration methods address the remaining question: how to build and improve the trial spaces. The study questions distinguish those choices from the guarantees of the small model.
