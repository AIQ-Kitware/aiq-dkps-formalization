# How eigenvector stability became a subject

Standalone overview: people, publications, and the mathematical questions connecting them.
Authored by GPT-6.1-Sol. Publication records and claim anchors are in `sources.md`;
remaining historical triage is in `review-notes.md`. These notes are not spoken.

## HiTitle: How eigenvector stability became a subject

Why: Meet the people behind the mathematics.
Recall: No formulas are needed on the cover.

How eigenvector stability became a subject.

## HiQuestion: One question, several mathematical traditions

Why: When a matrix changes, what can we still trust?
Recall: An eigenvector is a direction that a matrix only stretches.

An eigenvector is a direction that a matrix stretches without turning away from its line. Its eigenvalue tells us the stretching factor. If we change the matrix a little, how much can this special direction turn? That sounds like one question, but answering it brings together several mathematical traditions. Geometry tells us how to compare directions. Analysis tells us how to control errors. Numerical analysis asks what a computation can certify. Statistics asks what survives the randomness of data.

<!-- beat -->

The picture will keep returning to a blue reference direction and an amber changed direction. Later, each direction becomes a whole subspace: a collection of directions closed under addition and scaling. We will follow people and publications rather than prove their theorems. The timeline records publication landmarks. Its spacing is schematic, and nearby dates do not by themselves mean that one author influenced another. The question to keep asking is: what new way of understanding the problem did this work provide?

## HiJordan: Camille Jordan: angles between spaces

Why: Geometry supplies the objects we want to compare.
Recall: A line needs one angle; larger subspaces can need several.

Our first landmark is Camille Jordan. In 1875, his Essay on Geometry in n Dimensions appeared in the Bulletin of the French Mathematical Society. We are used to comparing two lines by one angle. Jordan belongs to the early history of the higher-dimensional version: the geometry that we now describe through principal angles. Instead of assigning just one number to two subspaces, we find a list of angles that describes how corresponding directions fit together.

<!-- beat -->

The two panels illustrate two different direction pairs. These are schematic views of two principal planes, not two drawings that must occupy the same two-dimensional space. One pair can be close while another is far apart. That is the important geometric lesson. A subspace can change unevenly in different directions. Much later, when an angle theorem controls a whole subspace, it is using this kind of geometry, even if its statement compresses the angle information into a single norm.

## HiRayleighRitz: Rayleigh and Ritz: useful approximations

Why: An approximation becomes more valuable when its error can be assessed.
Recall: A trial vector need not be an exact eigenvector.

John William Strutt, Lord Rayleigh, published the first volume of The Theory of Sound in 1877. Vibration problems provide a natural reason to seek eigenvalues and shapes of oscillation. Walter Ritz published his variational approximation method in 1909 in the Journal for Pure and Applied Mathematics. These are landmarks in the development of approximating a difficult problem within a simpler family of trial functions. The familiar name Rayleigh–Ritz brings these ideas together; it should not erase the distinct publications or contributions.

<!-- beat -->

Here is the connection to our question. Choose a trial vector, apply the operator, and compare the result with a scalar multiple of the vector. Any difference is a residual. The green arrow is that remaining error. A small residual is information we can compute, but we still need a reason that it certifies proximity to the particular eigenspace we want. That is where spectral separation will enter. Approximation creates the question that perturbation bounds help answer.

## HiWeyl: Hermann Weyl: values versus directions

Why: Stable eigenvalues and stable eigenvectors are different conclusions.
Recall: An eigenvalue is a number; an eigenspace is a geometric object.

Hermann Weyl’s 1912 paper in Mathematische Annalen is a publication landmark for eigenvalue theory and inequalities. The variational tradition also includes Richard Courant and Ernst Fischer, whose names appear in the min–max principle. These tools let us reason about eigenvalues using how a self-adjoint operator acts on vectors and subspaces. For this overview, the important distinction is between locating the eigenvalues and controlling the directions associated with them.

<!-- beat -->

Watch two eigenvalue markers approach each other. Their locations can change very little, while the choice of an individual eigenvector becomes sensitive. At a repeated eigenvalue, there is no uniquely distinguished orthonormal basis inside its eigenspace. A whole cluster of eigenvalues can nevertheless define a meaningful subspace when it is separated from the rest of the spectrum. This shifts our question from following a named eigenvector to following the space of all directions associated with the selected cluster.

## HiHotelling: Harold Hotelling: geometry enters statistics

Why: Different applications can lead to the same subspace geometry.
Recall: Correlation measures association between quantities.

Harold Hotelling published Relations Between Two Sets of Variates in Biometrika in 1936. His canonical correlation framework asks how to choose combinations from two collections of variables so that their association is strongest. With the appropriate inner products and normalization, this has a geometric relationship to comparing subspaces. The same idea of searching for best-aligned directions appears in a statistical language.

<!-- beat -->

The point is not that all the later authors followed one straight chain from this paper. It is that geometry and statistics were already asking related questions. A direction in one space is compared with a direction in another; after finding the best pair, further pairs describe what remains. Keep Hotelling in mind when we reach modern statistical perturbation results. Subspace geometry is useful both for understanding mathematical structure and for comparing structures estimated from observations.

## HiProjectionPeople: Sz.-Nagy and Davis: comparing whole spaces

Why: A projection describes a subspace without selecting its basis.
Recall: Projection keeps the component lying in a chosen subspace.

Béla Sz.-Nagy’s 1947 work on perturbations of self-adjoint transformations developed a construction for comparing nearby projections. Chandler Davis’s Separation of Two Linear Subspaces appeared in 1958 in Acta Scientiarum Mathematicarum in Szeged. These works help place our finite-dimensional angle pictures in a broader operator-theoretic setting. A projection records a subspace by mapping each vector to its component in that space. It does not require us to choose and track individual basis vectors.

<!-- beat -->

For nearby subspaces, we would like a length-preserving transformation that carries the first space onto the second. Think of moving the whole blue line onto the amber line without stretching it. In higher dimension the transformation must respect all the relevant directions together. Nearby-projection constructions give a systematic way to do this. They are part of the background to direct rotation, which will become important again when we ask how much an entire transporting transformation moves the ambient space.

## HiKatoHalmos: Kato and Halmos: the operator viewpoint

Why: Finite pictures point toward a theory on Hilbert space.
Recall: A Hilbert space has an inner product and may have infinitely many dimensions.

Tosio Kato’s Perturbation Theory for Linear Operators appeared in its first edition in 1966. Kato made spectral projections central to the study of changing operators and gave a streamlined nearby-projection construction, building on earlier work. Paul Halmos’s Two Subspaces appeared in the Transactions of the American Mathematical Society in 1969. It provides a powerful structural account of a pair of subspaces through their orthogonal projections. These are complementary ways to organize the geometry.

<!-- beat -->

The schematic blocks show why this organization helps: separate shared directions from the part where the two projections interact. In finite dimensions, principal planes turn the interacting part into familiar two-dimensional geometry. In an infinite-dimensional Hilbert space, the operator formulation carries information that a finite angle list cannot capture. Some operators are unbounded and are only defined on a domain. The full Davis–Kahan story therefore extends beyond matrices; a finite drawing is a guide to that theory, not its complete statement.

## HiRosenblum: Marvin Rosenblum: an equation for separation

Why: An operator equation turns geometry into an estimate.
Recall: A spectral gap measures separation between selected spectral sets.

Marvin Rosenblum’s On the Operator Equation B X minus X A equals Q appeared in the Duke Mathematical Journal in 1956. He also studied the self-adjoint case in a 1969 paper. The matrix equation belongs to a tradition associated with James Joseph Sylvester’s 1884 work. In modern perturbation arguments, this equation is a bridge: an unknown geometric error becomes X, while the right-hand side becomes an error we can measure.

<!-- beat -->

The scalar version explains the basic intuition. If b minus a times x equals y, and the absolute difference between b and a is at least delta, then the size of x is at most the size of y divided by delta. The operator version needs carefully stated spectral configurations and norm assumptions. We are not proving that extension here. We are identifying why operator equations and spectral separation belong in the cast: they turn the geometry of unwanted components into quantitative control.

## HiDavisKahan: Chandler Davis and William Kahan

Why: The earlier threads meet in quantitative subspace rotation.
Recall: The target is a subspace, and the error is measured by angles.

Chandler Davis published The Rotation of Eigenvectors by a Perturbation in 1963 and its second part in 1965, both in the Journal of Mathematical Analysis and Applications. Davis and William Kahan then published an announcement of new subspace perturbation bounds in 1969. Their extended treatment, Part Three, appeared in the SIAM Journal on Numerical Analysis in 1970. This is the paper at the center of our lecture series. The sequence matters: the familiar joint name sits within an existing program of research.

<!-- beat -->

The paper studies how spectral subspaces rotate and how residual information controls that rotation. It contains several angle theorem families, including sine and tangent bounds and double-angle bounds. They are related, but they do not all have interchangeable hypotheses. The operator setting allows infinite dimension and unbounded self-adjoint operators with the appropriate domain conditions. Our next picture compresses one central mechanism, while the technical lectures explain exactly which separation and domain assumptions make each statement true.

## HiBound: The idea to remember: error over separation

Why: A bound explains why the gap matters.
Recall: Residual means failure of the chosen eigen-equation; separation identifies the target.

Imagine a computed trial direction and the exact subspace we want. Project the trial direction onto the part outside that subspace. That unwanted component measures the geometric error. The residual tells us how well the trial data satisfy the operator equation. Under an appropriate separation hypothesis, the angle estimate bounds the error by the residual divided by the separation. In a one-dimensional picture the sine of the angle is the length of the unwanted component of a unit vector.

<!-- beat -->

The green residual and the violet separation do different jobs. A small residual says the equation is nearly satisfied. Separation prevents that fact from hiding an unwanted component among nearby spectral values. When the certified separation becomes small, the bound becomes weaker. This gives us the recurring idea behind the history: a geometric question can be answered by a measurable error together with information about the spectrum. It also explains why choosing the right definition of separation matters in later applications.

## HiWedinGolub: Wedin, Björck, and Golub: later developments

Why: A theorem about stability and an algorithm for angles serve different needs.
Recall: Singular vectors extend useful geometric ideas to rectangular matrices.

Per-Åke Wedin published Perturbation Bounds in Connection with Singular Value Decomposition in BIT in 1972. Singular vectors and singular values let us study rectangular matrices, where the familiar symmetric eigenproblem is no longer the right form. Wedin’s paper is an important landmark for singular-subspace perturbation. This is one way the surrounding theory grew beyond the symmetric eigenvector setting.

<!-- beat -->

Åke Björck and Gene Golub published Numerical Methods for Computing Angles Between Linear Subspaces in Mathematics of Computation in 1973. Notice the different question. A perturbation theorem tells us how a geometric quantity can change under assumptions. A numerical method tells us how to obtain that quantity from the data describing our spaces. Both matter, but proving a bound and designing a reliable computation are distinct accomplishments. The paired publication cards keep those contributions separate.

## HiYws: Yu, Wang, and Samworth: a statistical gap

Why: The useful hypothesis depends on what can be known or controlled.
Recall: Population means the underlying model; sample means an estimate from data.

Now move to statistics. There is an underlying population matrix, such as a covariance matrix, and a sample matrix estimated from observations. We want to compare their eigenspaces. Yi Yu, Tengyao Wang, and Richard Samworth posted their paper in 2014, and A Useful Variant of the Davis–Kahan Theorem for Statisticians appeared in Biometrika in 2015. Its central change is a bound whose separation condition uses only population eigenvalues. That makes it especially convenient when the estimated matrix is random.

<!-- beat -->

The two sides of the picture distinguish the fixed population quantities from their estimated versions. In common statistical formulations of Davis–Kahan, a separation condition can mix population and sample eigenvalues. The YWS variant moves the needed gap information to the population side, while the perturbation still measures the difference between the matrices. The paper also controls bases after a suitable change of orthonormal coordinates, and extends to singular subspaces of asymmetric or rectangular matrices. This is a refinement of how a perturbation theorem is made useful in a particular setting, not the invention of subspace perturbation itself.

## HiQuench: One application: comparing models with fewer queries

Why: Stable geometry can support a downstream statistical task.
Recall: A spectral embedding turns a matrix into coordinates.

For one brief application, consider Quench. Hayden Helm, Ben Johnson, and Carey Priebe published Query-Efficient Model Evaluation Using Cached Responses at ICML in 2026. Previously cached responses help describe relationships between models in a data kernel perspective space. That geometry can then help predict a new model’s benchmark performance while using fewer queries under the stated conditions. The intermediate ideas include constructing an embedding, controlling its error, and using nearby reference models. Subspace perturbation is part of that broader mathematical toolkit; it is not, by itself, a query-efficiency theorem.

## HiNormPeople: Von Neumann, Schatten, and Ky Fan: what is movement?

Why: Different norms can rank the same two motions differently.
Recall: A norm is a rule for measuring the size of an operator.

To return from statistical use to the geometry of moving spaces, we need another historical strand. John von Neumann’s matrix-inequality work appeared in 1937. Robert Schatten’s A Theory of Cross-Spaces appeared in 1950. Ky Fan’s Maximum Properties and Inequalities for the Eigenvalues of Completely Continuous Operators appeared in the Proceedings of the National Academy of Sciences in 1951. These are landmarks behind the norm and eigenvalue-sum language used throughout operator theory. A stretching factor is a singular value. The Schatten p norm raises each singular value to the power p, adds the results, and takes the p-th root. The trace norm is the case p equals one.

<!-- beat -->

The visual compares two lists of stretching factors. One norm measures the largest factor; another adds the factors. Those rules can favor different lists. For a transporting map W, the displacement is I minus W, which measures how much each input vector changes. Asking whether a particular rotation moves space least is incomplete until we say which norm measures that displacement. This is the point at which norm theory becomes essential to reading the optimality discussion in Section Four of Davis and Kahan.

## HiCorrection: A printed optimality claim needs a norm boundary

Why: The formalization separates a false printed statement from a supported repair.
Recall: A transporter must carry the source subspace onto the target.

The 1970 paper discusses direct rotation: a canonical way of carrying one nearby subspace onto another. Its printed Proposition Four Point Four makes a full-displacement optimality claim that is too broad in the real case. This repository records a machine-checked counterexample in four real dimensions and separately proves a repair for a class called Q-norms. This class includes the operator norm and Frobenius norm, but not the trace norm. The repaired claim therefore has a meaningful boundary: it applies to some familiar costs while excluding the cost that defeats the printed assertion. The correction concerns which norm classes support the comparison, not a failure of all the paper’s angle bounds. The original paper already contains a related complex phase mechanism, so that mechanism should not be presented as a new discovery here.

<!-- beat -->

The schematic comparison has two maps that both reach the target. A map can be better in trace norm even though the direct rotation is better in another norm. This illustrates why a precise feasible set and a precise cost matter. Formal checking establishes the encoded counterexample and repaired statement. Comparing those statements with the printed text is a separate source-interpretation step. Both are necessary if we want to say honestly what was corrected.

## HiMatching: From a correction to a transport question

Why: The new question is the minimum over every admissible motion.
Recall: Matching chooses disjoint pairs and leaves other vertices unpaired.

Once direct rotation is not always optimal for the chosen cost, a natural question remains: which transporter is optimal? For equal-dimensional real subspaces in finite dimension, the transport development here proves an unrestricted reduction to a weighted matching problem for Schatten powers from one up to, but excluding, two. At the trace-norm endpoint, each positive principal angle is a labelled vertex. Leaving an angle unpaired has a cost, and pairing two angles has a cost. The theorem identifies the global minimum with the cheapest such pairing pattern and supplies an attaining transporter.

<!-- beat -->

The highlighted edge illustrates a pairing choice, not a restriction imposed at the beginning of the optimization. The difficult direction is showing that no arbitrary ambient orthogonal transporter can do better than the best matching. Real and complex cases have different possibilities, so the field is part of the statement. This work grew out of the Davis–Kahan formalization and its reusable foundations. That is a documented research path, not a claim that the sine-theta theorem logically implies matching, or that matching improves the YWS or Quench bounds. Questions of historical priority for the exact extension remain subject to literature comparison.

## HiEvidence: What formal proofs add to the historical story

Why: Mathematical dependence, historical influence, and teaching order differ.
Recall: A checked Lean theorem proves its precise formal proposition.

Our final distinction is about evidence. A Lean proof can verify a precise mathematical statement with explicit hypotheses. It does not establish who discovered the result first, and it does not guarantee that a viewer understands the explanation. This project uses the Lean mathematics libraries Mathlib and Tau Ceti, together with remaining local developments. Some upstream foundations were developed through this effort, some were independently developed, and some have earlier ancestry. Those relationships should be reported from the provenance records rather than inferred from a namespace.

<!-- beat -->

The three rows describe different maps. A teaching prerequisite says which explanation helps you learn another. A proof dependency says which formal declaration a proof uses. A historical connection says what the publication evidence supports. They need not be identical. The long-term goal of this lecture series is to make the whole Davis–Kahan paper, its prerequisites, and the extensions here understandable, while progressively checking the technical learning map against Lean. Historical orientation gives us a reason to care about that map and introduces the people whose mathematics it contains.

## HiSummary: The people, the questions, and the next lectures

Why: Remember contributions by the questions they made answerable.
Recall: Geometry, perturbation, statistics, and transport share tools but ask different questions.

Here is the route we have followed. Jordan helps introduce the geometry of several angles. Rayleigh and Ritz represent the search for useful approximations, while eigenvalue theory reminds us that values and directions are different objects. Sz.-Nagy, Davis, Kato, Halmos, and Rosenblum give ways to compare spaces and analyze operators. Davis and Kahan bring the error-and-separation mechanism into quantitative subspace rotation bounds. Wedin, Björck, and Golub illustrate the distinct growth of perturbation theory and computation.

<!-- beat -->

Hotelling provides an early statistical connection, and Yu, Wang, and Samworth adapt the gap condition to population and sample comparisons. Quench briefly illustrates how stable geometry participates in a larger application. Von Neumann, Schatten, and Ky Fan help explain why measuring motion is itself a mathematical choice. The formalization and transport work continue that inquiry. To study the technical details, start with projections and principal angles, then residuals and spectral separation. The matching lectures take the separate route through norms and feasible variations. Two short questions will help check the relationships before you move on.
