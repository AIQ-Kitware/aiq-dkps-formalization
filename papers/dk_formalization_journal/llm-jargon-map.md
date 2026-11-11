leakage - probably unconventional, contamination or cross-coupling?

* Defect spaces


Beyond "geometric leakage", this manuscript contains several terms that read informally, borrow colloquial metaphors, bleed Lean-specific programming types into mathematical prose, or collide with existing definitions in functional analysis:

---

### 1. Clashes with Established Mathematical Terminology

* **"Defect spaces" ($D_0, D_1$)**


* **Where it appears:** Section 2.3 (*"The right-angle defect spaces $D_0 = \operatorname{ran}(P) \cap \operatorname{ker}(Q)$..."*), Section 4.1, Table 4.


* **The issue:** In functional analysis and operator theory, **"defect spaces"** (and *deficiency indices*) refer almost universally to the von Neumann deficiency subspaces of an unbounded symmetric operator ($\mathcal{K}_\pm = \operatorname{ker}(T^* \mp iI)$). Using "defect spaces" for subspace intersections will cause an immediate double-take for operator theorists.
* **Standard alternative:** *"Right-angle intersection spaces"*, *"orthogonal defect components"*, or simply *"the intersection subspaces $\operatorname{ran}(P) \cap \operatorname{ker}(Q)$."*




* **"Equisingular"**


* **Where it appears:** Table 4 under DK-6.1-lem (*"if the two $K$ blocks are equisingular and the two $L$ blocks are equisingular"*).


* **The issue:** In mathematics, **"equisingular"** is a technical term in algebraic geometry and singularity theory (e.g., equisingularity of algebraic curves/varieties). Using it to mean "having the same singular values" is an ad-hoc neologism.
* **Standard alternative:** *"Co-singular"*, *"have identical singular values"*, or *"are unitarily equivalent."*



---

### 2. Colloquial or Stylistically Informal Terms

* **"Short-angle"**


* **Where it appears:** Corollary 3 (*"No positive short-angle threshold"*) and Section 5.4 (*"real short-angle restriction"*).


* **The issue:** Angles possess *magnitude*, not length. In perturbation theory and physics, standard usage is universally **"small-angle"** (as in "small-angle approximation"), never "short-angle."
* **Standard alternative:** *"Small-angle"* or *"acute-angle."*


* **"Quarter turn"**


* **Where it appears:** Section 4.1 (*"selecting the branch with angles below a quarter turn"*), Section 2.8(b) (*"use the quarter-turn $J_0$"*), and Appendix A.


* **The issue:** "Quarter turn" is informal and associated with introductory geometry or robotics. In research mathematics, the standard phrasing is an angle of $\pi/2$ (or a $90^\circ$ rotation).
* **Standard alternative:** *"Angles bounded by $\pi/4$ (or $\pi/2$)"*, and *"standard symplectic unit"*, *"canonical $90^\circ$ rotator"*, or simply *"the skew-symmetric matrix $J_0$"*.




* **"Headline theorems"**


* **Where it appears:** Section 1 (*"We formalized the four headline theorems..."*), Section 3, Table 3.


* **The issue:** "Headline" is journalistic. Academic math papers avoid journalistic descriptors for theorems.
* **Standard alternative:** *"Main theorems"*, *"primary results"*, or *"central theorems."*


* **"Transporter" and "Competitor"**


* **Where it appears:** Throughout Sections 1, 2.4, 2.7, 5, and 6.


* **The issue:** Calling an orthogonal/unitary map $W$ satisfying $W(U) = V$ a "transporter" sounds like differential geometry (parallel transport) or science fiction. Calling the alternative matrix $W_\theta$ "the competitor" reads more like sports writing or algorithm benchmarking than functional analysis.


* **Standard alternative:** *"Subspace map"*, *"transition isometry/unitary"*, or *"intertwining orthogonal transformation"*; and *"competing orthogonal map"* or *"counterexample map."*





---

### 3. Engineering / Applied Metaphors

* **"Unwanted block" / "Unwanted complementary spectral subspace"**


* **Where it appears:** Section 2.6 (*"isometric coordinates for the unwanted complementary spectral subspace..."*), Section 3.1.1, Figure 1 caption, Appendix A.


* **The issue:** "Unwanted" is subjective/applied phrasing. In pure/applied mathematics, subspaces are characterized by their algebraic and geometric properties, not user preference.
* **Standard alternative:** *"Complementary spectral subspace"*, *"orthogonal complement"*, or *"outer spectral block."*


* **"Leakage" (in Table 4)**


* **Where it appears:** Table 4 under DK-6.3-lem (*"leakage estimate"*, *"a nearly maximizing finite-rank compression has small leakage"*).


* **The issue:** As previously discussed for Section 2.6, using "leakage" inside a formal lemma summary in an operator-theory paper will draw red ink from referees expecting standard functional-analytic language.


* **Standard alternative:** *"Off-diagonal energy"*, *"projection onto the complement"*, or *"tail bound."*



---

### 4. Interactive Theorem Prover (ITP) / Lean 4 Leaks into Math Prose

* **"Linear partial maps"**


* **Where it appears:** Section 4.3 (*"We formalized these domain conditions using linear partial maps."*)


* **The issue:** In Lean 4 / Mathlib, unbounded operators are represented by the type `LinearPMap`. However, in functional analysis, these are almost universally referred to as **"densely defined (or unbounded) linear operators with non-trivial domains."** Referring to them as "partial maps" sounds like computer science jargon.


* **Standard alternative:** Frame this explicitly around the type: *"We formalized these operators as unbounded linear maps defined on dense submodules (using Mathlib's `LinearPMap`)."*


* **"Spectra ancestry"**


* **Where it appears:** Section 1 (*"The measure constructions retain their earlier Spectra ancestry."*) and Section 2.10.


* **The issue:** "Ancestry" is software version-control and git lineage terminology.
* **Standard alternative:** *"The measure constructions derive from the earlier Spectra formalization library."*
