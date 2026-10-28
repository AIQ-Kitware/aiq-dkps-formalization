# Real orthogonal transport: exact rank-one optimization and paired-angle saturation

**Research note — 23 October 2026.** Source checkout `2b6aa58dcd30af28a14fe7cea05d73f235d3c7bd` (the uploaded source archive). These are complete conventional mathematical arguments. **No new Lean theorem for the results of this note has been compiled in this investigation.** The existing, separately verified Lean theorems for the real four-dimensional counterexample and sharp all-norm approximation retain their established status. Publication priority for the two extensions below remains open; the proof ingredients are classical.

## 1. Exact solution for real lines and hyperplanes in every ambient dimension

For a real orthogonal transformation `W`, let `s(I-W)` denote its singular values in decreasing order. Let `N` be any unitarily invariant norm on real `n`-by-`n` matrices, equivalently a symmetric gauge of those singular values. Fix `n >= 2`, and two lines `U,V` in `R^n`, or two hyperplanes `U,V` (the cases `n=2` coincide). Let `theta in [0,pi/2]` denote the angle between the lines, or between unit normals to the hyperplanes. For hyperplanes, this is the only potentially nonzero principal angle. Write

```
   a(theta) = 2 sin(theta/2),
   D_theta  = diag(a(theta), a(theta), 0, ..., 0),
   H        = diag(2, 0, ..., 0).
```

**Theorem 1 (exact real rank-one/codimension-one transport problem).** With the above hypotheses,

\[
\boxed{\min_{W\in O(n):\,WU=V}N(I-W)
 =\min\{N(D_\theta),\,N(H)\}.}
\]

In the component `SO(n)`, the minimum equals `N(D_theta)` and is attained by the usual two-plane rotation `R_theta`, acting as the identity outside the two-dimensional span of representative unit vectors (or normals). In the `det W=-1` component, the minimum equals `N(H)` and is attained by a single Householder reflection mapping the source line or source normal line to the target. Thus both values are achieved, even for a norm whose singular-value gauge is not strictly convex.

**Proof.** Choose unit vectors `x,y` representing the two lines or their unit normals, with `x·y=cos(theta)>=0`. Every admissible orthogonal map sends `x` to `y` or to `-y` (the line and its sign are preserved), so for every admissible `W`,

\[
\lVert (I-W)x\rVert_2
 \ge \min\{\lVert x-y\rVert_2,\lVert x+y\rVert_2\}
 =2\sin(\theta/2)=a(\theta).
\]

It follows that `s_1(I-W)=||I-W||_op>=a(theta)`.

Suppose first that `det W=+1`. By the real orthogonal spectral decomposition, every nonreal eigenvalue of `W` occurs in a conjugate pair. The multiplicity of eigenvalue `-1` is even: nonreal pairs have determinant one, all `+1` eigenvalues have determinant one, and `det W=+1`. Each complex-conjugate pair `e^{i phi},e^{-i phi}` contributes **two equal singular values** `2|sin(phi/2)|` to `I-W`, while each `-1` contributes singular value 2. Consequently the two largest singular values of `I-W` are equal (or are both zero when `W=I`). Combining this fact with the preceding operator-norm bound gives

\[
 s_1(I-W)=s_2(I-W)\ge a(\theta).
\]

All remaining singular values are nonnegative. Therefore the singular-value vector of `D_theta` is entrywise bounded by that of `I-W`. Symmetric-gauge monotonicity, or Fan dominance, yields `N(D_theta)<=N(I-W)`. The canonical rotation on `span{x,y}` (identity on its orthogonal complement) maps the given subspace onto the target, has determinant `+1`, and has precisely the displacement singular values of `D_theta`. The minimum in the positive-determinant component follows.

If `det W=-1`, then `-1` is an eigenvalue of odd multiplicity, in particular of multiplicity at least one. Thus `s_1(I-W)=2`, so `s(H)` is entrywise at most `s(I-W)` and `N(H)<=N(I-W)`. If `x!=y`, the Householder reflection

\[
 S=I-2\frac{(x-y)(x-y)^T}{\lVert x-y\rVert_2^2}
\]

sends `x` to `y`; by orthogonality, it maps the entire source line (respectively the orthogonal hyperplane) onto its target. It has determinant `-1` and singular-value list `(2,0,...,0)`. For `x=y`, choose any Householder reflection fixing `x` (possible for `n>=2`); it also maps `U` onto `V`. This proves the negative-component minimum and the theorem. `□`

**Consequences for concrete norms.** For the trace norm,

\[
\min\lVert I-W\rVert_1
 =\min\{4\sin(\theta/2),\,2\}.
\]

The direct rotation is trace minimizing if and only if `theta<=pi/3`, with a tie at the threshold. For every unitarily invariant norm simultaneously, `D_theta` is no greater than `H` exactly when `a(theta)<=1`: the corresponding vectors satisfy `(a,a,0,...) \prec_w (2,0,...)` if `2a<=2`, and if `a>1` the trace norm violates the comparison. The direct rotation is therefore a common minimizer for *all* such norms when `theta<=pi/3`. It remains operator-norm minimizing for all `theta<=pi/2`, while the reflection beats it in trace norm when `theta>pi/3`. For Frobenius norm, the direct rotation wins through `pi/2`, tying the reflection at the endpoint.

**Dimension consequence.** Every pair of proper nonzero equal-dimensional subspaces in real ambient dimension `n<=3` consists of lines or hyperplanes. Thus the real `pi/3` minimality assertion holds in dimensions 2 and 3 **for every unitarily invariant norm**. The project's Lean-verified `R^4` family violates it for each `theta>0`, even among determinant-`+1` competitors. Consequently the *least real ambient dimension admitting the false short-angle conclusion* is exactly **four**. This is a rigorous conventional proof; it is not a claim that the dimension-minimality theorem has been Lean-formalized or is historically unpublished.

**Scope controls.** The proof relies on the real orthogonal spectrum and a **one-dimensional** source, or one-dimensional orthogonal complement. The pairing of largest displacement singular values fails for general complex unitaries: an isolated complex eigenphase need not have a conjugate partner. It also fails for real orthogonal transformations of negative determinant, whose `-1` eigenvalue can be unpaired. Neither conclusion licenses a general all-dimensional or all-rank version of Proposition 4.4.

## 2. Exact real trace-norm attainment when positive principal-angle multiplicities are even

**Theorem 2 (paired-angle sufficient condition).** Let `U,V` be equal-dimensional subspaces of a finite-dimensional *real* Euclidean space, with principal angles in `[0,pi/2]`. Assume **each positive value** of the principal-angle multiset occurs with **even multiplicity** (zero angles may have any multiplicity). Then there is an orthogonal `W` mapping `U` onto `V` such that

\[
\boxed{\lVert I-W\rVert_1=\lVert P_U-P_V\rVert_1
 =2\sum_j\sin\theta_j.}
\]

The minimum over all real orthogonal transporters is therefore exactly the same displayed value. This includes positive right angles; the statement does not require the acute-pair direct rotation to be uniquely defined.

**Proof.** Apply the real cosine-sine decomposition to the two subspaces. For each positive principal angle `theta_j`, choose mutually orthogonal real principal planes `E_j=span{u_j,z_j}`, where `u_j∈U`, `z_j∈U^perp`, and the target line inside `E_j` is spanned by `v_j=cos(theta_j)u_j+sin(theta_j)z_j`. The remaining orthogonal summand is a direct sum of a common subspace (from zero angles) and a subspace outside both, on which the identity transports `U` to `V`.

Pair planes with identical *positive* angles `theta`. A pair of such real principal planes forms a real 4-space `E_j⊕E_k`; group `(u_j,u_k)` as one copy of `C` and `(z_j,z_k)` as another, where multiplication by `i` is the real orthogonal quarter-turn. The real canonical rotation on the pair is the realification of the complex matrix

\[
 R^{\mathbb C}_\theta=\begin{pmatrix}\cos\theta&-\sin\theta\\
                                      \sin\theta&\cos\theta\end{pmatrix}.
\]

Multiplication by the **same complex scalar phase** `e^{i theta}` yields the complex unitary `W_theta=e^{i theta}R^{C}_theta`, which still takes the complex source line onto the complex target line, hence its realification maps the source real *two-plane* onto the target real *two-plane*. The two complex eigenvalues of `W_theta` are `1,e^{2i theta}`. Its complex displacement singular values are `(0,2sin(theta))`; after realification each is repeated twice, giving real singular values `(2sin(theta),2sin(theta),0,0)` and trace norm `4sin(theta)`.

On these same four real coordinates, `P_U-P_V` has four singular values each `sin(theta)`, so its trace norm is also `4sin(theta)`. Take the orthogonal direct sum of these pairwise phase-corrected operators and the identity on every zero-angle or exterior summand. Because the trace norm is additive on orthogonal direct sums, the resulting admissible `W` has

\[
 \lVert I-W\rVert_1
 =\sum_{\text{paired }j,k}4\sin\theta_j
 =2\sum_{\text{all }j}\sin\theta_j
 =\lVert P_U-P_V\rVert_1.
\]

The universal projector lower bound `||P_U-P_V||_1 <= ||I-T||_1` for every admissible `T` proves global optimality. `□`

**Nonconverse.** The even-multiplicity condition is sufficient only. At a right angle in a *single* real two-plane, a reflection has trace displacement 2 and equals the projection-distance trace, despite multiplicity one. The odd-multiplicity *acute* case, arbitrary angle patterns, and the classification of all minimizers require separate analysis. This note makes no general real trace-norm closed-form claim.

## 3. Literature and formalization classification

* **Established mathematics:** real orthogonal spectral decomposition, Householder reflections, CS/principal-angle decomposition, Fan dominance, complex scalar phase adjustment (Davis–Kahan 1970, Example 4.2), and universal projection lower bound by reflection-commutator proof. Fan dominance appears explicitly in Bhatia, *Matrix Analysis*, Theorem IV.2.2, printed p.93; see [Bhatia publisher DOI](https://doi.org/10.1007/978-1-4612-0653-8). Bolotnikov–Li–Rodman, *Electronic Journal of Linear Algebra* **8** (2001), [DOI 10.13001/1081-3810.1058](https://doi.org/10.13001/1081-3810.1058), **Problem 1.1 p.26** already poses the same ambient constrained norm-minimization problem, and **Theorem 4.2 pp.39–40** solves its Frobenius specialization. The general objective itself must not be called new.
* **Present deductions:** Theorem 1 gives a closed-form solution for *every* real unitarily invariant norm on pairs of lines/hyperplanes, hence real dimension minimality of the small-angle counterexample. Theorem 2 gives a transparent even-multiplicity *sufficient* condition for attaining the trace projection lower bound. Neither appears verbatim in the source passages inspected for this audit; that absence does not establish priority.
* **Existing Lean results in this source snapshot:** `ProjectionDisplacement.lean` establishes the all-seminorm lower bound. `SharpDisplacement.lean` establishes the secant-factor comparison and uniform sharpness, `TraceOptimality.lean` establishes real four-dimensional optimality, and the newer `ComplexPhaseTrace.lean`/`ComplexTracePrincipalAngles.lean` establish unconditional finite-dimensional complex trace optimality and its exact principal-angle formula; `TraceSine.lean` proves the general real/complex two-projection trace identity. This note neither rewrites those theorems nor changes the audited source count of 29 (28 proved and printed Proposition 4.4 refuted). Its two new **real** generalizations are **conventional proofs pending formalization**.

## 4. Follow-up mathematics and independent review requirements

1. Determine whether an earlier *real* orthogonal completion/minimal-distortion paper has stated Theorem 1 with arbitrary symmetric gauges. Search BLR citations, the guidance-control paper cited at BLR 2001 p.27 [3], and rank-one unitary/orthogonal completion theory. This would settle historical priority, independently of the proof above.
2. Test whether even multiplicity is necessary for *strictly acute*, all-nonzero real angles; it is **not** necessary with right angles. Avoid assuming optimal transport respects each original principal plane, since the `R^4` witness couples planes.
3. Determine whether the odd-angle real trace minimum has a closed formula and, if so, identify the block-coupling patterns of its minimizers. Numerical experiments alone cannot certify the global minimum.
4. If pursuing Lean, first identify accepted real orthogonal determinant/eigenpair and symmetric-gauge comparison APIs in the pinned libraries. Build the rank-one theorem or even-multiplicity theorem as an independent mathematical extension, then add any manuscript theorem claim; **do not** modify the existing 29-source inventory.

**Source constraints:** Theorems 1–2 were proved here by standard, explicit constructions and eigenvalue arguments. Their novel *formulations* have not passed an exhaustive priority search. A referee should review the spectrum argument and the CS assembly before they are promoted to a submitted mathematics result.
