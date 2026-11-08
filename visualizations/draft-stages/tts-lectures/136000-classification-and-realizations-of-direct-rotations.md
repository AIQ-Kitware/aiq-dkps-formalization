# 136000 — Classification and realizations of direct rotations

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `045000–051000`, `049000–050000`, `130000–135000`. **Next:** `137000`.

<!-- BEGIN SPOKEN LECTURE -->

# Classification and realizations of direct rotations

Our last lectures compared ways of transporting one subspace onto another. We now return to a more basic question: what data determine a pair of subspaces up to a rigid change of coordinates? Answering that question also tells us exactly what is available when we try to construct a direct rotation.

We will distinguish three problems. Can two pairs of subspaces be identified by a unitary map? Can a particular pair be carried into itself by a direct rotation that sends its first subspace onto its second? And can we prescribe the angles and then build a pair that has them? These problems have related, but different, answers.

## Four elementary pieces

Take two closed subspaces, U and V, of a Hilbert space. Split the ambient space according to their intersections. The common part belongs to both. The source defect belongs to U and is perpendicular to V. The target defect belongs to V and is perpendicular to U. The exterior part is perpendicular to both.

Every vector in one of these pieces has an immediately understood relationship to the two subspaces. Common vectors need no movement. Source-defect vectors sit at a right angle to every vector of V. Target-defect vectors are the corresponding right-angle directions from the other side. Exterior vectors should remain outside both.

Remove those four closed pieces and look at their orthogonal complement. This is the generic part. There, neither a zero principal angle nor an exact right angle contributes an eigenvector of the elementary kinds just listed.

The distinction between the dimensions of the source and target defects is already decisive. For a direct rotation through right angles, every source-defect direction needs a target-defect partner. A quarter-turn sends the first to the second and the second to the negative of the first. That is an orthogonal, orientation-compatible action on their direct sum. If one defect space has greater Hilbert dimension than the other, no such matching can cover both.

For example, in real three-space let U be the first coordinate axis and let V be the plane spanned by the second and third axes. The source defect has dimension one, and the target defect has dimension two. This is a legitimate pair of subspaces, but the crossed defects cannot be paired. No direct rotation of the prescribed kind transports U onto V.

Contrast that with two perpendicular lines in the plane. The two crossed defects both have dimension one. The quarter-turn exists, even though the pair is not acute. Thus an exact right angle is not by itself an obstruction: unmatched right-angle multiplicity is the obstruction.

## The generic cosine operator

On the generic part, write the pair using Halmos's two-projection construction. In suitable coordinates, the first projection picks out the first factor. The second has a block whose upper-left entry is cosine squared, whose off-diagonal entries are cosine times sine, and whose lower-right entry is sine squared.

These are positive commuting operators, and their squares add to the identity. Think of them as many simultaneous principal planes, but without assuming that a basis of individual planes exists.

The cosine operator contains the relative position data. If it is diagonalizable, its eigenvalues are cosines of principal angles. In general there may be continuous spectrum, so an enumerable list of angles is insufficient. The correct invariant is the operator itself up to unitary equivalence, together with the four elementary dimensions.

To see why an operator is needed, consider multiplication by a varying function on an L two space. It may have no eigenvectors, yet it has a perfectly definite spectrum and changes the geometry of the associated pair. Any classification that merely counts principal-angle eigenvectors would miss that example.

Thus, for arbitrary Hilbert-space pairs, the Halmos decomposition has two kinds of data: the four elementary multiplicities, and the unitary-equivalence class of the generic cosine-square operator. A global unitary identifying two pairs must preserve each kind of data. Conversely, matching these data lets us assemble a unitary from the individual elementary identifications and a compatible unitary on the generic model.

## Why compactness simplifies the answer

Now suppose the relevant generic cosine operator is compact. The spectral theorem for compact positive operators says its positive spectral data consist of eigenvalues of finite multiplicity, with only zero available as an accumulation point.

We can record the positive eigenvalues as a decreasing sequence, repeated according to multiplicity, or equivalently record the dimension of the eigenspace for each positive eigenvalue. Both describe the same compact operator up to unitary equivalence, provided the kernel information is handled too.

For this application, remember that elementary zero-angle and right-angle multiplicities live in separate summands. We should not try to smuggle them into a generic eigenvalue sequence. A zero of the generic cosine may be excluded by generic-position hypotheses even when zero remains in its continuous spectrum.

Compactness makes the classification numerical; it does not abolish the four elementary dimensions.

## Building a prescribed angle sequence

We can run the process backward. Suppose we choose angles theta one, theta two, and so on between zero and ninety degrees. For simplicity first assume each lies strictly between those endpoints.

Take an orthogonal sum of two-dimensional coordinate planes. In each plane, let U use the horizontal axis, and let V use the unit line with horizontal component cosine theta and vertical component sine theta.

The projection onto U has matrix with entries one, zero, zero, zero. The projection onto V has entries cosine squared, cosine sine, cosine sine, sine squared. Assembled as a direct sum, these give the prescribed principal-angle blocks.

If we want infinitely many angles, use the Hilbert direct sum of those planes. Boundedness is automatic for the projection blocks because cosine and sine have magnitude at most one. If the angles tend to zero, the squared-sine defect operator is compact, as its diagonal entries tend to zero. That compactness statement concerns the sine defect; it is different from compactness of the cosine itself.

We can add common directions, exterior directions, and matched pairs of perpendicular directions. This realizes the elementary multiplicities as well as the angle data. The construction also shows why a direct rotation on the generic planes is straightforward: rotate each plane by its prescribed angle, with a consistent sign convention.

## Acuteness, uniformity, and uniqueness

There remains an infinite-dimensional subtlety. It is possible for every angle to be strictly less than ninety degrees while a sequence of angles approaches ninety degrees. In that case, no individual perpendicular vector exists, but the largest-angle supremum is still ninety degrees.

The polar construction of the canonical intertwiner is tied to the cosine operator and its kernel. When both crossed defects vanish, the canonical partial-isometry construction has the appropriate unitary extension. A uniform projection gap below one gives stronger information: the cosine is bounded below and has a bounded inverse, so the direct rotation can also be written by the usual inverse-square-root formula without a singular limiting problem.

Do not confuse those two levels of hypothesis. Absence of an exact perpendicular vector does not guarantee a uniform gap.

Finally, this classification does not restore the false full-displacement optimization claim we examined previously. The geometry may determine a canonical direct rotation uniquely while another admissible transporter has a smaller unsquared trace displacement. Classification and optimization ask different questions.

## Final reconstruction

If you need to classify a pair, begin by extracting the four elementary intersection pieces. Match their dimensions. On the generic remainder, compare the cosine-square operators by unitary equivalence. In the compact case, compare their positive eigenvalues with multiplicities. If instead you need a concrete realization, build an orthogonal sum of principal planes and append the elementary pieces. And if you need a direct rotation, check crossed-defect matching and the desired boundedness or acuteness hypotheses before writing a polar formula.

Those operations close our geometric unit. Next we will see why the same abstract machinery becomes useful for a physical differential equation: the vibration modes of a free beam.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For orthogonal projections onto closed subspaces \(U,V\), define
\[
H_{11}=U\cap V,\quad H_{10}=U\cap V^\perp,\quad
H_{01}=U^\perp\cap V,\quad H_{00}=U^\perp\cap V^\perp.
\]
The generic part is the orthogonal complement of their sum. Its positive commuting cosine and sine operators satisfy \(C^2+S^2=I\). Unitary equivalence of the pairs preserves elementary multiplicities and the generic positive-contraction operator, including its non-eigenvalue spectral information. At appropriate compact scope, positive eigenvalue multiplicities classify the generic part. For a diagonal model with \(\theta_n\to0\), \(S^2\) is compact; \(C\) need not be compact.

## Exact Lean declaration excerpts


**`theorem3_1_realization_ofAngles`.** An admissible abstract angle datum is realized by a pair of closed subspaces. The ambient Hilbert space and two block dimensions are supplied by the datum; this is not a theorem that arbitrary angle lists fit inside a prechosen finite-dimensional ambient space.

`DavisKahan/Sources/DavisKahan1970/Section3Theorem31Realization.lean` — `theorem3_1_realization_ofAngles` (exact declaration header; proof body omitted):

```lean
theorem theorem3_1_realization_ofAngles
    {Θ₀ : E →L[𝕜] E} {Θ₁ : F →L[𝕜] F}
    (hΘ₀ : IsSelfAdjoint Θ₀) (hΘ₁ : IsSelfAdjoint Θ₁)
    (_hspec₀ : spectrum ℝ Θ₀ ⊆ Set.Icc 0 (Real.pi / 2))
    (_hspec₁ : spectrum ℝ Θ₁ ⊆ Set.Icc 0 (Real.pi / 2))
    (J : E →L[𝕜] F) (hJ : J ∘L Θ₀ = Θ₁ ∘L J)
    (hisom : ContinuousLinearMap.adjoint J ∘L J ∘L cfc Real.sin Θ₀ = cfc Real.sin Θ₀)
    (hcoisom : J ∘L ContinuousLinearMap.adjoint J ∘L cfc Real.sin Θ₁ = cfc Real.sin Θ₁) :
    (∀ x : E, (sourceSubspace 𝕜 E F).starProjection
        ((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace.starProjection (modelInl 𝕜 E F x)) =
          modelInl 𝕜 E F (cfc Real.cos Θ₀ (cfc Real.cos Θ₀ x))) ∧
      (∀ y : F, (sourceSubspace 𝕜 E F)ᗮ.starProjection
        (((HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace)ᗮ.starProjection (modelInr 𝕜 E F y)) =
          modelInr 𝕜 E F (cfc Real.cos Θ₁ (cfc Real.cos Θ₁ y))) ∧
      halmosCommonPart (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.sin Θ₀ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ∧
      halmosExteriorPart (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.sin Θ₁ : F →L[𝕜] F) : F →ₗ[𝕜] F)) ∧
      halmosSourceDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInl 𝕜 E F : E →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.cos Θ₀ : E →L[𝕜] E) : E →ₗ[𝕜] E)) ∧
      halmosTargetDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom hcoisom).targetSubspace =
        Submodule.map (modelInr 𝕜 E F : F →ₗ[𝕜] WithLp 2 (E × F))
          (LinearMap.ker ((cfc Real.cos Θ₁ : F →L[𝕜] F) : F →ₗ[𝕜] F)) ∧
      Nonempty (↥(halmosSourceDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace) ≃ₗᵢ[𝕜]
        ↥(halmosTargetDefect (sourceSubspace 𝕜 E F)
          (HalmosAngleDatum.ofIntertwinedAngles hΘ₀ hΘ₁ J hJ hisom
            hcoisom).targetSubspace)) :=
```


**`pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData`.** The four elementary Halmos summands and positive generic-angle multiplicities form the complete invariant under the specific compactness hypotheses on the sandwiched projections.

`DavisKahan/Geometry/Halmos/CompactClassification.lean` — `pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData` (exact declaration header; proof body omitted):

```lean
theorem pairOfSubspacesUnitaryEquivalent_iff_sameCompactAngleData
    (hc₁ : IsCompactOperator (U₁.starProjection ∘L V₁.starProjection ∘L U₁.starProjection))
    (hc₂ : IsCompactOperator (U₂.starProjection ∘L V₂.starProjection ∘L U₂.starProjection)) :
    PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      SameCompactAngleData U₁ V₁ U₂ V₂ :=
```


**`isCompactOperator_angleSinSqOp`.** This construction concerns the *squared sine* diagonal operator when the prescribed angles tend to zero; it must not be confused with compactness of the cosine operator.

`DavisKahan/Geometry/Halmos/AngleSequenceRealization.lean` — `isCompactOperator_angleSinSqOp` (exact declaration header; proof body omitted):

```lean
theorem isCompactOperator_angleSinSqOp (hlim : Tendsto θ atTop (nhds 0)) :
    IsCompactOperator (angleSinSqOp 𝕜 θ) :=
```
