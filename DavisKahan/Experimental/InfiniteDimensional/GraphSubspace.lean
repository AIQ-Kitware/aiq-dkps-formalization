/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.OperatorAngle
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Graph subspaces and angular operators

Literature writeup: local TeX, Sections 16--17.  This is the geometric bridge
between projection estimates and operator Riccati equations.
-/


/-! ## Construction plan

* Define the graph subspace as the range of `x |-> (x, X x)` under the
  orthogonal-sum equivalence; for an ambient decomposition, transport this
  construction through `U x Uperp ~= E`.
* Prove the graph projection formula by solving the normal equations.  The
  diagonal factors are `(1+X⋆X)^{-1}` and `(1+XX⋆)^{-1}` and are positive
  invertible.
* Derive the graph/angular correspondence from transversality of the first
  coordinate projection, then identify the graph norm with tangent of the
  operator angle.
-/


/-! ## Donor API audit and execution plan

The graph-subspace vendor survey is recorded in
`dev/graph-subspace-vendor-survey-2026-07-14.md`.  The immediate proof should
reuse the pinned Mathlib APIs below rather than rebuilding closed-range or
inverse-continuity arguments locally.

Work with subtype maps rather than ambient formulas first.  Define the graph
embedding from `U` to `E` by `u ↦ u + X u`, where `IsAngularOperator U X`
ensures `X u ∈ Uᗮ`.  The Pythagorean identity gives a one-antilipschitz bound.
Use `AntilipschitzWith.isClosed_range` to obtain closedness of the range, then
the standard closed-subspace projection instance.

For acute-to-graph, restrict `projection U` to `V`.  The preferred inverse
routes are:

* `ContinuousLinearMap.equivRange` after injectivity and closed range are known;
* `ContinuousLinearEquiv.ofBijective` after direct injectivity and surjectivity;
* `Units.oneSub` for the near-identity compression when the acute norm bound
  yields an operator of norm strictly below one.

`LinearPMap.graph` and `LinearPMap.IsClosed` are the canonical graph language
for later alignment with the unbounded appendix.  The bounded graph may be
implemented first as a continuous-map range, but its comparison with the
`LinearPMap` graph should be explicit rather than introducing a second
unrelated graph notion.

The current unconditional projection instance for `graphSubspace U X` is a
signature defect: an arbitrary ambient `X` need not give a closed graph range.
The implementation pass must either add `hX : IsAngularOperator U X` to that
instance or bundle angularity into the graph object before closing it.

For the projection formula, define
`G := I + X.adjoint ∘L X` on `U`.  Prove `G ≥ I`, hence invertible, before
mentioning `G⁻¹` or `G⁻¹/²`.  Construct the normalized graph isometry
`J := graphEmbedding ∘ G⁻¹/²`; then the projection is `J ∘L J.adjoint`.
Expand this identity blockwise and only afterward package the ambient
`graphProjectionFormula`.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Graph subspace over `U` with angular operator `X`.

Defined as the topological closure of the parametrized graph range
`{P_U x + X (P_U x) | x}`, matching the range convention of
`acute_iff_exists_bounded_angularOperator`.  Taking the closure makes the
orthogonal-projection instance below unconditional; for an angular operator
the graph embedding is bounded below, its range is already closed, and the
closure adds nothing. -/
noncomputable def graphSubspace (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : E →L[𝕜] E) : Submodule 𝕜 E :=
  (LinearMap.range
    (projection U + X ∘L projection U).toLinearMap).topologicalClosure

noncomputable instance graphSubspace_hasOrthogonalProjection
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) : (graphSubspace U X).HasOrthogonalProjection := by
  have : CompleteSpace (graphSubspace U X) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- For an angular operator the graph embedding fixes the range pointwise
through `T ∘ P_U = T` and `P_U ∘ T = P_U`, so the parametrized graph range is
closed and the graph subspace is exactly that range. -/
theorem graphSubspace_eq_range (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] {X : E →L[𝕜] E}
    (hX : IsAngularOperator U X) :
    graphSubspace U X =
      LinearMap.range (projection U + X ∘L projection U).toLinearMap := by
  have hPX : ∀ y, projection U (X y) = 0 := fun y => by
    simpa using ContinuousLinearMap.ext_iff.mp hX.2 y
  have hidem : ∀ x, projection U (projection U x) = projection U x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  set T : E →L[𝕜] E := projection U + X ∘L projection U with hT
  have hPT : ∀ x, projection U (T x) = projection U x := by
    intro x
    simp only [hT, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, map_add]
    rw [hidem, hPX, add_zero]
  have hTP : ∀ x, T (projection U x) = T x := by
    intro x
    simp only [hT, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply]
    rw [hidem]
  have hclosed :
      IsClosed ((LinearMap.range T.toLinearMap : Submodule 𝕜 E) : Set E) := by
    rw [← isSeqClosed_iff_isClosed]
    intro seq y hseq hlim
    have hfix : ∀ n, seq n = T (projection U (seq n)) := by
      intro n
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (hseq n)
      have hx' : T x = seq n := hx
      rw [← hx', hPT, hTP]
    have hlim2 : Filter.Tendsto seq Filter.atTop
        (nhds (T (projection U y))) := by
      refine Filter.Tendsto.congr (fun n => (hfix n).symm) ?_
      exact ((T ∘L projection U).continuous.tendsto y).comp hlim
    exact ⟨projection U y, (tendsto_nhds_unique hlim hlim2).symm⟩
  refine le_antisymm ?_ (Submodule.le_topologicalClosure _)
  exact Submodule.topologicalClosure_minimal _ le_rfl hclosed

/-- Closed-formula candidate for the projection onto a graph. -/
noncomputable def graphProjectionFormula
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) : E →L[𝕜] E := by
  sorry

/-- Every acute subspace is the graph of a unique bounded angular operator.

Proof strategy:

* regard `P_U|_V : V -> U` as a bounded map between Banach spaces;
* prove it is bijective from the acute/equal-defect hypotheses;
* invoke the bounded inverse theorem;
* set `X u = P_{Uᗮ} ((P_U|_V)⁻¹ u)` and extend it by zero on `Uᗮ`;
* prove the graph equality by decomposing each `v ∈ V` into its `U` and
  `Uᗮ` components;
* prove uniqueness by applying `P_U` and `P_{Uᗮ}` to an arbitrary graph
  representation.

The finite-dimensional theorem should later be a specialization of this
result, not an independent basis calculation. 

Lean proof route for a weaker agent:

1. Obtain an angular operator from `acute_iff_exists_bounded_angularOperator`.
2. Show its range description agrees with `graphSubspace` by unfolding the latter.
3. For uniqueness, apply `P_U` and `P_{Uᗮ}` to equal graph vectors and use injectivity of the graph parametrization.


Ext-agent signature audit (GPT 5.6 High): Correct. Acuteness supplies both injectivity
and surjectivity of the coordinate projection and therefore uniqueness of the bounded
graph map.

Preferred dependency route: Build on the acute graph representation and the bounded
inverse theorem, then use functional calculus for `I + X*X` to obtain projection and
angle formulas.
-/
theorem existsUnique_angularOperator
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hacute : IsAcute U V) :
    ∃! X : E →L[𝕜] E,
      IsAngularOperator U X ∧ graphSubspace U X = V := by
  obtain ⟨X, hXang, hXrange⟩ :=
    (acute_iff_exists_bounded_angularOperator U V).mp hacute
  have hidem : ∀ x, projection U (projection U x) = projection U x := fun x =>
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem x)
  refine ⟨X, ⟨hXang, ?_⟩, ?_⟩
  · rw [graphSubspace_eq_range U hXang]
    exact hXrange.symm
  · rintro Y ⟨hYang, hYgraph⟩
    have hPX : ∀ y, projection U (X y) = 0 := fun y => by
      simpa using ContinuousLinearMap.ext_iff.mp hXang.2 y
    have hPY : ∀ y, projection U (Y y) = 0 := fun y => by
      simpa using ContinuousLinearMap.ext_iff.mp hYang.2 y
    have hranges :
        LinearMap.range (projection U + Y ∘L projection U).toLinearMap =
          LinearMap.range (projection U + X ∘L projection U).toLinearMap := by
      rw [← graphSubspace_eq_range U hYang, hYgraph, hXrange]
    have key : ∀ x, Y (projection U x) = X (projection U x) := by
      intro x
      have hmem : projection U x + Y (projection U x) ∈
          LinearMap.range (projection U + X ∘L projection U).toLinearMap := by
        rw [← hranges]
        exact ⟨x, rfl⟩
      obtain ⟨w, hw⟩ := hmem
      have hw' : projection U w + X (projection U w) =
          projection U x + Y (projection U x) := hw
      have happ := congrArg (fun z => projection U z) hw'
      simp only [map_add, hidem, hPX, hPY, add_zero] at happ
      rw [happ] at hw'
      exact (add_left_cancel hw').symm
    ext x
    calc Y x = Y (projection U x) := by
          rw [← ContinuousLinearMap.comp_apply, hYang.1]
      _ = X (projection U x) := key x
      _ = X x := by rw [← ContinuousLinearMap.comp_apply, hXang.1]

/-- Projection onto a graph subspace in terms of the angular operator.

Proof strategy: define the isometry from `U` into the graph by normalizing
`u ↦ u + X u` with `(I + X*X)^{-1/2}`.  The graph projection is `J J*`.
Expand this product in the decomposition `U ⊕ Uᗮ`, commute the functional
calculus terms through `X` using the polar decomposition, and identify the
four blocks with `graphProjectionFormula`.  Prove positivity and invertibility
of `I + X*X` before performing block algebra. 

Lean proof route for a weaker agent:

1. Define the normalized graph embedding `J u=(u,Xu)(I+X*X)^{-1/2}`.
2. Prove `J` is an isometry onto `graphSubspace U X`.
3. Compute the orthogonal projection as `J J*` and expand its four blocks.
4. Match the expanded expression with `graphProjectionFormula U X`.


Ext-agent signature audit (GPT 5.6 High): Correct only with `IsAngularOperator`; without
that hypothesis the ambient map may mix the base and complementary coordinates and the
advertised block formula is false.

Preferred dependency route: Build on the acute graph representation and the bounded
inverse theorem, then use functional calculus for `I + X*X` to obtain projection and
angle formulas.
-/
theorem projection_graphSubspace_formula
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    projection (graphSubspace U X) = graphProjectionFormula U X := by
  sorry

/-- Tangent of the maximal angle is the angular-operator norm. 

Lean proof route for a weaker agent:

1. Use `projection_graphSubspace_formula` to compute the gap between `U` and the graph.
2. Show the gap is `‖X‖/sqrt(1+‖X‖²)` by functional calculus and spectral mapping.
3. Apply the scalar identity `tan(arcsin(x/sqrt(1+x²)))=x` for `x≥0`.


Ext-agent signature audit (GPT 5.6 High): Correct because every bounded graph is acute.
The proof must establish the angle range before applying inverse trigonometric
identities.

Preferred dependency route: Build on the acute graph representation and the bounded
inverse theorem, then use functional calculus for `I + X*X` to obtain projection and
angle formulas.
-/
theorem tan_maximalAngle_eq_norm_angularOperator
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    Real.tan (maximalAngle U (graphSubspace U X)) = ‖X‖ := by
  sorry

/-- Contractive angular operators correspond to angles below `π / 4`. 

Lean proof route for a weaker agent:

1. Rewrite the angle with `tan_maximalAngle_eq_norm_angularOperator`.
2. Establish `0≤maximalAngle<π/2` for a graph subspace.
3. Use strict monotonicity of `tan` and `tan(π/4)=1` to prove both implications.


Ext-agent signature audit (GPT 5.6 High): Correct after the preceding tangent identity
and the fact that graph angles lie in `[0,π/2)`.

Preferred dependency route: Build on the acute graph representation and the bounded
inverse theorem, then use functional calculus for `I + X*X` to obtain projection and
angle formulas.
-/
theorem norm_angularOperator_lt_one_iff
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (X : E →L[𝕜] E) (hX : IsAngularOperator U X) :
    ‖X‖ < 1 ↔ maximalAngle U (graphSubspace U X) < Real.pi / 4 := by
  sorry

end DavisKahanExt
end ForMathlib
