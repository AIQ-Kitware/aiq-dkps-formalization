/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.DoubleAngle.TanTwoThetaKyFan
import DavisKahan.DoubleAngle.KyFanOrthonormal
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# The `tan 2Θ` theorem at every unitary-invariant ideal, infinite dimensions

The Davis--Kahan 1970 Section 7 tangent-double-angle estimate on an
arbitrary `RCLike` Hilbert space, for a finite-dimensional invariant-graph
configuration: `U` is a finite-dimensional subspace, `A` is block diagonal
for `U ⊕ Uᗮ` in the quadratic-form sense, `H` is fully off-diagonal, and
the graph coordinate `T` of the perturbed invariant subspace is supported
on `U` with values in `Uᗮ`.

The result is the source's norm scope in the repository's
infinite-dimensional idiom: for every `k`, the `k`-th Ky Fan
approximation-number prefix of any `tan 2Θ₀` representative is controlled
by that of `H` with constant two over the form gap, and consequently every
Fan-dominant unitary-invariant ideal family transports membership of `H`
to membership of `tan 2Θ₀` with the same gauge estimate.

## Method

Everything happens inside the finite-dimensional carrier
`M := U ⊔ T '' U`: the graph relation, the off-diagonal structure, and the
form bounds all compress exactly to `M`, because the invariance hypothesis
forces `(A + H)` to map the graph of `T` into `M`.  The compiled
finite-dimensional Ky Fan theorem
(`kyFan_doubleAngleTangent_offDiagonal_le`) applies to the compressions,
and the two Ky Fan prefixes transport back to the ambient operators along
`approximationSingularValue_comp_le` for the contractive inclusion and
projection, exactly for `T` and one-sidedly for `H`.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace
open DavisKahan.Experimental.ExactSinTheta
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

section Helpers

/-- The difference of nested orthogonal projections lands in the orthogonal
complement of the smaller subspace. -/
private theorem starProjection_sub_mem_orthogonal
    {U M : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (hUM : U ≤ M) (x : E) :
    M.starProjection x - U.starProjection x ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  rw [inner_sub_right]
  have h1 : ⟪w, M.starProjection x⟫_𝕜 = ⟪w, x⟫_𝕜 := by
    rw [← M.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hUM hw)]
  have h2 : ⟪w, U.starProjection x⟫_𝕜 = ⟪w, x⟫_𝕜 := by
    rw [← U.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hw]
  rw [h1, h2, sub_self]

/-- The orthogonal projection kills the orthogonal complement. -/
private theorem starProjection_eq_zero_of_mem_orthogonal
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    {x : E} (hx : x ∈ Uᗮ) :
    U.starProjection x = 0 := by
  have h := DFunLike.congr_fun (U.starProjection_orthogonal') x
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    Submodule.starProjection_eq_self_iff.mpr hx] at h
  exact sub_eq_self.mp h.symm

/-- The projection onto an intermediate subspace preserves the orthogonal
complement of a smaller subspace. -/
private theorem starProjection_mem_orthogonal_of_le
    {U M : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (hUM : U ≤ M)
    {x : E} (hx : x ∈ Uᗮ) :
    M.starProjection x ∈ Uᗮ := by
  have h := starProjection_sub_mem_orthogonal (𝕜 := 𝕜) hUM x
  rwa [starProjection_eq_zero_of_mem_orthogonal hx, sub_zero] at h

/-- The residual of an orthogonal projection is orthogonal to the target. -/
private theorem sub_starProjection_mem_orthogonal'
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (x : E) :
    x - U.starProjection x ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  rw [← inner_conj_symm, U.starProjection_inner_eq_zero x w hw, map_zero]

/-- Composition with contractions does not increase approximation singular
values. -/
private theorem approximationSingularValue_comp_contractions_le
    {E₁ F G G' : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup G'] [InnerProductSpace 𝕜 G'] [CompleteSpace G']
    (n : ℕ) (L : F →L[𝕜] G) (K : E₁ →L[𝕜] F) (R : G' →L[𝕜] E₁)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    approximationSingularValue n (L ∘L K ∘L R) ≤
      approximationSingularValue n K := by
  refine (approximationSingularValue_comp_le n L K R).trans ?_
  have h0 := approximationSingularValue_nonneg n K
  calc ‖L‖ * approximationSingularValue n K * ‖R‖
      ≤ 1 * approximationSingularValue n K * 1 := by
        refine mul_le_mul (mul_le_mul hL le_rfl h0 zero_le_one) hR
          (norm_nonneg _) ?_
        positivity
    _ = approximationSingularValue n K := by ring

end Helpers

section Main

variable {A H T : E →L[𝕜] E} {U : Submodule 𝕜 E} [FiniteDimensional 𝕜 U]
  {a b : ℝ}

/-- **The Ky Fan root of the `tan 2Θ` theorem on an arbitrary Hilbert
space** (finite-dimensional invariant configuration).  Every prefix sum of
the double-angle tangents of the graph-coordinate approximation numbers is
controlled by the corresponding approximation-number prefix of the
off-diagonal perturbation, with the sharp constant two. -/
theorem kyFan_doubleAngleTangent_offDiagonal_le_infinite
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : approximationSingularValue 0 T < 1)
    (k : ℕ) :
    (b - a) * ∑ n ∈ Finset.range k,
        doubleAngleTangent (approximationSingularValue n T) ≤
      2 * kyFanApproximationGauge k H := by
  classical
  -- the finite-dimensional carrier of the whole configuration
  set W : Submodule 𝕜 E := U.map (T : E →ₗ[𝕜] E) with hWdef
  set M : Submodule 𝕜 E := U ⊔ W with hMdef
  haveI : FiniteDimensional 𝕜 W := Module.Finite.map U (T : E →ₗ[𝕜] E)
  haveI : FiniteDimensional 𝕜 M := inferInstance
  haveI : CompleteSpace M := FiniteDimensional.complete 𝕜 ↥M
  have hUM : U ≤ M := le_sup_left
  have hMperpU : Mᗮ ≤ Uᗮ := Submodule.orthogonal_le hUM
  have hTsplit : ∀ x : E, T x = T (U.starProjection x) := by
    intro x
    have hz := hTzero _ (sub_starProjection_mem_orthogonal' (𝕜 := 𝕜) x)
    have hadd : T x = T (U.starProjection x) +
        T (x - U.starProjection x) := by
      rw [← map_add]
      congr 1
      abel
    rw [hadd, hz, add_zero]
  have hTM : ∀ x : E, T x ∈ M := by
    intro x
    rw [hTsplit x]
    exact Submodule.mem_sup_right
      (Submodule.mem_map_of_mem (U.starProjection_apply_mem x))
  -- the compressions
  set A' : ↥M →L[𝕜] ↥M :=
    M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL with hA'def
  set H' : ↥M →L[𝕜] ↥M :=
    M.orthogonalProjectionOnto ∘L H ∘L M.subtypeL with hH'def
  set T' : ↥M →L[𝕜] ↥M :=
    M.orthogonalProjectionOnto ∘L T ∘L M.subtypeL with hT'def
  have hcoeT : ∀ x : ↥M, ((T' x : ↥M) : E) = T (x : E) := by
    intro x
    show M.starProjection (T (x : E)) = T (x : E)
    exact Submodule.starProjection_eq_self_iff.mpr (hTM (x : E))
  -- the trial subspace inside the carrier
  set U' : Submodule 𝕜 ↥M := U.comap M.subtype with hU'def
  haveI : CompleteSpace U' := FiniteDimensional.complete 𝕜 ↥U'
  have hU'mem : ∀ x : ↥M, x ∈ U' ↔ (x : E) ∈ U := fun x => Iff.rfl
  have hU'perp : ∀ x : ↥M, x ∈ U'ᗮ ↔ (x : E) ∈ Uᗮ := by
    intro x
    constructor
    · intro hx
      rw [Submodule.mem_orthogonal]
      intro w hw
      have hwM : w ∈ M := hUM hw
      have h := (Submodule.mem_orthogonal U' x).mp hx ⟨w, hwM⟩
        ((hU'mem ⟨w, hwM⟩).mpr hw)
      rwa [Submodule.coe_inner] at h
    · intro hx
      rw [Submodule.mem_orthogonal]
      intro w hw
      rw [Submodule.coe_inner]
      exact (Submodule.mem_orthogonal U (x : E)).mp hx (w : E)
        ((hU'mem w).mp hw)
  -- symmetry of the compressions
  have hsym : ∀ (B : E →L[𝕜] E), IsSelfAdjoint B →
      (M.orthogonalProjectionOnto ∘L B ∘L
        M.subtypeL : ↥M →L[𝕜] ↥M).toLinearMap.IsSymmetric := by
    intro B hB x y
    show ⟪((M.orthogonalProjectionOnto ∘L B ∘L M.subtypeL) x : ↥M),
        y⟫_𝕜 = ⟪x, ((M.orthogonalProjectionOnto ∘L B ∘L M.subtypeL) y :
        ↥M)⟫_𝕜
    rw [Submodule.coe_inner, Submodule.coe_inner]
    show ⟪M.starProjection (B (x : E)), (y : E)⟫_𝕜 =
      ⟪(x : E), M.starProjection (B (y : E))⟫_𝕜
    calc ⟪M.starProjection (B (x : E)), (y : E)⟫_𝕜
        = ⟪B (x : E), M.starProjection (y : E)⟫_𝕜 :=
          M.inner_starProjection_left_eq_right _ _
      _ = ⟪B (x : E), (y : E)⟫_𝕜 := by
          rw [Submodule.starProjection_eq_self_iff.mpr y.2]
      _ = ⟪(x : E), B (y : E)⟫_𝕜 := hB.isSymmetric (x : E) (y : E)
      _ = ⟪M.starProjection (x : E), B (y : E)⟫_𝕜 := by
          rw [Submodule.starProjection_eq_self_iff.mpr x.2]
      _ = ⟪(x : E), M.starProjection (B (y : E))⟫_𝕜 :=
          M.inner_starProjection_left_eq_right _ _
  -- transfer the block hypotheses to the carrier
  have hAU' : ∀ x ∈ U', A'.toLinearMap x ∈ U' := by
    intro x hx
    have hAx : A (x : E) ∈ U := hAU _ ((hU'mem x).mp hx)
    refine (hU'mem _).mpr ?_
    show M.starProjection (A (x : E)) ∈ U
    rw [Submodule.starProjection_eq_self_iff.mpr (hUM hAx)]
    exact hAx
  have hHU' : ∀ x ∈ U', H'.toLinearMap x ∈ U'ᗮ := by
    intro x hx
    have hHx : H (x : E) ∈ Uᗮ := hHU _ ((hU'mem x).mp hx)
    refine (hU'perp _).mpr ?_
    show M.starProjection (H (x : E)) ∈ Uᗮ
    exact starProjection_mem_orthogonal_of_le hUM hHx
  have hHUperp' : ∀ x ∈ U'ᗮ, H'.toLinearMap x ∈ U' := by
    intro x hx
    have hHx : H (x : E) ∈ U := hHUperp _ ((hU'perp x).mp hx)
    refine (hU'mem _).mpr ?_
    show M.starProjection (H (x : E)) ∈ U
    rw [Submodule.starProjection_eq_self_iff.mpr (hUM hHx)]
    exact hHx
  have hTmem' : ∀ x : ↥M, T'.toLinearMap x ∈ U'ᗮ := by
    intro x
    refine (hU'perp _).mpr ?_
    show ((T' x : ↥M) : E) ∈ Uᗮ
    rw [hcoeT]
    exact hTmem (x : E)
  have hTzero' : ∀ x ∈ U'ᗮ, T'.toLinearMap x = 0 := by
    intro x hx
    apply Subtype.ext
    show ((T' x : ↥M) : E) = ((0 : ↥M) : E)
    rw [hcoeT]
    exact hTzero _ ((hU'perp x).mp hx)
  -- transfer the quadratic-form bounds
  have hpair : ∀ (B : E →L[𝕜] E) (x : ↥M),
      ⟪(M.orthogonalProjectionOnto ∘L B ∘L
          M.subtypeL : ↥M →L[𝕜] ↥M).toLinearMap x, x⟫_𝕜 =
        ⟪B (x : E), (x : E)⟫_𝕜 := by
    intro B x
    rw [Submodule.coe_inner]
    show ⟪M.starProjection (B (x : E)), (x : E)⟫_𝕜 = _
    rw [M.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr x.2]
  have hUb' : ∀ x ∈ U', b * ‖x‖ ^ 2 ≤
      RCLike.re ⟪A'.toLinearMap x, x⟫_𝕜 := by
    intro x hx
    have h := hUb (x : E) ((hU'mem x).mp hx)
    rw [hpair A x]
    exact h
  have hUa' : ∀ x ∈ U'ᗮ, RCLike.re ⟪A'.toLinearMap x, x⟫_𝕜 ≤
      a * ‖x‖ ^ 2 := by
    intro x hx
    have h := hUa (x : E) ((hU'perp x).mp hx)
    rw [hpair A x]
    exact h
  -- transfer the graph invariance
  have hinv' : ∀ x ∈ U', ∃ y ∈ U',
      (A'.toLinearMap + H'.toLinearMap) (x + T'.toLinearMap x) =
        y + T'.toLinearMap y := by
    intro x hx
    obtain ⟨y, hyU, hy⟩ := hinv (x : E) ((hU'mem x).mp hx)
    refine ⟨⟨y, hUM hyU⟩, hyU, ?_⟩
    apply Subtype.ext
    show M.starProjection (A ((x : E) + M.starProjection (T (x : E)))) +
        M.starProjection (H ((x : E) + M.starProjection (T (x : E)))) =
      y + M.starProjection (T y)
    rw [Submodule.starProjection_eq_self_iff.mpr (hTM (x : E)),
      Submodule.starProjection_eq_self_iff.mpr (hTM y)]
    have hyM : y + T y ∈ M := M.add_mem (hUM hyU) (hTM y)
    calc M.starProjection (A ((x : E) + T (x : E))) +
          M.starProjection (H ((x : E) + T (x : E)))
        = M.starProjection ((A + H) ((x : E) + T (x : E))) := by
          rw [ContinuousLinearMap.add_apply]
          exact (map_add M.starProjection _ _).symm
      _ = M.starProjection (y + T y) := by rw [hy]
      _ = y + T y := Submodule.starProjection_eq_self_iff.mpr hyM
  -- exact transport of the graph-coordinate singular values
  have hTfact : T = M.subtypeL ∘L T' ∘L M.orthogonalProjectionOnto := by
    ext x
    show T x = ((T' (M.orthogonalProjectionOnto x) : ↥M) : E)
    rw [hcoeT]
    show T x = T (M.starProjection x)
    have hperp : x - M.starProjection x ∈ Uᗮ :=
      hMperpU (sub_starProjection_mem_orthogonal' (𝕜 := 𝕜) x)
    have hz := hTzero _ hperp
    have hadd : T x = T (M.starProjection x) +
        T (x - M.starProjection x) := by
      rw [← map_add]
      congr 1
      abel
    rw [hadd, hz, add_zero]
  have hTa : ∀ n, approximationSingularValue n T' =
      approximationSingularValue n T := by
    intro n
    refine le_antisymm ?_ ?_
    · rw [hT'def]
      exact approximationSingularValue_comp_contractions_le n
        M.orthogonalProjectionOnto T M.subtypeL
        M.orthogonalProjectionOnto_norm_le M.norm_subtypeL_le
    · conv_lhs => rw [hTfact]
      exact approximationSingularValue_comp_contractions_le n
        M.subtypeL T' M.orthogonalProjectionOnto
        M.norm_subtypeL_le M.orthogonalProjectionOnto_norm_le
  have hT'id : T'.toLinearMap.toContinuousLinearMap = T' := by
    ext x; rfl
  have hTsv : ∀ n, T'.toLinearMap.singularValues n =
      approximationSingularValue n T := by
    intro n
    have h := approximationSingularValue_eq_singularValues T'.toLinearMap n
    rw [hT'id] at h
    rw [← h, hTa n]
  have hT1' : T'.toLinearMap.singularValues 0 < 1 := by
    rw [hTsv 0]
    exact hT1
  -- one-sided transport of the perturbation prefix
  have hH'id : H'.toLinearMap.toContinuousLinearMap = H' := by
    ext x; rfl
  have hHbridge :
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
        H'.toLinearMap = kyFanApproximationGauge k H' := by
    rw [rectangularKyFanSum_eq_kyFanApproximationGauge k H'.toLinearMap,
      hH'id]
  have hHgauge : kyFanApproximationGauge k H' ≤
      kyFanApproximationGauge k H := by
    unfold kyFanApproximationGauge
    refine Finset.sum_le_sum fun n _ => ?_
    rw [hH'def]
    exact approximationSingularValue_comp_contractions_le n
      M.orthogonalProjectionOnto H M.subtypeL
      M.orthogonalProjectionOnto_norm_le M.norm_subtypeL_le
  -- apply the finite theorem on the carrier
  have hfin := kyFan_doubleAngleTangent_offDiagonal_le
    (hsym A hA) (hsym H hH) hAU' hHU' hHUperp' hTmem' hTzero'
    hUb' hUa' hinv' hT1' k
  calc (b - a) * ∑ n ∈ Finset.range k,
        doubleAngleTangent (approximationSingularValue n T)
      = (b - a) * ∑ n ∈ Finset.range k,
          doubleAngleTangent (T'.toLinearMap.singularValues n) := by
        congr 1
        exact Finset.sum_congr rfl fun n _ => by rw [hTsv n]
    _ ≤ 2 * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k
          H'.toLinearMap := hfin
    _ = 2 * kyFanApproximationGauge k H' := by rw [hHbridge]
    _ ≤ 2 * kyFanApproximationGauge k H := by linarith

/-- Representative packaging of the infinite-dimensional Ky Fan root: any
operator between Hilbert spaces whose approximation numbers are the
double-angle tangents of the graph-coordinate approximation numbers obeys
the prefix bounds. -/
theorem kyFan_tanTwoTheta0_offDiagonal_le_infinite
    {E₂ F₂ : Type*}
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [CompleteSpace F₂]
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : approximationSingularValue 0 T < 1)
    (tanTwoTheta0 : E₂ →L[𝕜] F₂)
    (htan : ∀ n, approximationSingularValue n tanTwoTheta0 =
      doubleAngleTangent (approximationSingularValue n T))
    (k : ℕ) :
    (b - a) * kyFanApproximationGauge k tanTwoTheta0 ≤
      2 * kyFanApproximationGauge k H := by
  have hgauge : kyFanApproximationGauge k tanTwoTheta0 =
      ∑ n ∈ Finset.range k,
        doubleAngleTangent (approximationSingularValue n T) := by
    unfold kyFanApproximationGauge
    exact Finset.sum_congr rfl fun n _ => htan n
  rw [hgauge]
  exact kyFan_doubleAngleTangent_offDiagonal_le_infinite hA hH hAU hHU
    hHUperp hTmem hTzero hUb hUa hinv hT1 k

/-- **Davis--Kahan 1970, `tan 2Θ` theorem, every Fan-dominant
unitary-invariant ideal, arbitrary Hilbert space** (finite-dimensional
invariant configuration).  If the off-diagonal perturbation `H` belongs to
the ideal, then so does every `tan 2Θ₀` representative, and
`(b - a) · N(tan 2Θ₀) ≤ 2 · N(H)`. -/
theorem tanTwoTheta0_offDiagonal_mem_and_gauge_le_infinite
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : approximationSingularValue 0 T < 1)
    (tanTwoTheta0 : E →L[𝕜] E)
    (htan : ∀ n, approximationSingularValue n tanTwoTheta0 =
      doubleAngleTangent (approximationSingularValue n T))
    (hHmem : N.toRectangularSymmetricIdealFamily.Mem H) :
    N.toRectangularSymmetricIdealFamily.Mem tanTwoTheta0 ∧
      (b - a) * N.toRectangularSymmetricIdealFamily.gauge tanTwoTheta0 ≤
        2 * N.toRectangularSymmetricIdealFamily.gauge H := by
  have hδ : (0 : ℝ) < (b - a) / 2 := by linarith
  have hscaled : ∀ k,
      (b - a) / 2 * kyFanApproximationGauge k tanTwoTheta0 ≤
        kyFanApproximationGauge k H := by
    intro k
    have h := kyFan_tanTwoTheta0_offDiagonal_le_infinite hA hH hAU hHU
      hHUperp hTmem hTzero hUb hUa hinv hT1 tanTwoTheta0 htan k
    linarith
  obtain ⟨hmem, hgauge⟩ :=
    mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N hδ hHmem hscaled
  exact ⟨hmem, by linarith⟩

end Main

end DavisKahanTheory
end TauCeti