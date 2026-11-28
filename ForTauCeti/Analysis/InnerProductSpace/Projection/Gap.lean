/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Projection.Gap

/-!
# Gap geometry for orthogonally complemented subspaces

The symmetric and directed projection gaps over arbitrary `RCLike` scalars.
-/

public section


open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

/-- **A nonzero crossed intersection pins the directed gap at one.**

A vector of `U ⊓ Vᗮ` is fixed by `P_U` and by `P_{Vᗮ}`, hence by their
composite, so the directed gap attains its maximum.  This is the "defect
block contributes the singular value `1`" half of the Halmos picture, and it
needs no decomposition to state or to prove. -/
theorem directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⊓ Vᗮ ≠ ⊥) :
    U.directedProjectionGap V = 1 := by
  refine le_antisymm (U.directedProjectionGap_le_one V) (le_of_not_gt ?_)
  intro hlt
  exact h (disjoint_iff.mp (U.disjoint_orthogonal_of_directedProjectionGap_lt_one V hlt))

end Submodule

variable [CompleteSpace E]

namespace Submodule

/-! ### When the two directed gaps agree

The directed gap is genuinely asymmetric: `U = ⊤`, `V` a proper subspace has
`U.directedProjectionGap V = 1` and `V.directedProjectionGap U = 0`.  The three
results below isolate exactly what removes the asymmetry, and it is the pair of
*crossed intersections* `U ⊓ Vᗮ` and `Uᗮ ⊓ V` — Davis--Kahan 1970's Section 3
standing assumption (3.5) in its qualitative form.

The engine is `directedProjectionGap_le_of_inf_orthogonal_eq_bot`, and its proof
is two lines of Cauchy--Schwarz plus one density argument, with no Halmos
decomposition and no spectral theory:

* writing `c` for `√(1 - ‖P_{Vᗮ} P_U‖²)`, Pythagoras turns the directed bound
  into `c ‖u‖ ≤ ‖P_V u‖` for every `u ∈ U`;
* for `u ∈ U` and `a = P_V u`, `⟪P_U a, u⟫ = ⟪a, a⟫`, so Cauchy--Schwarz gives
  `‖a‖² ≤ ‖P_U a‖ ‖u‖`, and dividing by `‖u‖` propagates the same constant to
  `a`: `c ‖a‖ ≤ ‖P_U a‖`;
* `P_V '' U` is dense in `V` when `Uᗮ ⊓ V = ⊥`, and `c ‖x‖ ≤ ‖P_U x‖` is a
  closed condition, so the bound holds on all of `V`, which is the reverse
  directed estimate.

Only one crossed intersection is used per direction, and only through
`Uᗮ ⊓ V = ⊥`; that asymmetry is what makes the combined hypothesis an
if-and-only-if rather than a conjunction. -/

/-- **One vanishing crossed intersection reverses the directed gap estimate.**

If `Uᗮ ⊓ V = ⊥` then `‖P_{Uᗮ} P_V‖ ≤ ‖P_{Vᗮ} P_U‖`.  Geometrically: with no
part of `V` orthogonal to `U`, the image `P_V '' U` is dense in `V`, and the
worst tilt of `V` away from `U` is already witnessed by the tilt of `U` away
from `V`. -/
theorem directedProjectionGap_le_of_inf_orthogonal_eq_bot (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : Uᗮ ⊓ V = ⊥) :
    V.directedProjectionGap U ≤ U.directedProjectionGap V := by
  set t := U.directedProjectionGap V with ht
  have ht0 : 0 ≤ t := U.directedProjectionGap_nonneg V
  have ht1 : t ≤ 1 := U.directedProjectionGap_le_one V
  have hk0 : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
  set c := Real.sqrt (1 - t ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hk0
  -- Pythagoras turns the directed bound into a lower bound for `P_V` on `U`.
  have hstep1 : ∀ u ∈ U, c * ‖u‖ ≤ ‖V.starProjection u‖ := by
    intro u hu
    have hperp := (U.directedProjectionGap_le_iff V ht0).mp (le_of_eq ht.symm) u hu
    have hpy : ‖u‖ ^ 2 = ‖V.starProjection u‖ ^ 2 + ‖Vᗮ.starProjection u‖ ^ 2 :=
      V.norm_sq_eq_add_norm_sq_starProjection u
    have hsq : (c * ‖u‖) ^ 2 ≤ ‖V.starProjection u‖ ^ 2 := by
      have hsqperp : ‖Vᗮ.starProjection u‖ ^ 2 ≤ (t * ‖u‖) ^ 2 := by
        nlinarith [norm_nonneg (Vᗮ.starProjection u),
          mul_nonneg ht0 (norm_nonneg u)]
      have hexpand : (c * ‖u‖) ^ 2 = ‖u‖ ^ 2 - (t * ‖u‖) ^ 2 := by
        rw [mul_pow, mul_pow, hcsq]; ring
      rw [hexpand]
      linarith
    calc c * ‖u‖ = Real.sqrt ((c * ‖u‖) ^ 2) :=
          (Real.sqrt_sq (mul_nonneg hc0 (norm_nonneg u))).symm
      _ ≤ Real.sqrt (‖V.starProjection u‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖V.starProjection u‖ := Real.sqrt_sq (norm_nonneg _)
  -- The same constant propagates to the image `P_V '' U` by Cauchy--Schwarz.
  set S : Submodule 𝕜 E := U.map (V.starProjection : E →ₗ[𝕜] E) with hS
  set T : Set E := {x : E | c * ‖x‖ ≤ ‖U.starProjection x‖} with hT
  have hTclosed : IsClosed T :=
    isClosed_le (continuous_const.mul continuous_norm)
      (continuous_norm.comp U.starProjection.continuous)
  have hST : (S : Set E) ⊆ T := by
    rintro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    change c * ‖V.starProjection u‖ ≤ ‖U.starProjection (V.starProjection u)‖
    rcases eq_or_ne (V.starProjection u) 0 with h0 | h0
    · rw [h0]; simp
    have hunorm : 0 < ‖u‖ := by
      refine norm_pos_iff.mpr fun huz => h0 ?_
      rw [huz, map_zero]
    have hzero : ⟪V.starProjection u, u - V.starProjection u⟫_𝕜 = 0 :=
      inner_eq_zero_symm.mp
        (V.starProjection_inner_eq_zero u _ (V.starProjection_apply_mem u))
    have hself : ⟪V.starProjection u, u⟫_𝕜
        = ⟪V.starProjection u, V.starProjection u⟫_𝕜 := by
      have hsub := inner_sub_right (𝕜 := 𝕜) (V.starProjection u) u (V.starProjection u)
      rw [hzero] at hsub
      exact sub_eq_zero.mp hsub.symm
    have hmove : ⟪U.starProjection (V.starProjection u), u⟫_𝕜
        = ⟪V.starProjection u, V.starProjection u⟫_𝕜 := by
      rw [Submodule.inner_starProjection_left_eq_right U,
        Submodule.starProjection_eq_self_iff.mpr hu, hself]
    have hcs : ‖V.starProjection u‖ * ‖V.starProjection u‖
        ≤ ‖U.starProjection (V.starProjection u)‖ * ‖u‖ := by
      have hbound := norm_inner_le_norm (𝕜 := 𝕜)
        (U.starProjection (V.starProjection u)) u
      have hnormself : ‖⟪V.starProjection u, V.starProjection u⟫_𝕜‖
          = ‖V.starProjection u‖ * ‖V.starProjection u‖ := by
        rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _), sq]
      rwa [hmove, hnormself] at hbound
    have hlow : c * ‖u‖ * ‖V.starProjection u‖
        ≤ ‖V.starProjection u‖ * ‖V.starProjection u‖ :=
      mul_le_mul_of_nonneg_right (hstep1 u hu) (norm_nonneg _)
    nlinarith [hcs, hlow, hunorm, norm_pos_iff.mpr h0]
  -- `P_V '' U` is dense in `V` precisely because `Uᗮ ⊓ V = ⊥`.
  have hVle : V ≤ Sᗮᗮ := by
    intro v hv
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hy' := (Submodule.mem_orthogonal S y).mp hy
    have hyV : V.starProjection y = 0 := by
      have hmem : V.starProjection y ∈ Uᗮ ⊓ V := by
        refine Submodule.mem_inf.mpr ⟨?_, V.starProjection_apply_mem y⟩
        rw [Submodule.mem_orthogonal]
        intro u hu
        have hzu : ⟪V.starProjection u, y⟫_𝕜 = 0 :=
          hy' (V.starProjection u) (Submodule.mem_map_of_mem hu)
        rwa [Submodule.inner_starProjection_left_eq_right] at hzu
      rw [h] at hmem
      simpa using hmem
    have hyperp : y ∈ Vᗮ := (Submodule.starProjection_apply_eq_zero_iff V).mp hyV
    exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal V y).mp hyperp v hv)
  have hstep3 : ∀ v ∈ V, c * ‖v‖ ≤ ‖U.starProjection v‖ := by
    intro v hv
    have hmem : v ∈ closure (S : Set E) := by
      have hvv := hVle hv
      rwa [Submodule.orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe,
        Submodule.topologicalClosure_coe] at hvv
    exact hTclosed.closure_subset_iff.mpr hST hmem
  -- Reversing Pythagoras on `V` is the reverse directed estimate.
  apply (V.directedProjectionGap_le_iff U ht0).mpr
  intro v hv
  have hpy := U.norm_sq_eq_add_norm_sq_starProjection v
  have hc2 : (c * ‖v‖) ^ 2 ≤ ‖U.starProjection v‖ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hc0 (norm_nonneg v)) (norm_nonneg _)).mpr (hstep3 v hv)
  have hexpand : (c * ‖v‖) ^ 2 = ‖v‖ ^ 2 - (t * ‖v‖) ^ 2 := by
    rw [mul_pow, mul_pow, hcsq]
    ring
  rw [hexpand] at hc2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht0 (norm_nonneg v))).mp
  linarith

/-- **The two directed gaps agree exactly when the crossed intersections vanish
together.**

The hypothesis is the qualitative content of Davis--Kahan 1970's standing
assumption (3.5): *one* crossed defect is trivial if and only if the other is.
It is strictly weaker than assuming both vanish, and strictly weaker than an
equality of dimensions; it is what the norm statement actually consumes.

Both branches are elementary.  When both crossed intersections vanish, the two
applications of `directedProjectionGap_le_of_inf_orthogonal_eq_bot` are the two
inequalities.  When neither vanishes, both directed gaps are pinned at `1` by
`directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot`. -/
theorem directedProjectionGap_comm_of_inf_orthogonal_eq_bot_iff (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U ⊓ Vᗮ = ⊥ ↔ Uᗮ ⊓ V = ⊥) :
    U.directedProjectionGap V = V.directedProjectionGap U := by
  by_cases hb : U ⊓ Vᗮ = ⊥
  · have hb' : Uᗮ ⊓ V = ⊥ := h.mp hb
    refine le_antisymm
      (V.directedProjectionGap_le_of_inf_orthogonal_eq_bot U (by rwa [inf_comm] at hb)) ?_
    exact U.directedProjectionGap_le_of_inf_orthogonal_eq_bot V hb'
  · have hb' : Uᗮ ⊓ V ≠ ⊥ := fun hc => hb (h.mpr hc)
    rw [U.directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot V hb,
      V.directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot U
        (by rwa [inf_comm] at hb')]

/-- **The symmetric gap is the directed gap under the crossed-defect
hypothesis.**

`projectionGap` is the maximum of the two directed gaps, so once they agree it
is either one of them.  This is the identification Davis--Kahan use to read a
directed `sin Θ` estimate as a statement about `‖P_U - P_V‖`, and it is the
place their Section 3 standing assumption enters. -/
theorem projectionGap_eq_directedProjectionGap_of_inf_orthogonal_eq_bot_iff
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U ⊓ Vᗮ = ⊥ ↔ Uᗮ ⊓ V = ⊥) :
    U.projectionGap V = U.directedProjectionGap V := by
  rw [Submodule.projectionGap_eq_max,
    ← U.directedProjectionGap_comm_of_inf_orthogonal_eq_bot_iff V h, max_self]


end Submodule

