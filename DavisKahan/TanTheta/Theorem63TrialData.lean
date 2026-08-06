/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

import DavisKahan.TanTheta.Theorem63FiniteSource

/-!
# Theorem 6.3 over abstract trial-block data

The finite-trial Theorem 6.3 chain in `Theorem63FiniteSource.lean` takes a bounded
symmetric ambient operator `T` and derives the compression and Ritz residual from it.  The
paper's unbounded scope claim needs the same chain when the ambient operator is a closed
unbounded self-adjoint operator: there the trial action, its compression, and its residual
are still bounded (the trial subspace sits inside the operator domain with bounded block
data), but no bounded ambient operator exists.

This module isolates exactly what the tangent chain consumes as **data**:

* `Theorem63TrialData`: the bounded trial action `Z →L H`, its compression, and its
  residual, tied by the block identity and residual orthogonality;
* the two **form hypotheses** — the compression bounded above by `α`, and the crossed
  pairing `⟪P_{Vᗮ} z, P_{Vᗮ} (action z)⟫` bounded below by `(α + δ) ‖P_{Vᗮ} z‖²` — the
  latter replacing the unbounded operator's quadratic form on `Vᗮ`, which is only defined
  on the operator domain; on vectors of the form `P_{Vᗮ} z` with `z` in the trial space it
  is available through spectral commutation, and those are the only vectors the singular
  value argument ever uses;
* the finite-trial Ky Fan core over this data
  (`Theorem63TrialData.all_kyFan_core_directedTangent`).

The orthonormality of the residual witnesses is reused from the bounded chain through a
**surrogate operator**: the witness family depends only on the geometry of the sine block
and on its singular values sitting strictly below one, so `Vᗮ.starProjection` itself
serves as a bounded symmetric operator satisfying the bounded chain's hypotheses.

`Theorem63TrialData.ofBounded` recovers the bounded chain's data, so the bounded theorems
are instances.
-/

open scoped InnerProductSpace BigOperators

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactTanTheta

open ExactSinTheta
open Module (finrank)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The bounded data of a trial block for the Theorem 6.3 chain: the ambient action of
the trial subspace, its compression back into the trial subspace, and the residual,
tied by the block identity.  For a bounded symmetric ambient operator these are
`T ∘L Z.subtypeL`, `theorem63Compression T Z`, and `theorem63Residual T Z`; for an
unbounded self-adjoint operator whose domain contains the trial subspace they are the
bundled data of an `UnboundedTrialBlock`. -/
structure Theorem63TrialData (Z V : Submodule ℂ H)
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] where
  /-- The ambient action of the trial subspace. -/
  action : Z →L[ℂ] H
  /-- The compression of the action back into the trial subspace. -/
  compression : Z →L[ℂ] Z
  /-- The Ritz residual of the trial subspace. -/
  residual : Z →L[ℂ] H
  /-- The compression is symmetric. -/
  compression_isSymmetric : compression.IsSymmetric
  /-- The block identity: action = compression + residual. -/
  action_eq : ∀ z : Z, action z = ((compression z : Z) : H) + residual z
  /-- The residual is orthogonal to the trial subspace. -/
  residual_orthogonal : ∀ (z z' : Z), ⟪residual z, ((z' : Z) : H)⟫_ℂ = 0

namespace Theorem63TrialData

variable {Z V : Submodule ℂ H} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- The residual is orthogonal to the trial subspace, inner product on the left. -/
theorem inner_residual_left (data : Theorem63TrialData Z V) (z z' : Z) :
    ⟪((z' : Z) : H), data.residual z⟫_ℂ = 0 := by
  rw [← inner_conj_symm, data.residual_orthogonal z z', map_zero]

omit [CompleteSpace H] in
/-- The residual lands in the orthogonal complement of the trial subspace. -/
theorem residual_mem_orthogonal (data : Theorem63TrialData Z V) (z : Z) :
    data.residual z ∈ Zᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  exact data.inner_residual_left z ⟨u, hu⟩

omit [CompleteSpace H] in
/-- The compression is the trial projection of the action. -/
theorem starProjection_action (data : Theorem63TrialData Z V) (z : Z) :
    Z.starProjection (data.action z) = ((data.compression z : Z) : H) := by
  rw [data.action_eq z, map_add,
    Submodule.starProjection_eq_self_iff.mpr (data.compression z).2,
    (Submodule.starProjection_apply_eq_zero_iff Z).mpr
      (data.residual_mem_orthogonal z), add_zero]

omit [CompleteSpace H] in
/-- The compression's quadratic form is the ambient pairing of the action. -/
theorem inner_compression_eq (data : Theorem63TrialData Z V) (z : Z) :
    ⟪data.compression z, z⟫_ℂ = ⟪data.action z, ((z : Z) : H)⟫_ℂ := by
  rw [Submodule.coe_inner, data.action_eq z, inner_add_left,
    data.residual_orthogonal z z, add_zero]

omit [CompleteSpace H] in
/-- The sine-side Sylvester identity, in pure block algebra: projecting the action onto
`Vᗮ` is the sine block of the compression plus the projected residual. -/
theorem sineSylvester (data : Theorem63TrialData Z V) (v : Z) :
    Vᗮ.starProjection (data.action v) =
      theorem63DirectedSineBlock Z V (data.compression v) +
        Vᗮ.starProjection (data.residual v) := by
  rw [data.action_eq v, map_add]
  rfl

/-! ### The bounded instance -/

/-- The trial-block data of a bounded symmetric ambient operator. -/
noncomputable def ofBounded (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Theorem63TrialData Z V where
  action := T ∘L Z.subtypeL
  compression := theorem63Compression T Z
  residual := theorem63Residual T Z
  compression_isSymmetric := by
    intro x y
    calc
      ⟪(theorem63Compression T Z x : Z), y⟫_ℂ =
          ⟪T ((x : Z) : H), ((y : Z) : H)⟫_ℂ := by
        rw [Submodule.coe_inner]
        change ⟪(Z.orthogonalProjectionOnto (T ((x : Z) : H)) : H), ((y : Z) : H)⟫_ℂ = _
        have hc : (Z.orthogonalProjectionOnto (T ((x : Z) : H)) : H) =
            Z.starProjection (T ((x : Z) : H)) := rfl
        rw [hc, Z.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr y.2]
      _ = ⟪((x : Z) : H), T ((y : Z) : H)⟫_ℂ := hT _ _
      _ = ⟪x, theorem63Compression T Z y⟫_ℂ := by
        rw [Submodule.coe_inner]
        change _ = ⟪((x : Z) : H), (Z.orthogonalProjectionOnto (T ((y : Z) : H)) : H)⟫_ℂ
        have hc : (Z.orthogonalProjectionOnto (T ((y : Z) : H)) : H) =
            Z.starProjection (T ((y : Z) : H)) := rfl
        rw [hc, ← Z.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.mpr x.2]
  action_eq := fun z => by
    change T ((z : Z) : H) = ((theorem63Compression T Z z : Z) : H) +
      theorem63Residual T Z z
    have h := theorem63Residual_eq_complementaryProjection T Z
    have hz := congrArg (fun L : Z →L[ℂ] H => L z) h
    simp only [ContinuousLinearMap.comp_apply] at hz
    have hsplit := (Submodule.starProjection_add_starProjection_orthogonal
      (K := Z) (T ((z : Z) : H))).symm
    rw [hz]
    have hc : ((theorem63Compression T Z z : Z) : H) =
        Z.starProjection (T ((z : Z) : H)) := rfl
    rw [hc]
    exact hsplit
  residual_orthogonal := fun z z' =>
    Submodule.inner_left_of_mem_orthogonal z'.2
      (theorem63Residual_apply_mem_orthogonal T Z z)

omit [CompleteSpace H] in
/-- The bounded instance's residual is the Ritz residual. -/
theorem ofBounded_residual (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (ofBounded T hT Z V).residual = theorem63Residual T Z := rfl

omit [CompleteSpace H] in
/-- The bounded instance's compression is the Ritz compression. -/
theorem ofBounded_compression (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (ofBounded T hT Z V).compression = theorem63Compression T Z := rfl

/-- The crossed form hypothesis holds for a bounded symmetric operator that reduces `V`
and is bounded below on `Vᗮ`. -/
theorem ofBounded_crossed_lower (T : H →L[ℂ] H) (hT : T.IsSymmetric)
    (Z V : Submodule ℂ H) [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hV : T.Reduces V) {c : ℝ}
    (hUnwantedLower : ∀ y ∈ Vᗮ, c * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ) (z : Z) :
    c * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection ((ofBounded T hT Z V).action z)⟫_ℂ := by
  set y : H := Vᗮ.starProjection ((z : Z) : H) with hy_def
  have hyV : y ∈ Vᗮ := Vᗮ.starProjection_apply_mem _
  have haction : (ofBounded T hT Z V).action z = T ((z : Z) : H) := rfl
  have hsplit : T ((z : Z) : H) =
      T (V.starProjection ((z : Z) : H)) + T y := by
    rw [hy_def, ← map_add]
    congr 1
    exact (Submodule.starProjection_add_starProjection_orthogonal
      (K := V) ((z : Z) : H)).symm
  have hpair : ⟪y, Vᗮ.starProjection (T ((z : Z) : H))⟫_ℂ = ⟪y, T y⟫_ℂ := by
    rw [← Vᗮ.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hyV, hsplit, inner_add_right]
    have hTV : T (V.starProjection ((z : Z) : H)) ∈ V :=
      hV.1 _ (V.starProjection_apply_mem _)
    rw [Submodule.inner_left_of_mem_orthogonal hTV hyV, zero_add]
  rw [haction, hpair]
  have h := hUnwantedLower y hyV
  calc
    c * ‖y‖ ^ 2 ≤ RCLike.re ⟪T y, y⟫_ℂ := h
    _ = RCLike.re ⟪y, T y⟫_ℂ := by
      rw [← inner_conj_symm, RCLike.conj_re]

/-! ### Restriction to a subspace of the trial space -/

/-- The continuous inclusion of one submodule into a larger one. -/
noncomputable def inclCLM {F Z : Submodule ℂ H} (hFZ : F ≤ Z) : F →L[ℂ] Z :=
  (Submodule.inclusion hFZ).mkContinuous 1 (fun x => by
    change ‖((x : F) : H)‖ ≤ 1 * ‖x‖
    simp)

omit [CompleteSpace H] in
/-- The inclusion does not move the ambient vector. -/
theorem inclCLM_coe {F Z : Submodule ℂ H} (hFZ : F ≤ Z) (x : F) :
    ((inclCLM hFZ x : Z) : H) = ((x : F) : H) := rfl

/-- The trial-block data restricted to a subspace of the trial space. -/
noncomputable def restrict (data : Theorem63TrialData Z V)
    (F : Submodule ℂ H) (hFZ : F ≤ Z) [F.HasOrthogonalProjection] :
    Theorem63TrialData F V where
  action := data.action ∘L inclCLM hFZ
  compression := F.orthogonalProjectionOnto ∘L data.action ∘L inclCLM hFZ
  residual := data.action ∘L inclCLM hFZ -
    F.subtypeL ∘L (F.orthogonalProjectionOnto ∘L data.action ∘L inclCLM hFZ)
  compression_isSymmetric := by
    intro x y
    have hx : ⟪(F.orthogonalProjectionOnto (data.action (inclCLM hFZ x)) : F), y⟫_ℂ =
        ⟪data.action (inclCLM hFZ x), ((y : F) : H)⟫_ℂ := by
      rw [Submodule.coe_inner]
      have hc : ((F.orthogonalProjectionOnto (data.action (inclCLM hFZ x)) : F) : H) =
          F.starProjection (data.action (inclCLM hFZ x)) := rfl
      rw [hc, F.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr y.2]
    have hy : ⟪x, (F.orthogonalProjectionOnto (data.action (inclCLM hFZ y)) : F)⟫_ℂ =
        ⟪((x : F) : H), data.action (inclCLM hFZ y)⟫_ℂ := by
      rw [Submodule.coe_inner]
      have hc : ((F.orthogonalProjectionOnto (data.action (inclCLM hFZ y)) : F) : H) =
          F.starProjection (data.action (inclCLM hFZ y)) := rfl
      rw [hc, ← F.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr x.2]
    have hmid : ⟪data.action (inclCLM hFZ x), ((y : F) : H)⟫_ℂ =
        ⟪((x : F) : H), data.action (inclCLM hFZ y)⟫_ℂ := by
      have h1 : ⟪data.action (inclCLM hFZ x), ((y : F) : H)⟫_ℂ =
          ⟪data.compression (inclCLM hFZ x), inclCLM hFZ y⟫_ℂ := by
        rw [data.action_eq (inclCLM hFZ x), inner_add_left]
        have hres := data.residual_orthogonal (inclCLM hFZ x) (inclCLM hFZ y)
        rw [inclCLM_coe] at hres
        rw [hres, add_zero, Submodule.coe_inner]
        rfl
      have h2 : ⟪((x : F) : H), data.action (inclCLM hFZ y)⟫_ℂ =
          ⟪inclCLM hFZ x, data.compression (inclCLM hFZ y)⟫_ℂ := by
        rw [data.action_eq (inclCLM hFZ y), inner_add_right]
        have hres := data.inner_residual_left (inclCLM hFZ y) (inclCLM hFZ x)
        rw [inclCLM_coe] at hres
        rw [hres, add_zero, Submodule.coe_inner]
        rfl
      rw [h1, h2]
      exact data.compression_isSymmetric _ _
    calc
      ⟪((F.orthogonalProjectionOnto ∘L data.action ∘L inclCLM hFZ) x : F), y⟫_ℂ =
          ⟪data.action (inclCLM hFZ x), ((y : F) : H)⟫_ℂ := hx
      _ = ⟪((x : F) : H), data.action (inclCLM hFZ y)⟫_ℂ := hmid
      _ = ⟪x, ((F.orthogonalProjectionOnto ∘L data.action ∘L inclCLM hFZ) y : F)⟫_ℂ :=
        hy.symm
  action_eq := fun z => by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
    have hc : ((F.orthogonalProjectionOnto (data.action (inclCLM hFZ z)) : F) : H) =
        F.starProjection (data.action (inclCLM hFZ z)) := rfl
    change data.action (inclCLM hFZ z) =
      F.starProjection (data.action (inclCLM hFZ z)) +
        (data.action (inclCLM hFZ z) -
          F.starProjection (data.action (inclCLM hFZ z)))
    abel
  residual_orthogonal := fun z z' => by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply]
    change ⟪data.action (inclCLM hFZ z) -
        F.starProjection (data.action (inclCLM hFZ z)), ((z' : F) : H)⟫_ℂ = 0
    have hmem : data.action (inclCLM hFZ z) -
        F.starProjection (data.action (inclCLM hFZ z)) ∈ Fᗮ := by
      have h := Submodule.sub_starProjection_mem_orthogonal
        (K := F) (data.action (inclCLM hFZ z))
      exact h
    exact Submodule.inner_left_of_mem_orthogonal z'.2 hmem

omit [CompleteSpace H] in
/-- The restricted action, applied. -/
theorem restrict_action_apply (data : Theorem63TrialData Z V)
    (F : Submodule ℂ H) (hFZ : F ≤ Z) [F.HasOrthogonalProjection] (f : F) :
    (data.restrict F hFZ).action f = data.action (inclCLM hFZ f) := rfl

omit [CompleteSpace H] in
/-- The compression form bound restricts to every subspace of the trial space. -/
theorem restrict_compression_upper (data : Theorem63TrialData Z V)
    (F : Submodule ℂ H) (hFZ : F ≤ Z) [F.HasOrthogonalProjection] {alpha : ℝ}
    (hM : ∀ z : Z, RCLike.re ⟪data.compression z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2) :
    ∀ f : F, RCLike.re ⟪(data.restrict F hFZ).compression f, f⟫_ℂ ≤
      alpha * ‖f‖ ^ 2 := by
  intro f
  have h1 : ⟪(data.restrict F hFZ).compression f, f⟫_ℂ =
      ⟪(data.restrict F hFZ).action f, ((f : F) : H)⟫_ℂ :=
    (data.restrict F hFZ).inner_compression_eq f
  have h2 : ⟪data.compression (inclCLM hFZ f), inclCLM hFZ f⟫_ℂ =
      ⟪data.action (inclCLM hFZ f), ((inclCLM hFZ f : Z) : H)⟫_ℂ :=
    data.inner_compression_eq (inclCLM hFZ f)
  have hle := hM (inclCLM hFZ f)
  rw [h2] at hle
  rw [h1, restrict_action_apply]
  have hcoe : ((inclCLM hFZ f : Z) : H) = ((f : F) : H) := rfl
  rw [hcoe] at hle
  have hnorm : ‖inclCLM hFZ f‖ = ‖f‖ := rfl
  rw [hnorm] at hle
  exact hle

omit [CompleteSpace H] in
/-- The crossed lower form bound restricts to every subspace of the trial space. -/
theorem restrict_crossed_lower (data : Theorem63TrialData Z V)
    (F : Submodule ℂ H) (hFZ : F ≤ Z) [F.HasOrthogonalProjection] {c : ℝ}
    (hVl : ∀ z : Z, c * ‖Vᗮ.starProjection ((z : Z) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((z : Z) : H),
        Vᗮ.starProjection (data.action z)⟫_ℂ) :
    ∀ f : F, c * ‖Vᗮ.starProjection ((f : F) : H)‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection ((f : F) : H),
        Vᗮ.starProjection ((data.restrict F hFZ).action f)⟫_ℂ := by
  intro f
  have h := hVl (inclCLM hFZ f)
  have hcoe : ((inclCLM hFZ f : Z) : H) = ((f : F) : H) := rfl
  rw [hcoe] at h
  rw [restrict_action_apply]
  exact h

end Theorem63TrialData

end ExactTanTheta
end Experimental
end DavisKahan
end TauCeti
