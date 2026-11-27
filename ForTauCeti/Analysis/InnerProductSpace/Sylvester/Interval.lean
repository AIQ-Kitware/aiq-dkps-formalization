/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Basic
public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound

/-!
# Ordered Sylvester estimates

Sharp constant-one rectangular unitarily invariant seminorm bounds under
ordered spectral separation. The interval/exterior bounds are in TauCeti’s
`UnitarilyInvariantSeminorm.Sylvester.Basic`.

## Sources

The interval and exterior forms of the Sylvester estimate follow
Bhatia--Davis--McIntosh
(`prose/distilled_literature/BhatiaDavisMcIntosh1983_spectral_subspaces_sylvester.tex`);
the sharp `π / 2` constant and its Fourier route are distilled in
`prose/distilled_literature/AlbeverioMakarovMotovilov2001_sylvester_fourier_pi_over_two.tex`.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Sylvester/Interval.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/

public section

namespace TauCeti

open TauCeti

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-- **The adjoint of a Sylvester equation, in the sign the norm bounds want.**

From `A X − X B = C` with `A`, `B` symmetric, taking adjoints gives
`X⋆ A − B X⋆ = C⋆`; negating puts it in the orientation the interval-gap
estimate uses. -/
private theorem sylvester_adjoint_neg {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E}
    {X C : E →ₗ[𝕜] F} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    B ∘ₗ X.adjoint - X.adjoint ∘ₗ A = -C.adjoint := by
  have hadj : X.adjoint ∘ₗ A - B ∘ₗ X.adjoint = C.adjoint := by
    simpa only [map_sub, LinearMap.adjoint_comp, hA.adjoint_eq, hB.adjoint_eq] using
      congrArg (fun T : E →ₗ[𝕜] F => T.adjoint) hEq
  calc
    B ∘ₗ X.adjoint - X.adjoint ∘ₗ A
        = -(X.adjoint ∘ₗ A - B ∘ₗ X.adjoint) := by abel
    _ = -C.adjoint := congrArg Neg.neg hadj

private theorem uiNorm_sylvester_le_of_form_bounds_aux
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c δ : ℝ} (hδ : 0 < δ)
    (hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    (hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  let A' : F →L[𝕜] F := A.toContinuousLinearMap
  let B' : E →L[𝕜] E := B.toContinuousLinearMap
  let X' : E →L[𝕜] F := X.toContinuousLinearMap
  let C' : E →L[𝕜] F := C.toContinuousLinearMap
  let N' : (E →L[𝕜] F) → ℝ := fun T => N T.toLinearMap
  have hA' : A'.IsSymmetric := fun x y => hA x y
  have hB' : B'.IsSymmetric := fun x y => hB x y
  have hadd : ∀ f g : E →L[𝕜] F, N' (f + g) ≤ N' f + N' g := by
    intro f g
    simp only [N', ContinuousLinearMap.toLinearMap_add]
    exact map_add_le_add N _ _
  have hsmul : ∀ (a : 𝕜) (f : E →L[𝕜] F), N' (a • f) = ‖a‖ * N' f := by
    intro a f
    simp only [N', ContinuousLinearMap.toLinearMap_smul]
    exact map_smul_eq_mul N _ _
  have hidealL : ∀ D : F →L[𝕜] F, ∀ T : E →L[𝕜] F,
      N' (D ∘L T) ≤ ‖D‖ * N' T := by
    intro D T
    -- `N'` is `N` precomposed with `toLinearMap`. The goal is stated over `∘L` on bundled
    -- maps and `N`'s ideal API over `∘ₗ` on the underlying ones; the two are the same term,
    -- so this `change` is the entire translation between the two spellings.
    change N (D.toLinearMap ∘ₗ T.toLinearMap) ≤ ‖D‖ * N T.toLinearMap
    have h := N.map_comp_le_left D.toLinearMap T.toLinearMap
      (c := ‖D.toLinearMap.toContinuousLinearMap‖)
      (fun y => D.toLinearMap.toContinuousLinearMap.le_opNorm y)
    have hD : D.toLinearMap.toContinuousLinearMap = D := by
      ext x
      rfl
    rwa [hD] at h
  have hidealR : ∀ T : E →L[𝕜] F, ∀ D : E →L[𝕜] E,
      N' (T ∘L D) ≤ N' T * ‖D‖ := by
    intro T D
    -- As `hidealL`: the same `∘L` / `∘ₗ` translation, on the other side.
    change N (T.toLinearMap ∘ₗ D.toLinearMap) ≤ N T.toLinearMap * ‖D‖
    have h := N.map_comp_le_right T.toLinearMap D.toLinearMap
      (c := ‖D.toLinearMap.toContinuousLinearMap‖)
      (fun x => D.toLinearMap.toContinuousLinearMap.le_opNorm x)
    have hD : D.toLinearMap.toContinuousLinearMap = D := by
      ext x
      rfl
    simpa only [hD, mul_comm] using h
  have hEq' : A' ∘L X' - X' ∘L B' = C' := by
    ext x
    simpa [A', B', X', C', ContinuousLinearMap.comp_apply] using
      LinearMap.congr_fun hEq x
  have hbound : N' X' ≤ N' C' / δ :=
    TauCeti.ContinuousLinearMap.le_div_of_comp_sub_comp_eq_rectangular
      hadd hsmul hidealL hidealR hA' hB' hδ hAform hBform hEq'
  have hbound' : N X ≤ N C / δ := by
    simpa [N', X', C'] using hbound
  rw [le_div_iff₀ hδ] at hbound'
  simpa [mul_comm] using hbound'


/-- Sharp constant-one ordered Sylvester estimate in every rectangular UI
norm.

The proof first extends the integral-free absorption argument from square to
rectangular operator seminorms.  In either ordered orientation, the largest
eigenvalue of the lower block supplies a cut `c`; eigenbasis expansion then
gives the global upper and lower quadratic-form bounds.  The reverse
orientation is reduced to the first by taking adjoints and transporting the
rectangular UI norm.
-/
theorem uiNorm_sylvester_le_of_orderedGap
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedSylvesterGap A B δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hX0 : X = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    have hC0 : C = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    simp [hX0, hC0]
  rcases subsingleton_or_nontrivial F with _ | _
  · have hX0 : X = 0 := by
      ext x
      exact Subsingleton.elim _ _
    have hC0 : C = 0 := by
      ext x
      exact Subsingleton.elim _ _
    simp [hX0, hC0]
  let : NeZero (Module.finrank 𝕜 E) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
  let : NeZero (Module.finrank 𝕜 F) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
  rcases hgap with hBA | hAB
  · let j₀ : Fin (Module.finrank 𝕜 E) := ⟨0, Module.finrank_pos⟩
    let c : ℝ := hB.eigenvalues rfl j₀
    have hc : c ∈ Module.End.restrictedPointSpectrum B ⊤ := by
      rw [Module.End.restrictedPointSpectrum_top]
      exact hB.hasEigenvalue_eigenvalues rfl j₀
    have hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
      fun _ => hB.re_inner_apply_self_le_of_mem_spanIndices rfl (s := Set.univ)
        (fun j _ => hB.eigenvalues_antitone rfl (Fin.zero_le j))
        (by simp [OrthonormalBasis.mem_spanIndices_iff])
    have hAspec : Module.End.PointSpectrumIn A ⊤ (Set.Ici (c + δ)) :=
      Module.End.pointSpectrumIn_iff_restrictedPointSpectrum_subset.mpr
        (fun _ hμ => hBA.add_le hc hμ)
    have hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜 :=
      fun _ => hA.le_re_inner_apply_self_of_pointSpectrumIn
        (fun _ _ => Submodule.mem_top) hAspec Submodule.mem_top
    exact uiNorm_sylvester_le_of_form_bounds_aux N hA hB hδ hAform hBform hEq
  · let i₀ : Fin (Module.finrank 𝕜 F) := ⟨0, Module.finrank_pos⟩
    let c : ℝ := hA.eigenvalues rfl i₀
    have hc : c ∈ Module.End.restrictedPointSpectrum A ⊤ := by
      rw [Module.End.restrictedPointSpectrum_top]
      exact hA.hasEigenvalue_eigenvalues rfl i₀
    have hAform : ∀ y, RCLike.re ⟪A y, y⟫_𝕜 ≤ c * ‖y‖ ^ 2 :=
      fun _ => hA.re_inner_apply_self_le_of_mem_spanIndices rfl (s := Set.univ)
        (fun i _ => hA.eigenvalues_antitone rfl (Fin.zero_le i))
        (by simp [OrthonormalBasis.mem_spanIndices_iff])
    have hBspec : Module.End.PointSpectrumIn B ⊤ (Set.Ici (c + δ)) :=
      Module.End.pointSpectrumIn_iff_restrictedPointSpectrum_subset.mpr
        (fun _ hμ => hAB.add_le hc hμ)
    have hBform : ∀ x, (c + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜 :=
      fun _ => hB.le_re_inner_apply_self_of_pointSpectrumIn
        (fun _ _ => Submodule.mem_top) hBspec Submodule.mem_top
    have hEqAdj : B ∘ₗ X.adjoint - X.adjoint ∘ₗ A = -C.adjoint :=
      sylvester_adjoint_neg hA hB hEq
    have hbound := uiNorm_sylvester_le_of_form_bounds_aux
      N.compAdjoint
      hB hA hδ hBform hAform hEqAdj
    simpa only [UnitarilyInvariantSeminorm.compAdjoint_apply,
      LinearMap.adjoint_adjoint, map_neg_eq_map] using hbound

/-- Ordered positivity/coercivity form used by the existing integral-free
proof.
-/
theorem uiNorm_sylvester_le_of_form_bounds
    (N : UnitarilyInvariantSeminorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c δ : ℝ} (hδ : 0 < δ)
    (hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    (hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  exact uiNorm_sylvester_le_of_form_bounds_aux N hA hB hδ hAform hBform hEq

end TauCeti
