/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Basic
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Internal.SpectralBounds
import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm
import ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound

/-!
# Ordered and interval/exterior Sylvester estimates

Sharp constant-one operator and rectangular unitarily invariant norm bounds
under ordered or interval/exterior spectral separation.

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

namespace TauCeti

open TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
/-- Sharp operator-norm interval/exterior Sylvester estimate.

The analytic step is the dimension-free polar-absorption theorem in
`SylvesterBound`.  Finite dimensionality is used only to turn the interval and
exterior eigenvalue hypotheses into a strip norm bound for the inner operator
and a coercive bound for the modulus of the outer operator. -/
theorem opNorm_sylvester_le_of_intervalGap
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * ‖X.toContinuousLinearMap‖ ≤ ‖C.toContinuousLinearMap‖ := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hX0 : X = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    rw [hX0]
    simp
  rcases subsingleton_or_nontrivial F with _ | _
  · have hX0 : X = 0 := by
      ext x
      exact Subsingleton.elim _ _
    rw [hX0]
    simp
  letI : NeZero (Module.finrank 𝕜 E) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  letI : NeZero (Module.finrank 𝕜 F) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  let j₀ : Fin (Module.finrank 𝕜 E) := ⟨0, Module.finrank_pos⟩
  have hj₀ := hgap.1 (eigenvalue_mem_restrictedSpectrum_top hB j₀)
  have hab : a ≤ b := hj₀.1.trans hj₀.2
  let m : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  let S : F →ₗ[𝕜] F := A - (m : 𝕜) • LinearMap.id
  let T : E →ₗ[𝕜] E := B - (m : 𝕜) • LinearMap.id
  let H : F →ₗ[𝕜] F := TauCeti.abs S
  let U : F ≃ₗᵢ[𝕜] F := choosePolarUnitary S
  let Z : E →ₗ[𝕜] F := U.symm.toLinearMap ∘ₗ X
  let Y : E →ₗ[𝕜] F := U.symm.toLinearMap ∘ₗ C
  have hr : 0 ≤ r := by simp only [r]; linarith
  have hTnorm : ‖T.toContinuousLinearMap‖ ≤ r := by
    simpa [T, m, r] using opNorm_shift_le_of_spectrumIn_Icc hB hab hgap.1
  have hSlower : ∀ y, (r + δ) * ‖y‖ ≤ ‖S y‖ := by
    simpa [S, m, r] using
      norm_shift_lower_of_spectrumOutside hA hab hδ hgap.2
  have hHsym : H.IsSymmetric := (TauCeti.isPositive_abs S).isSymmetric
  have hHeig : ∀ i : Fin (Module.finrank 𝕜 F),
      r + δ ≤ hHsym.eigenvalues rfl i := by
    intro i
    have hi : (r + δ) * ‖hHsym.eigenvectorBasis rfl i‖ ≤
        ‖H (hHsym.eigenvectorBasis rfl i)‖ := by
      change (r + δ) * ‖hHsym.eigenvectorBasis rfl i‖ ≤
        ‖TauCeti.abs S (hHsym.eigenvectorBasis rfl i)‖
      rw [TauCeti.norm_abs_apply]
      exact hSlower (hHsym.eigenvectorBasis rfl i)
    have hnonneg := (TauCeti.isPositive_abs S).nonneg_eigenvalues rfl i
    rw [hHsym.apply_eigenvectorBasis rfl i, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg hnonneg,
      (hHsym.eigenvectorBasis rfl).orthonormal.norm_eq_one, mul_one, mul_one] at hi
    exact hi
  have hHform : ∀ y, (r + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪H y, y⟫_𝕜 :=
    le_re_inner_of_le_eigenvalues hHsym hHeig
  have hShift : S ∘ₗ X - X ∘ₗ T = C := by
    ext x
    have hx := LinearMap.congr_fun hEq x
    simp only [S, T, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply] at hx
    rw [← hx]
    module
  have hPolar : H ∘ₗ X - Z ∘ₗ T = Y := by
    ext x
    have hx := LinearMap.congr_fun hShift x
    have hx' : U.symm (S (X x)) - U.symm (X (T x)) = U.symm (C x) := by
      calc
        U.symm (S (X x)) - U.symm (X (T x)) =
            U.symm (S (X x) - X (T x)) := (map_sub U.symm _ _).symm
        _ = U.symm (C x) := congrArg U.symm hx
    have hSX : U.symm (S (X x)) = H (X x) := by
      have hp := LinearMap.congr_fun (polar_decomposition_choosePolarUnitary S) (X x)
      change S (X x) = U (H (X x)) at hp
      rw [hp, U.symm_apply_apply]
    change H (X x) - U.symm (X (T x)) = U.symm (C x)
    rwa [← hSX]
  have hZnorm : ‖Z.toContinuousLinearMap‖ = ‖X.toContinuousLinearMap‖ := by
    apply le_antisymm
    · refine Z.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _) fun x => ?_
      change ‖U.symm (X x)‖ ≤ ‖X.toContinuousLinearMap‖ * ‖x‖
      rw [U.symm.norm_map]
      exact X.toContinuousLinearMap.le_opNorm x
    · refine X.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _) fun x => ?_
      change ‖X x‖ ≤ ‖Z.toContinuousLinearMap‖ * ‖x‖
      rw [← U.symm.norm_map (X x)]
      exact Z.toContinuousLinearMap.le_opNorm x
  have hYnorm : ‖Y.toContinuousLinearMap‖ = ‖C.toContinuousLinearMap‖ := by
    apply le_antisymm
    · refine Y.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _) fun x => ?_
      change ‖U.symm (C x)‖ ≤ ‖C.toContinuousLinearMap‖ * ‖x‖
      rw [U.symm.norm_map]
      exact C.toContinuousLinearMap.le_opNorm x
    · refine C.toContinuousLinearMap.opNorm_le_bound (norm_nonneg _) fun x => ?_
      change ‖C x‖ ≤ ‖Y.toContinuousLinearMap‖ * ‖x‖
      rw [← U.symm.norm_map (C x)]
      exact Y.toContinuousLinearMap.le_opNorm x
  have hPolar' : H.toContinuousLinearMap ∘L X.toContinuousLinearMap -
      Z.toContinuousLinearMap ∘L T.toContinuousLinearMap = Y.toContinuousLinearMap := by
    ext x
    simpa [ContinuousLinearMap.comp_apply] using LinearMap.congr_fun hPolar x
  have hbound := ContinuousLinearMap.gap_mul_opNorm_le_of_comp_sub_comp_eq
    (fun x y => hHsym x y) hr hδ hHform hTnorm
    hZnorm hPolar'
  rwa [hYnorm] at hbound

private theorem uiNorm_sylvester_le_of_form_bounds_aux
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
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
    exact N.add_le _ _
  have hsmul : ∀ (a : 𝕜) (f : E →L[𝕜] F), N' (a • f) = ‖a‖ * N' f := by
    intro a f
    simp only [N', ContinuousLinearMap.toLinearMap_smul]
    exact N.smul_eq _ _
  have hidealL : ∀ D : F →L[𝕜] F, ∀ T : E →L[𝕜] F,
      N' (D ∘L T) ≤ ‖D‖ * N' T := by
    intro D T
    change N (D.toLinearMap ∘ₗ T.toLinearMap) ≤ ‖D‖ * N T.toLinearMap
    have h := N.comp_le_opNorm_mul D.toLinearMap T.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by
      ext x
      rfl
    rwa [hD] at h
  have hidealR : ∀ T : E →L[𝕜] F, ∀ D : E →L[𝕜] E,
      N' (T ∘L D) ≤ N' T * ‖D‖ := by
    intro T D
    change N (T.toLinearMap ∘ₗ D.toLinearMap) ≤ N T.toLinearMap * ‖D‖
    have h := N.comp_le_mul_opNorm T.toLinearMap D.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by
      ext x
      rfl
    rwa [hD] at h
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
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
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
    simp [hX0, hC0, N.apply_zero]
  rcases subsingleton_or_nontrivial F with _ | _
  · have hX0 : X = 0 := by
      ext x
      exact Subsingleton.elim _ _
    have hC0 : C = 0 := by
      ext x
      exact Subsingleton.elim _ _
    simp [hX0, hC0, N.apply_zero]
  letI : NeZero (Module.finrank 𝕜 E) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
  letI : NeZero (Module.finrank 𝕜 F) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
  rcases hgap with hBA | hAB
  · let j₀ : Fin (Module.finrank 𝕜 E) := ⟨0, Module.finrank_pos⟩
    let c : ℝ := hB.eigenvalues rfl j₀
    have hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 :=
      re_inner_le_of_eigenvalues_le hB (fun j =>
        hB.eigenvalues_antitone rfl (Fin.zero_le j))
    have hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜 :=
      le_re_inner_of_le_eigenvalues hA fun i =>
        hBA c (hA.eigenvalues rfl i)
          (eigenvalue_mem_restrictedSpectrum_top hB j₀)
          (eigenvalue_mem_restrictedSpectrum_top hA i)
    exact uiNorm_sylvester_le_of_form_bounds_aux N hA hB hδ hAform hBform hEq
  · let i₀ : Fin (Module.finrank 𝕜 F) := ⟨0, Module.finrank_pos⟩
    let c : ℝ := hA.eigenvalues rfl i₀
    have hAform : ∀ y, RCLike.re ⟪A y, y⟫_𝕜 ≤ c * ‖y‖ ^ 2 :=
      re_inner_le_of_eigenvalues_le hA (fun i =>
        hA.eigenvalues_antitone rfl (Fin.zero_le i))
    have hBform : ∀ x, (c + δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜 :=
      le_re_inner_of_le_eigenvalues hB fun j =>
        hAB c (hB.eigenvalues rfl j)
          (eigenvalue_mem_restrictedSpectrum_top hA i₀)
          (eigenvalue_mem_restrictedSpectrum_top hB j)
    have hadj : X.adjoint ∘ₗ A - B ∘ₗ X.adjoint = C.adjoint := by
      simpa only [map_sub, LinearMap.adjoint_comp, hA.adjoint_eq, hB.adjoint_eq] using
        congrArg (fun T : E →ₗ[𝕜] F => T.adjoint) hEq
    have hEqAdj : B ∘ₗ X.adjoint - X.adjoint ∘ₗ A = -C.adjoint := by
      calc
        B ∘ₗ X.adjoint - X.adjoint ∘ₗ A
            = -(X.adjoint ∘ₗ A - B ∘ₗ X.adjoint) := by abel
        _ = -C.adjoint := congrArg Neg.neg hadj
    have hbound := uiNorm_sylvester_le_of_form_bounds_aux
      (RectangularUnitarilyInvariantNorm.adjointTransport N)
      hB hA hδ hBform hAform hEqAdj
    have hXnorm :
        (RectangularUnitarilyInvariantNorm.adjointTransport N) X.adjoint = N X := by
      change N X.adjoint.adjoint = N X
      rw [LinearMap.adjoint_adjoint]
    have hCnorm :
        (RectangularUnitarilyInvariantNorm.adjointTransport N) (-C.adjoint) = N C := by
      change N ((-C.adjoint).adjoint) = N C
      rw [map_neg, LinearMap.adjoint_adjoint, N.apply_neg]
    rw [hXnorm, hCnorm] at hbound
    exact hbound

/-- Sharp constant-one interval/exterior Sylvester estimate in every
rectangular UI norm.

The proof follows the dimension-free polar-absorption route used for the
operator norm.  Shift the interval to its midpoint, replace the exterior
operator by its absolute value, and absorb the polar unitary into the unknown
and right-hand side.  The abstract rectangular seminorm theorem in
`SylvesterBound` applies because every rectangular UI norm is subadditive,
absolutely homogeneous, and satisfies both operator-ideal inequalities.
Unitary invariance identifies the rotated norms with the original ones.
-/
theorem uiNorm_sylvester_le_of_intervalGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  rcases subsingleton_or_nontrivial E with _ | _
  · have hX0 : X = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst x
      simp
    rw [hX0, N.apply_zero, mul_zero]
    exact N.nonneg C
  rcases subsingleton_or_nontrivial F with _ | _
  · have hX0 : X = 0 := by
      ext x
      exact Subsingleton.elim _ _
    rw [hX0, N.apply_zero, mul_zero]
    exact N.nonneg C
  letI : NeZero (Module.finrank 𝕜 E) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  letI : NeZero (Module.finrank 𝕜 F) :=
    ⟨Nat.ne_of_gt Module.finrank_pos⟩
  let j₀ : Fin (Module.finrank 𝕜 E) := ⟨0, Module.finrank_pos⟩
  have hj₀ := hgap.1 (eigenvalue_mem_restrictedSpectrum_top hB j₀)
  have hab : a ≤ b := hj₀.1.trans hj₀.2
  let m : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  let S : F →ₗ[𝕜] F := A - (m : 𝕜) • LinearMap.id
  let T : E →ₗ[𝕜] E := B - (m : 𝕜) • LinearMap.id
  let H : F →ₗ[𝕜] F := TauCeti.abs S
  let U : F ≃ₗᵢ[𝕜] F := choosePolarUnitary S
  let Z : E →ₗ[𝕜] F := U.symm.toLinearMap ∘ₗ X
  let Y : E →ₗ[𝕜] F := U.symm.toLinearMap ∘ₗ C
  have hr : 0 ≤ r := by simp only [r]; linarith
  have hTnorm : ‖T.toContinuousLinearMap‖ ≤ r := by
    simpa [T, m, r] using opNorm_shift_le_of_spectrumIn_Icc hB hab hgap.1
  have hSlower : ∀ y, (r + δ) * ‖y‖ ≤ ‖S y‖ := by
    simpa [S, m, r] using
      norm_shift_lower_of_spectrumOutside hA hab hδ hgap.2
  have hHsym : H.IsSymmetric := (TauCeti.isPositive_abs S).isSymmetric
  have hHeig : ∀ i : Fin (Module.finrank 𝕜 F),
      r + δ ≤ hHsym.eigenvalues rfl i := by
    intro i
    have hi : (r + δ) * ‖hHsym.eigenvectorBasis rfl i‖ ≤
        ‖H (hHsym.eigenvectorBasis rfl i)‖ := by
      change (r + δ) * ‖hHsym.eigenvectorBasis rfl i‖ ≤
        ‖TauCeti.abs S (hHsym.eigenvectorBasis rfl i)‖
      rw [TauCeti.norm_abs_apply]
      exact hSlower (hHsym.eigenvectorBasis rfl i)
    have hnonneg := (TauCeti.isPositive_abs S).nonneg_eigenvalues rfl i
    rw [hHsym.apply_eigenvectorBasis rfl i, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg hnonneg,
      (hHsym.eigenvectorBasis rfl).orthonormal.norm_eq_one, mul_one, mul_one] at hi
    exact hi
  have hHform : ∀ y, (r + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪H y, y⟫_𝕜 :=
    le_re_inner_of_le_eigenvalues hHsym hHeig
  have hShift : S ∘ₗ X - X ∘ₗ T = C := by
    ext x
    have hx := LinearMap.congr_fun hEq x
    simp only [S, T, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply] at hx
    rw [← hx]
    module
  have hPolar : H ∘ₗ X - Z ∘ₗ T = Y := by
    ext x
    have hx := LinearMap.congr_fun hShift x
    have hx' : U.symm (S (X x)) - U.symm (X (T x)) = U.symm (C x) := by
      calc
        U.symm (S (X x)) - U.symm (X (T x)) =
            U.symm (S (X x) - X (T x)) := (map_sub U.symm _ _).symm
        _ = U.symm (C x) := congrArg U.symm hx
    have hSX : U.symm (S (X x)) = H (X x) := by
      have hp := LinearMap.congr_fun (polar_decomposition_choosePolarUnitary S) (X x)
      change S (X x) = U (H (X x)) at hp
      rw [hp, U.symm_apply_apply]
    change H (X x) - U.symm (X (T x)) = U.symm (C x)
    rwa [← hSX]
  have hZnorm : N Z = N X := by
    change N (U.symm.toLinearMap ∘ₗ X) = N X
    have h := N.invariant U.symm (LinearIsometryEquiv.refl 𝕜 E) X
    have hcomp : U.symm.toLinearMap ∘ₗ X ∘ₗ
        (LinearIsometryEquiv.refl 𝕜 E).toLinearMap =
        U.symm.toLinearMap ∘ₗ X := by
      ext x
      rfl
    rwa [hcomp] at h
  have hYnorm : N Y = N C := by
    change N (U.symm.toLinearMap ∘ₗ C) = N C
    have h := N.invariant U.symm (LinearIsometryEquiv.refl 𝕜 E) C
    have hcomp : U.symm.toLinearMap ∘ₗ C ∘ₗ
        (LinearIsometryEquiv.refl 𝕜 E).toLinearMap =
        U.symm.toLinearMap ∘ₗ C := by
      ext x
      rfl
    rwa [hcomp] at h
  let H' : F →L[𝕜] F := H.toContinuousLinearMap
  let T' : E →L[𝕜] E := T.toContinuousLinearMap
  let X' : E →L[𝕜] F := X.toContinuousLinearMap
  let Z' : E →L[𝕜] F := Z.toContinuousLinearMap
  let Y' : E →L[𝕜] F := Y.toContinuousLinearMap
  let N' : (E →L[𝕜] F) → ℝ := fun Q => N Q.toLinearMap
  have hadd : ∀ f g : E →L[𝕜] F, N' (f + g) ≤ N' f + N' g := by
    intro f g
    simp only [N', ContinuousLinearMap.toLinearMap_add]
    exact N.add_le _ _
  have hsmul : ∀ (q : 𝕜) (f : E →L[𝕜] F), N' (q • f) = ‖q‖ * N' f := by
    intro q f
    simp only [N', ContinuousLinearMap.toLinearMap_smul]
    exact N.smul_eq _ _
  have hidealL : ∀ D : F →L[𝕜] F, ∀ Q : E →L[𝕜] F,
      N' (D ∘L Q) ≤ ‖D‖ * N' Q := by
    intro D Q
    change N (D.toLinearMap ∘ₗ Q.toLinearMap) ≤ ‖D‖ * N Q.toLinearMap
    have h := N.comp_le_opNorm_mul D.toLinearMap Q.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by ext x; rfl
    rwa [hD] at h
  have hidealR : ∀ Q : E →L[𝕜] F, ∀ D : E →L[𝕜] E,
      N' (Q ∘L D) ≤ N' Q * ‖D‖ := by
    intro Q D
    change N (Q.toLinearMap ∘ₗ D.toLinearMap) ≤ N Q.toLinearMap * ‖D‖
    have h := N.comp_le_mul_opNorm Q.toLinearMap D.toLinearMap
    have hD : D.toLinearMap.toContinuousLinearMap = D := by ext x; rfl
    rwa [hD] at h
  have hPolar' : H' ∘L X' - Z' ∘L T' = Y' := by
    ext x
    simpa [H', T', X', Z', Y', ContinuousLinearMap.comp_apply] using
      LinearMap.congr_fun hPolar x
  have hZX' : N' Z' = N' X' := by
    simpa [N', X', Z'] using hZnorm
  have hbound := ContinuousLinearMap.gap_mul_le_of_comp_sub_comp_eq_rectangular
    hadd hsmul hidealL hidealR (fun x y => hHsym x y) hr hδ hHform
    hTnorm hZX' hPolar'
  have hbound' : δ * N X ≤ N Y := by
    simpa [N', X', Y'] using hbound
  rwa [hYnorm] at hbound'

/-- Sharp constant-one interval/exterior Sylvester estimate in either
orientation.

The forward branch is `uiNorm_sylvester_le_of_intervalGap`.  In the reverse
branch, take adjoints, negate the resulting Sylvester equation, and transport
the rectangular UI norm across adjoint. -/
theorem uiNorm_sylvester_le_of_unorderedIntervalGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : UnorderedIntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  rcases hgap with hforward | hreverse
  · exact uiNorm_sylvester_le_of_intervalGap N hA hB hδ hforward hEq
  · have hadj : X.adjoint ∘ₗ A - B ∘ₗ X.adjoint = C.adjoint := by
      simpa only [map_sub, LinearMap.adjoint_comp, hA.adjoint_eq, hB.adjoint_eq] using
        congrArg (fun T : E →ₗ[𝕜] F => T.adjoint) hEq
    have hEqAdj : B ∘ₗ X.adjoint - X.adjoint ∘ₗ A = -C.adjoint := by
      calc
        B ∘ₗ X.adjoint - X.adjoint ∘ₗ A =
            -(X.adjoint ∘ₗ A - B ∘ₗ X.adjoint) := by abel
        _ = -C.adjoint := congrArg Neg.neg hadj
    have hbound := uiNorm_sylvester_le_of_intervalGap
      (RectangularUnitarilyInvariantNorm.adjointTransport N)
      hB hA hδ hreverse hEqAdj
    have hXnorm :
        (RectangularUnitarilyInvariantNorm.adjointTransport N) X.adjoint = N X := by
      change N X.adjoint.adjoint = N X
      rw [LinearMap.adjoint_adjoint]
    have hCnorm :
        (RectangularUnitarilyInvariantNorm.adjointTransport N) (-C.adjoint) = N C := by
      change N ((-C.adjoint).adjoint) = N C
      rw [map_neg, LinearMap.adjoint_adjoint, N.apply_neg]
    rw [hXnorm, hCnorm] at hbound
    exact hbound

/-- Ky Fan specialization of the sharp interval/exterior Sylvester
estimate.  The hard work is already contained in
`uiNorm_sylvester_le_of_intervalGap`; evaluating the concrete Ky Fan norm gives
this singular-value prefix-sum form directly.
-/
theorem kyFan_sylvester_le_of_intervalGap
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ) (hgap : IntervalSylvesterGap A B a b δ)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) (k : ℕ) :
    δ * RectangularUnitarilyInvariantNorm.rectangularKyFanSum k X ≤
      RectangularUnitarilyInvariantNorm.rectangularKyFanSum k C := by
  have h := uiNorm_sylvester_le_of_intervalGap
    (RectangularUnitarilyInvariantNorm.kyFan k) hA hB hδ hgap hEq
  simpa only [RectangularUnitarilyInvariantNorm.kyFan_apply] using h

/-- Ordered positivity/coercivity form used by the existing integral-free
proof.
-/
theorem uiNorm_sylvester_le_of_form_bounds
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →ₗ[𝕜] F} {B : E →ₗ[𝕜] E} {X C : E →ₗ[𝕜] F}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) {c δ : ℝ} (hδ : 0 < δ)
    (hAform : ∀ y, (c + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A y, y⟫_𝕜)
    (hBform : ∀ x, RCLike.re ⟪B x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2)
    (hEq : A ∘ₗ X - X ∘ₗ B = C) :
    δ * N X ≤ N C := by
  exact uiNorm_sylvester_le_of_form_bounds_aux N hA hB hδ hAform hBform hEq

end DavisKahanTheory
end TauCeti
