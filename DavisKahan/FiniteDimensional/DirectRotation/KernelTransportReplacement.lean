/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.KernelCostSplitting
import DavisKahan.Geometry.Polar.CanonicalSymmetry

/-!
# Replacing the actual right-angle action of a transporter

Every self-adjoint unitary on the cosine kernel which exchanges the source
reflection sectors extends to a feasible ambient transporter, while keeping
any given cosine-preserving transporter on the positive-cosine complement.
The extension and cosine commutation are conclusions, not hypotheses.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- An arbitrary reflecting action on the actual right-angle kernel can
replace that of a cosine-preserving transporter without changing its action
on the orthogonal complement. This applies over either scalar field. -/
theorem exists_transport_replacing_cosine_kernel
    (K L : Submodule 𝕜 E) (T : E ≃ₗᵢ[𝕜] E) (hT : K.map T.toLinearMap = L)
    (hTC : Commute (T : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L)) :
    let N := (Proposition35.section3CosAngleOperator K L).ker
    ∀ S : N ≃ₗᵢ[𝕜] N, IsSelfAdjoint (S : N →L[𝕜] N) →
      (∀ x : N, (S ⟨K.reflection x,
        Proposition35.reflection_mem_cosine_kernel K L x x.property⟩ : E) =
          -K.reflection (S x)) →
      ∃ W : E ≃ₗᵢ[𝕜] E,
        K.map W.toLinearMap = L ∧
        Commute (W : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L) ∧
        (∀ x : E, Proposition35.section3CosAngleOperator K L x = 0 →
          W x = star (W : E →L[𝕜] E) x) ∧
        (∀ x : N, W x = (S x : E)) ∧
        (∀ x ∈ Nᗮ, W x = T x) := by
  dsimp only
  intro S hS hanti
  let C := Proposition35.section3CosAngleOperator K L
  let N := C.ker
  have hinv : ∀ x ∈ N, T x ∈ N := by
    intro x hx
    change C (T x) = 0
    have h := DFunLike.congr_fun hTC.eq x
    change T (C x) = C (T x) at h
    rw [show C x = 0 from hx, map_zero] at h
    exact h.symm
  obtain ⟨_, _, _, hred⟩ := T.exists_restriction_of_finite_invariant N hinv
  have hinvp : ∀ x ∈ Nᗮ, T x ∈ Nᗮ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem T.toLinearMap).mp
      hred.orthogonal_mem_invtSubmodule
  obtain ⟨Tpos, hTpos, _, _⟩ := T.exists_restriction_of_finite_invariant Nᗮ hinvp
  obtain ⟨W, hW₀, hWpos'⟩ := N.exists_unitary_orthogonal_sum S Tpos
  have hWpos (x : Nᗮ) : W x = T x := (hWpos' x).trans (hTpos x)
  have hJinv : ∀ x ∈ N, K.reflection x ∈ N := by
    intro x hx
    exact Proposition35.reflection_mem_cosine_kernel K L x hx
  obtain ⟨_, _, _, hJred⟩ :=
    K.reflection.exists_restriction_of_finite_invariant N hJinv
  have hJinvp : ∀ x ∈ Nᗮ, K.reflection x ∈ Nᗮ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem K.reflection.toLinearMap).mp
      hJred.orthogonal_mem_invtSubmodule
  have hWJ₀ (x : N) : W (K.reflection x) = L.reflection (W x) := by
    calc
      W (K.reflection x) = (S ⟨K.reflection x, hJinv x x.property⟩ : E) :=
        hW₀ ⟨K.reflection x, hJinv x x.property⟩
      _ = -K.reflection (S x) := hanti x
      _ = L.reflection (S x) :=
        (Proposition35.reflection_eq_neg_on_cosine_kernel K L (S x) (S x).property).symm
      _ = L.reflection (W x) := congrArg L.reflection (hW₀ x).symm
  have hWJpos (x : Nᗮ) : W (K.reflection x) = L.reflection (W x) := by
    calc
      W (K.reflection x) = T (K.reflection x) := hWpos ⟨_, hJinvp x x.property⟩
      _ = L.reflection (T x) := (K.map_eq_iff_intertwines_reflection L T).mp hT x
      _ = L.reflection (W x) := congrArg L.reflection (hWpos x).symm
  let d := N.orthogonalDecomposition
  have hWmap : K.map W.toLinearMap = L := by
    apply (K.map_eq_iff_intertwines_reflection L W).mpr
    intro x
    obtain ⟨y, rfl⟩ := d.symm.surjective x
    change W (K.reflection ((y.fst : E) + (y.snd : E))) =
      L.reflection (W ((y.fst : E) + (y.snd : E)))
    rw [map_add, map_add, map_add, map_add, hWJ₀, hWJpos]
  have hCself : IsSelfAdjoint C := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
    (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint
  have hCinvp (x : E) (hx : x ∈ Nᗮ) : C x ∈ Nᗮ := by
    intro y hy
    have h := hCself.isSymmetric y x
    change inner 𝕜 (C y) x = inner 𝕜 y (C x) at h
    rw [show C y = 0 from hy, inner_zero_left] at h
    exact h.symm
  have hWC₀ (x : N) : W (C x) = C (W x) := by
    rw [show C (x : E) = 0 from x.property, map_zero, hW₀]
    exact (S x).property.symm
  have hWCpos (x : Nᗮ) : W (C x) = C (W x) := by
    rw [show W (C x) = T (C x) from hWpos ⟨_, hCinvp x x.property⟩, hWpos]
    exact DFunLike.congr_fun hTC.eq (x : E)
  have hWC : Commute (W : E →L[𝕜] E) C := by
    ext x
    obtain ⟨y, rfl⟩ := d.symm.surjective x
    change W (C ((y.fst : E) + (y.snd : E))) =
      C (W ((y.fst : E) + (y.snd : E)))
    rw [map_add, map_add, map_add, map_add, hWC₀, hWCpos]
  have hSsymm : S.symm = S := by
    ext x
    have h := DFunLike.congr_fun hS.star_eq x
    rw [show star (S : N →L[𝕜] N) = (S.symm : N →L[𝕜] N) from
      S.adjoint_eq_symm] at h
    change S.symm x = S x at h
    exact congrArg (fun z : N => (z : E)) h
  have hWinv (x : N) : W.symm x = (S.symm x : E) := by
    apply W.injective
    rw [W.apply_symm_apply, hW₀, S.apply_symm_apply]
  have hWself (x : E) (hx : C x = 0) : W x = star (W : E →L[𝕜] E) x := by
    rw [show star (W : E →L[𝕜] E) = (W.symm : E →L[𝕜] E) from W.adjoint_eq_symm]
    change W x = W.symm x
    calc
      W x = (S ⟨x, hx⟩ : E) := hW₀ ⟨x, hx⟩
      _ = (S.symm ⟨x, hx⟩ : E) := by rw [hSsymm]
      _ = W.symm x := (hWinv ⟨x, hx⟩).symm
  exact ⟨W, hWmap, hWC, hWself, hW₀, fun x hx => hWpos ⟨x, hx⟩⟩

/-- Any unitary identification of the actual crossed defects can replace
the right-angle action of a cosine-preserving transporter. The entire
positive-cosine action is preserved. This is geometric and applies over
either scalar field, without an optimality or reflection assumption on
the input transporter. -/
theorem exists_transport_prescribing_defects
    (K L : Submodule 𝕜 E) (T : E ≃ₗᵢ[𝕜] E) (hT : K.map T.toLinearMap = L)
    (hTC : Commute (T : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L))
    (D : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L) :
    ∃ W : E ≃ₗᵢ[𝕜] E, K.map W.toLinearMap = L ∧
      Commute (W : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L) ∧
      (∀ x : E, Proposition35.section3CosAngleOperator K L x = 0 →
        W x = star (W : E →L[𝕜] E) x) ∧
      (∀ x : halmosSourceDefect K L, W x = (D x : E)) ∧
      (∀ y : halmosTargetDefect K L, W y = (D.symm y : E)) ∧
      (∀ x ∈ (Proposition35.section3CosAngleOperator K L).kerᗮ, W x = T x) := by
  let N := (Proposition35.section3CosAngleOperator K L).ker
  obtain ⟨V, hV, hVself, hVC, hVsource, hVtarget⟩ :=
    exists_selfAdjoint_transport_prescribing_defects K L D
  have hVinv : ∀ x ∈ N, V x ∈ N := by
    intro x hx
    have h := DFunLike.congr_fun hVC.eq x
    change V (Proposition35.section3CosAngleOperator K L x) =
      Proposition35.section3CosAngleOperator K L (V x) at h
    rw [show Proposition35.section3CosAngleOperator K L x = 0 from hx, map_zero] at h
    exact h.symm
  obtain ⟨S, hS, _, _⟩ := V.exists_restriction_of_finite_invariant N hVinv
  have hSself : IsSelfAdjoint (S : N →L[𝕜] N) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change inner 𝕜 (S x : E) (y : E) = inner 𝕜 (x : E) (S y : E)
    rw [hS, hS]
    exact hVself.isSymmetric x y
  have hanti (x : N) : (S ⟨K.reflection x,
      Proposition35.reflection_mem_cosine_kernel K L x x.property⟩ : E) =
        -K.reflection (S x) := by
    rw [hS, hS]
    exact Proposition35.transport_anticommutes_reflection_on_cosine_kernel K L V hV hVC x
      x.property
  obtain ⟨W, hW, hWC, hWself, hWS, hagree⟩ :=
    exists_transport_replacing_cosine_kernel K L T hT hTC S hSself hanti
  have hsource (x : halmosSourceDefect K L) : (x : E) ∈ N := by
    rw [show N = (Proposition35.section3CosAngleOperator K L).ker from rfl,
      Proposition35.ker_section3CosAngleOperator_eq_crossedDefectSum]
    exact Submodule.mem_sup_left x.property
  have htarget (x : halmosTargetDefect K L) : (x : E) ∈ N := by
    rw [show N = (Proposition35.section3CosAngleOperator K L).ker from rfl,
      Proposition35.ker_section3CosAngleOperator_eq_crossedDefectSum]
    exact Submodule.mem_sup_right x.property
  refine ⟨W, hW, hWC, hWself, ?_, ?_, hagree⟩
  · intro x
    exact (hWS ⟨x, hsource x⟩).trans ((hS _).trans (hVsource x))
  · intro x
    exact (hWS ⟨x, htarget x⟩).trans ((hS _).trans (hVtarget x))

end TauCeti.DavisKahan.FiniteDimensional
