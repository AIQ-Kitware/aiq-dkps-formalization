/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm.Basic

/-!
# Ky Fan majorization for rectangular unitarily invariant norms

The engine of the theory: a map whose Ky Fan sums are dominated by another's lies in
the convex hull of the latter's two-sided unitary orbit, and therefore has the smaller
value under *every* rectangular unitarily invariant norm.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm`,
  split out on 2026-07-28 because that file had grown to 2124 lines while Tau Ceti's
  `lean_lib` enforces a hard 1500-line ceiling, and 1000 for a newly added file.
* Extraction class: **split**.  No statement, proof or declaration name changed; only
  `exists_unitary_factorization_of_singularValues_eq` was promoted from `private` to
  public, because the split puts its users in a different module.
* Original authors / copyright: Jon Crall, Claude Fable 5;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

namespace TauCeti
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]

namespace RectangularUnitarilyInvariantNorm

variable (N : RectangularUnitarilyInvariantNorm 𝕜 E F)

/- `Module ℝ (E →ₗ[𝕜] F)` is a *local* instance in `Basic`, so it does not survive the
import.  Re-enable it here; making it global would put a second `Module ℝ` structure on
every `𝕜`-linear map space, which is why it is local in the first place. -/
attribute [local instance] realModuleLinearMap


/-- Extend a unitary action on an isometrically embedded coordinate space to
an ambient unitary. -/
private theorem exists_ambient_unitary_intertwining
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [FiniteDimensional 𝕜 K]
    (ι : H →ₗᵢ[𝕜] K) (U : H ≃ₗᵢ[𝕜] H) :
    ∃ W : K ≃ₗᵢ[𝕜] K,
      W.toLinearMap ∘ₗ ι.toLinearMap =
        ι.toLinearMap ∘ₗ U.toLinearMap := by
  obtain ⟨W, hW⟩ := exists_linearIsometryEquiv_map_eq_of_inner_eq
    (φ := fun x : H => ι x) (ψ := fun x : H => ι (U x)) (by
      intro x y
      rw [ι.inner_map_map, ι.inner_map_map, U.inner_map_map])
  refine ⟨W, ?_⟩
  ext x
  simpa only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] using hW x

/-- Lift an endomorphism of a common coordinate space to a rectangular map by
an isometric codomain embedding and a coisometric domain projection. -/
private noncomputable def coordinateLift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (X : H →ₗ[𝕜] H) : E →ₗ[𝕜] F :=
  ιF.toLinearMap ∘ₗ X ∘ₗ LinearMap.adjoint ιE.toLinearMap

private theorem singularValues_coordinateLift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (X : H →ₗ[𝕜] H) :
    (coordinateLift ιE ιF X).singularValues = X.singularValues := by
  unfold coordinateLift
  calc
    (ιF.toLinearMap ∘ₗ X ∘ₗ LinearMap.adjoint ιE.toLinearMap).singularValues =
        (X ∘ₗ LinearMap.adjoint ιE.toLinearMap).singularValues :=
      singularValues_linearIsometry_comp ιF _
    _ = X.singularValues :=
      singularValues_comp_adjoint_linearIsometry ιE X

/-- Pull a rectangular UI norm back to square operators on a common coordinate
space.  Ambient extensions of the coordinate unitaries prove full square
unitary invariance. -/
private noncomputable def coordinateSquareNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F) :
    UnitarilyInvariantNorm 𝕜 H where
  toFun X := N (coordinateLift ιE ιF X)
  add_le' X Y := by
    have hmap : coordinateLift ιE ιF (X + Y) =
        coordinateLift ιE ιF X + coordinateLift ιE ιF Y := by
      ext x
      simp [coordinateLift, LinearMap.comp_apply]
    rw [hmap]
    exact N.add_le _ _
  smul' a X := by
    have hmap : coordinateLift ιE ιF (a • X) =
        a • coordinateLift ιE ιF X := by
      ext x
      simp [coordinateLift, LinearMap.comp_apply]
    rw [hmap]
    exact N.smul_eq a _
  invariant' U V X := by
    obtain ⟨UF, hUF⟩ := exists_ambient_unitary_intertwining ιF U
    obtain ⟨WE, hWE⟩ := exists_ambient_unitary_intertwining ιE V.symm
    have hadj : LinearMap.adjoint ιE.toLinearMap ∘ₗ WE.symm.toLinearMap =
        V.toLinearMap ∘ₗ LinearMap.adjoint ιE.toLinearMap := by
      have h := congrArg LinearMap.adjoint hWE
      simpa only [LinearMap.adjoint_comp,
        WE.adjoint_toLinearMap_eq_symm,
        (V.symm).adjoint_toLinearMap_eq_symm,
        LinearIsometryEquiv.symm_symm] using h
    have hlift : coordinateLift ιE ιF
          (U.toLinearMap ∘ₗ X ∘ₗ V.toLinearMap) =
        UF.toLinearMap ∘ₗ coordinateLift ιE ιF X ∘ₗ
          WE.symm.toLinearMap := by
      ext z
      simp only [coordinateLift, LinearMap.comp_apply]
      calc
        ιF (U (X (V (LinearMap.adjoint ιE.toLinearMap z)))) =
            UF (ιF (X (V (LinearMap.adjoint ιE.toLinearMap z)))) :=
          (LinearMap.congr_fun hUF _).symm
        _ = UF (ιF (X (LinearMap.adjoint ιE.toLinearMap (WE.symm z)))) := by
          have hz := LinearMap.congr_fun hadj z
          simp only [LinearMap.comp_apply,
            LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] at hz
          exact congrArg (fun q => UF (ιF (X q))) hz.symm
    rw [hlift]
    exact N.invariant UF WE.symm _

/-- The initial coordinate embedding determined by the first `d` vectors of
the standard orthonormal basis. -/
private noncomputable def initialCoordinateIsometry
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [FiniteDimensional 𝕜 K]
    {d : ℕ} (hd : d ≤ finrank 𝕜 K) :
    EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] K :=
  familyIsometry ((stdOrthonormalBasis 𝕜 K).orthonormal.comp
    (fun i => Fin.castLE hd i) (Fin.castLE_injective hd))

/-- The square diagonal operator carrying the nonzero rectangular singular
coordinates. -/
private noncomputable def singularValueDiagonal (d : ℕ)
    (A : E →ₗ[𝕜] F) :
    EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
  diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
    (fun i => A.singularValues (i : ℕ))

private theorem singularValues_singularValueDiagonal
    {d : ℕ} (A : E →ₗ[𝕜] F) (hrank : finrank 𝕜 A.range ≤ d) :
    (singularValueDiagonal d A).singularValues = A.singularValues := by
  have hanti : Antitone (fun i : Fin d => A.singularValues (i : ℕ)) :=
    fun i j hij => A.singularValues_antitone (Fin.le_def.mp hij)
  have hnonneg : ∀ i : Fin d, 0 ≤ A.singularValues (i : ℕ) :=
    fun i => A.singularValues_nonneg _
  apply Finsupp.ext
  intro i
  rcases lt_or_ge i d with hi | hi
  · simpa [singularValueDiagonal] using
      singularValues_diagOp (𝕜 := 𝕜) finrank_euclideanSpace_fin
        (EuclideanSpace.basisFun (Fin d) 𝕜) hanti hnonneg ⟨i, hi⟩
  · have hcoord : finrank 𝕜 (EuclideanSpace 𝕜 (Fin d)) ≤ i := by
      simpa only [finrank_euclideanSpace_fin] using hi
    rw [(singularValueDiagonal d A).singularValues_of_finrank_le hcoord,
      A.singularValues_eq_zero_iff_le_finrank_range.mpr (hrank.trans hi)]

private theorem apply_eq_coordinateSquareNorm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (N : RectangularUnitarilyInvariantNorm 𝕜 E F)
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (A : E →ₗ[𝕜] F) (X : H →ₗ[𝕜] H)
    (hσ : X.singularValues = A.singularValues) :
    N A = coordinateSquareNorm N ιE ιF X := by
  have hliftσ : (coordinateLift ιE ιF X).singularValues = A.singularValues :=
    (singularValues_coordinateLift ιE ιF X).trans hσ
  obtain ⟨U, V, hfac⟩ :=
    exists_unitary_factorization_of_singularValues_eq hliftσ.symm
  change N A = N (coordinateLift ιE ιF X)
  rw [hfac]
  exact N.invariant U V _


/-- A real-linear two-sided unitary action on rectangular maps. -/
private noncomputable def twoSidedActionLinear
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    (E →ₗ[𝕜] F) →ₗ[ℝ] (E →ₗ[𝕜] F) where
  toFun A := U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap
  map_add' A B := by
    ext x
    simp [LinearMap.comp_apply]
  map_smul' r A := by
    ext x
    change U (((r : 𝕜) • A) (V x)) = ((r : 𝕜) •
      (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)) x
    simp [LinearMap.comp_apply]

/-- The real convex hull of a two-sided unitary orbit is invariant under any
further two-sided unitary action. -/
private theorem twoSidedAction_mem_convexHull
    {E₀ F₀ : Type*}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    {A C : E₀ →ₗ[𝕜] F₀}
    (hA : A ∈ convexHull ℝ (twoSidedUnitaryOrbit C))
    (U : F₀ ≃ₗᵢ[𝕜] F₀) (V : E₀ ≃ₗᵢ[𝕜] E₀) :
    U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap ∈
      convexHull ℝ (twoSidedUnitaryOrbit C) := by
  let L := twoSidedActionLinear (𝕜 := 𝕜) U V
  have hmem : L A ∈ L '' convexHull ℝ (twoSidedUnitaryOrbit C) :=
    ⟨A, hA, rfl⟩
  rw [L.image_convexHull] at hmem
  apply convexHull_mono (𝕜 := ℝ) ?_ hmem
  rintro Y ⟨Y0, ⟨U0, V0, rfl⟩, rfl⟩
  refine ⟨U0.trans U, V.trans V0, ?_⟩
  ext x
  rfl

/-- Abstract T-transform descent with values in a convex set invariant under
coordinate transpositions and one-coordinate sign changes.

This is the membership-valued analogue of
`UnitarilyInvariantNorm.gauge_le_gauge_of_prefix_sums_le`.  It is formulated
once here so the rectangular orbit theorem can use the same finite descent
without invoking separation theorems or an external majorization library. -/
private theorem mem_convex_of_prefix_sums_le
    {n : ℕ} {K : Set (Fin n → ℝ)} (hK : Convex ℝ K)
    (hswap : ∀ y ∈ K, ∀ j l : Fin n, y ∘ Equiv.swap j l ∈ K)
    (hneg : ∀ y ∈ K, ∀ j : Fin n,
      Function.update y j (-(y j)) ∈ K)
    {z y : Fin n → ℝ} (hzanti : Antitone z)
    (hz0 : ∀ i, 0 ≤ z i) (hy0 : ∀ i, 0 ≤ y i)
    (hpre : ∀ m : ℕ,
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), z i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), y i)
    (hyK : y ∈ K) : z ∈ K := by
  classical
  have update_mem : ∀ (q : Fin n → ℝ), q ∈ K → ∀ (j : Fin n) (t : ℝ),
      |t| ≤ q j → Function.update q j t ∈ K := by
    intro q hq j t ht
    have hqj : 0 ≤ q j := le_trans (abs_nonneg t) ht
    rcases hqj.eq_or_lt with hzero | hpos
    · have ht0 : t = 0 := by
        have : |t| ≤ 0 := by simpa [hzero] using ht
        exact abs_eq_zero.mp (le_antisymm this (abs_nonneg t))
      have hupd : Function.update q j t = q := by
        funext i
        rcases eq_or_ne i j with rfl | hij
        · rw [Function.update_self, ht0, ← hzero]
        · rw [Function.update_of_ne hij]
      simpa [hupd] using hq
    · let c1 : ℝ := (q j + t) / (2 * q j)
      let c2 : ℝ := (q j - t) / (2 * q j)
      obtain ⟨ht1, ht2⟩ := abs_le.mp ht
      have hden : 0 < 2 * q j := by linarith
      have hc1 : 0 ≤ c1 := div_nonneg (by linarith) hden.le
      have hc2 : 0 ≤ c2 := div_nonneg (by linarith) hden.le
      have hsum : c1 + c2 = 1 := by
        dsimp [c1, c2]
        field_simp
        ring
      have hdecomp : Function.update q j t =
          c1 • q + c2 • Function.update q j (-(q j)) := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases eq_or_ne i j with rfl | hij
        · rw [Function.update_self, Function.update_self]
          dsimp [c1, c2]
          field_simp
          ring
        · rw [Function.update_of_ne hij, Function.update_of_ne hij,
            ← add_mul, hsum, one_mul]
      rw [hdecomp]
      exact hK hq (hneg q hq j) hc1 hc2 hsum
  have mono_mem : ∀ d (q : Fin n → ℝ),
      (Finset.univ.filter fun i => z i ≠ q i).card ≤ d →
      q ∈ K → (∀ i, z i ≤ q i) → z ∈ K := by
    intro d
    induction d with
    | zero =>
        intro q hcard hq _
        have hemp : (Finset.univ.filter fun i => z i ≠ q i) = ∅ :=
          Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
        have hzq : z = q := funext fun i => by
          by_contra hne
          have hi : i ∈ Finset.univ.filter fun i => z i ≠ q i :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
          rw [hemp] at hi
          simp at hi
        simpa [hzq] using hq
    | succ d ih =>
        intro q hcard hq hzq
        by_cases heq : z = q
        · simpa [heq] using hq
        · have hne : (Finset.univ.filter fun i => z i ≠ q i).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hemp
            apply heq
            funext i
            by_contra hneq
            have hi : i ∈ Finset.univ.filter fun i => z i ≠ q i :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩
            rw [hemp] at hi
            simp at hi
          obtain ⟨j, hj⟩ := hne
          let q' := Function.update q j (z j)
          have hq'K : q' ∈ K := by
            apply update_mem q hq j (z j)
            rw [abs_of_nonneg (hz0 j)]
            exact hzq j
          have hzq' : ∀ i, z i ≤ q' i := by
            intro i
            rcases eq_or_ne i j with rfl | hij
            · simp [q']
            · simp [q', hij, hzq i]
          have hsub : (Finset.univ.filter fun i => z i ≠ q' i) ⊆
              (Finset.univ.filter fun i => z i ≠ q i).erase j := by
            intro i hi
            obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
            have hij : i ≠ j := by
              rintro rfl
              exact hine (by simp [q'])
            refine Finset.mem_erase.mpr ⟨hij,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
            simpa [q', hij] using hine
          have hcard' : (Finset.univ.filter fun i => z i ≠ q' i).card ≤ d := by
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_erase_of_mem hj
            omega
          exact ih q' hcard' hq'K hzq'
  have H : ∀ d (q : Fin n → ℝ),
      (Finset.univ.filter fun i => z i ≠ q i).card ≤ d →
      (∀ i, 0 ≤ q i) →
      (∀ m : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), z i ≤
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), q i) →
      q ∈ K → z ∈ K := by
    intro d
    induction d with
    | zero =>
        intro q hcard _ _ hq
        exact mono_mem 0 q hcard hq (fun i => by
          have := hpre ((i : ℕ) + 1)
          -- The zero-disagreement case already gives equality directly.
          have hemp : (Finset.univ.filter fun k => z k ≠ q k) = ∅ :=
            Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
          by_contra hnot
          have hi : i ∈ Finset.univ.filter fun k => z k ≠ q k :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_gt (lt_of_not_ge hnot)⟩
          rw [hemp] at hi
          simp at hi)
    | succ d ih =>
        intro q hcard hq0 hqpre hqK
        by_cases hall : ∀ i, z i ≤ q i
        · exact mono_mem (d + 1) q hcard hqK hall
        push Not at hall
        have hSne : (Finset.univ.filter fun i : Fin n => q i < z i).Nonempty :=
          hall.imp fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        let l := (Finset.univ.filter fun i : Fin n => q i < z i).min' hSne
        have hlS : q l < z l :=
          (Finset.mem_filter.mp
            ((Finset.univ.filter fun i : Fin n => q i < z i).min'_mem hSne)).2
        have hlmin : ∀ i, i < l → z i ≤ q i := by
          intro i hil
          by_contra hzy
          push Not at hzy
          exact absurd
            (Finset.min'_le _ i (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, hzy⟩)) (not_le.mpr hil)
        have hexj : ∃ j, j < l ∧ z j < q j := by
          by_contra h
          push Not at h
          have heq : ∀ i, i < l → z i = q i := fun i hi =>
            le_antisymm (hlmin i hi) (h i hi)
          have hp := hqpre ((l : ℕ) + 1)
          have hset : (Finset.univ.filter fun i : Fin n =>
              (i : ℕ) < (l : ℕ) + 1) =
              insert l (Finset.univ.filter fun i : Fin n => (i : ℕ) < (l : ℕ)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_insert]
            constructor
            · intro hi
              rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with heq' | hlt
              · exact Or.inl (Fin.ext heq')
              · exact Or.inr hlt
            · rintro (rfl | hi)
              · omega
              · omega
          have hlnot : l ∉ Finset.univ.filter
              (fun i : Fin n => (i : ℕ) < (l : ℕ)) := by simp
          rw [hset, Finset.sum_insert hlnot, Finset.sum_insert hlnot] at hp
          have hsum_eq :
              ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < (l : ℕ)), z i =
                ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < (l : ℕ)), q i := by
            refine Finset.sum_congr rfl fun i hi => heq i ?_
            exact Fin.lt_def.mpr (Finset.mem_filter.mp hi).2
          rw [hsum_eq] at hp
          linarith
        obtain ⟨j, hjl, hzj⟩ := hexj
        have hjl_ne : j ≠ l := ne_of_lt hjl
        let delta : ℝ := min (q j - z j) (z l - q l)
        have hdeltaPos : 0 < delta := lt_min (by linarith) (by linarith)
        have hdelta1 : delta ≤ q j - z j := min_le_left _ _
        have hdelta2 : delta ≤ z l - q l := min_le_right _ _
        have hdeltaLt : delta < q j - q l :=
          lt_of_le_of_lt hdelta1 (by linarith [hzanti hjl.le])
        have hqjl : 0 < q j - q l := by linarith
        let c : ℝ := delta / (q j - q l)
        have hcpos : 0 < c := div_pos hdeltaPos hqjl
        have hclt : c < 1 := (div_lt_one hqjl).mpr hdeltaLt
        have hcmul : c * (q j - q l) = delta :=
          div_mul_cancel₀ delta (ne_of_gt hqjl)
        let q' : Fin n → ℝ :=
          Function.update (Function.update q j (q j - delta)) l (q l + delta)
        have hq'j : q' j = q j - delta := by
          simp [q', Function.update_of_ne hjl_ne]
        have hq'l : q' l = q l + delta := by simp [q']
        have hq'i : ∀ i, i ≠ j → i ≠ l → q' i = q i := by
          intro i hij hil
          simp [q', hij, hil]
        have hcomb : q' = (1 - c) • q + c • (q ∘ Equiv.swap j l) := by
          funext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Function.comp_apply]
          rcases eq_or_ne i j with rfl | hij
          · rw [hq'j, Equiv.swap_apply_left]
            linear_combination hcmul
          rcases eq_or_ne i l with rfl | hil
          · rw [hq'l, Equiv.swap_apply_right]
            linear_combination -hcmul
          · rw [hq'i i hij hil, Equiv.swap_apply_of_ne_of_ne hij hil]
            ring
        have hq'0 : ∀ i, 0 ≤ q' i := by
          intro i
          rcases eq_or_ne i j with heq | hij
          · rw [heq, hq'j]
            linarith [hz0 j]
          rcases eq_or_ne i l with heq | hil
          · rw [heq, hq'l]
            linarith [hq0 l]
          · rw [hq'i i hij hil]
            exact hq0 i
        have hq'pre : ∀ m : ℕ,
            ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), z i ≤
              ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < m), q' i := by
          intro m
          rcases le_or_gt m (j : ℕ) with hmj | hmj
          · have hcong : ∀ i ∈ Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m), q' i = q i := by
              intro i hi
              have hivm := (Finset.mem_filter.mp hi).2
              have hij : i ≠ j := fun h => by subst h; omega
              have hil : i ≠ l := fun h => by subst h; omega
              exact hq'i i hij hil
            rw [Finset.sum_congr rfl hcong]
            exact hqpre m
          rcases le_or_gt m (l : ℕ) with hml | hml
          · have hcong : ∀ i ∈ Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m),
                q' i = Function.update q j (q j - delta) i := by
              intro i hi
              have hivm := (Finset.mem_filter.mp hi).2
              have hil : i ≠ l := fun h => by subst h; omega
              simp [q', hil]
            have hjmem : j ∈ Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmj⟩
            rw [Finset.sum_congr rfl hcong,
              Finset.sum_update_of_mem hjmem]
            have hqsplit : ∑ i ∈ Finset.univ.filter
                  (fun i : Fin n => (i : ℕ) < m), q i =
                q j + ∑ i ∈ (Finset.univ.filter
                  (fun i : Fin n => (i : ℕ) < m)) \ {j}, q i := by
              rw [← Finset.erase_eq]
              exact (Finset.add_sum_erase _ q hjmem).symm
            have hterm : q j - z j ≤
                ∑ i ∈ Finset.univ.filter
                  (fun i : Fin n => (i : ℕ) < m), (q i - z i) := by
              refine Finset.single_le_sum (f := fun i => q i - z i) ?_ hjmem
              intro i hi
              have hivm := (Finset.mem_filter.mp hi).2
              have hil : i < l := Fin.lt_def.mpr (by omega)
              linarith [hlmin i hil]
            rw [Finset.sum_sub_distrib] at hterm
            linarith [hqpre m, hdelta1]
          · have hjmem : j ∈ Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
            have hlmem : l ∈ Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hml⟩
            have hjmem' : j ∈ (Finset.univ.filter
                (fun i : Fin n => (i : ℕ) < m)) \ {l} :=
              Finset.mem_sdiff.mpr ⟨hjmem, by simp [hjl_ne]⟩
            have heqsum : ∑ i ∈ Finset.univ.filter
                  (fun i : Fin n => (i : ℕ) < m), q' i =
                ∑ i ∈ Finset.univ.filter
                  (fun i : Fin n => (i : ℕ) < m), q i := by
              have h1 : ∑ i ∈ Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m), q' i =
                  (q l + delta) + ∑ i ∈ (Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l},
                    Function.update q j (q j - delta) i := by
                unfold q'
                exact Finset.sum_update_of_mem hlmem _ _
              have h2 : ∑ i ∈ (Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l},
                    Function.update q j (q j - delta) i =
                  (q j - delta) + ∑ i ∈ ((Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l}) \ {j}, q i :=
                Finset.sum_update_of_mem hjmem' _ _
              have h3 : ∑ i ∈ Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m), q i =
                  q l + ∑ i ∈ (Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l}, q i := by
                rw [← Finset.erase_eq]
                exact (Finset.add_sum_erase _ q hlmem).symm
              have h4 : ∑ i ∈ (Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l}, q i =
                  q j + ∑ i ∈ ((Finset.univ.filter
                    (fun i : Fin n => (i : ℕ) < m)) \ {l}) \ {j}, q i := by
                rw [← Finset.erase_eq, ← Finset.erase_eq]
                exact (Finset.add_sum_erase _ q (by rwa [Finset.erase_eq])).symm
              rw [h1, h2, h3, h4]
              ring
            rw [heqsum]
            exact hqpre m
        have hsub : (Finset.univ.filter fun i => z i ≠ q' i) ⊆
            Finset.univ.filter fun i => z i ≠ q i := by
          intro i hi
          obtain ⟨-, hine⟩ := Finset.mem_filter.mp hi
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => ?_⟩
          have hij : i ≠ j := by
            rintro rfl
            exact absurd heq hzj.ne
          have hil : i ≠ l := by
            rintro rfl
            exact absurd heq hlS.ne'
          exact hine (by rw [hq'i i hij hil]; exact heq)
        have hwitness : ∃ w ∈ Finset.univ.filter (fun i => z i ≠ q i),
            w ∉ Finset.univ.filter (fun i => z i ≠ q' i) := by
          rcases min_choice (q j - z j) (z l - q l) with hmin | hmin
          · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzj.ne⟩, ?_⟩
            have hj' : q' j = z j := by
              rw [hq'j]
              dsimp [delta]
              rw [hmin]
              ring
            simp [hj']
          · refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlS.ne'⟩, ?_⟩
            have hl' : q' l = z l := by
              rw [hq'l]
              dsimp [delta]
              rw [hmin]
              ring
            simp [hl']
        have hcard' : (Finset.univ.filter fun i => z i ≠ q' i).card ≤ d := by
          have hlt := Finset.card_lt_card
            ((Finset.ssubset_iff_of_subset hsub).mpr hwitness)
          omega
        have hq'K : q' ∈ K := by
          rw [hcomb]
          exact hK hqK (hswap q hqK j l) (by linarith) hcpos.le (by linarith)
        exact ih q' hcard' hq'0 hq'pre hq'K
  exact H _ y le_rfl hy0 hpre hyK

/-- Lift a square coordinate operator to a rectangular map after arbitrary
left and right coordinate unitaries, extending those unitaries to the ambient
spaces. -/
private theorem coordinateLift_unitary_factorization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (U V : H ≃ₗᵢ[𝕜] H) (X : H →ₗ[𝕜] H) :
    ∃ (UF : F ≃ₗᵢ[𝕜] F) (VE : E ≃ₗᵢ[𝕜] E),
      coordinateLift ιE ιF
          (U.toLinearMap ∘ₗ X ∘ₗ V.toLinearMap) =
        UF.toLinearMap ∘ₗ coordinateLift ιE ιF X ∘ₗ VE.toLinearMap := by
  obtain ⟨UF, hUF⟩ := exists_ambient_unitary_intertwining ιF U
  obtain ⟨WE, hWE⟩ := exists_ambient_unitary_intertwining ιE V.symm
  have hadj : LinearMap.adjoint ιE.toLinearMap ∘ₗ WE.symm.toLinearMap =
      V.toLinearMap ∘ₗ LinearMap.adjoint ιE.toLinearMap := by
    have h := congrArg LinearMap.adjoint hWE
    simpa only [LinearMap.adjoint_comp, WE.adjoint_toLinearMap_eq_symm,
      (V.symm).adjoint_toLinearMap_eq_symm,
      LinearIsometryEquiv.symm_symm] using h
  refine ⟨UF, WE.symm, ?_⟩
  ext z
  simp only [coordinateLift, LinearMap.comp_apply]
  calc
    ιF (U (X (V (LinearMap.adjoint ιE.toLinearMap z)))) =
        UF (ιF (X (V (LinearMap.adjoint ιE.toLinearMap z)))) :=
      (LinearMap.congr_fun hUF _).symm
    _ = UF (ιF (X (LinearMap.adjoint ιE.toLinearMap (WE.symm z)))) := by
      have hz := LinearMap.congr_fun hadj z
      simp only [LinearMap.comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] at hz
      exact congrArg (fun q => UF (ιF (X q))) hz.symm

/-- Real-linear map from a singular-value coordinate vector to its rectangular
diagonal lift. -/
private noncomputable def coordinateDiagonalLift
    {d : ℕ}
    (ιE : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E)
    (ιF : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] F) :
    (Fin d → ℝ) →ₗ[ℝ] (E →ₗ[𝕜] F) where
  toFun x := coordinateLift ιE ιF
    (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) x)
  map_add' x y := by
    ext z
    simp [coordinateLift, diagOp_add, LinearMap.comp_apply]
  map_smul' r x := by
    ext z
    change coordinateLift ιE ιF
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) (r • x)) z =
      ((r : 𝕜) • coordinateLift ιE ιF
        (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) x)) z
    rw [diagOp_real_smul]
    simp only [coordinateLift, LinearMap.comp_apply, LinearMap.smul_apply]
    exact ιF.toLinearMap.map_smul (r : 𝕜)
      ((diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) x)
        (LinearMap.adjoint ιE.toLinearMap z))

/-- Weak singular-value majorization is exactly the finite-dimensional
convex-hull order generated by the two-sided unitary orbit.

The proof applies the abstract T-transform descent to the preimage of the orbit
convex hull under a rectangular diagonal lift.  Coordinate swaps and sign
changes become two-sided unitary actions, while equal singular-value data is
transported by the rectangular SVD factorization already proved above. -/
theorem mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le
    {A B : E →ₗ[𝕜] F}
    (h : ∀ k, rectangularKyFanSum k A ≤ rectangularKyFanSum k B) :
    A ∈ convexHull ℝ (twoSidedUnitaryOrbit B) := by
  classical
  let d : ℕ := min (finrank 𝕜 E) (finrank 𝕜 F)
  have hdE : d ≤ finrank 𝕜 E := by
    dsimp [d]
    exact min_le_left _ _
  have hdF : d ≤ finrank 𝕜 F := by
    dsimp [d]
    exact min_le_right _ _
  let ιE := initialCoordinateIsometry (𝕜 := 𝕜) (K := E) hdE
  let ιF := initialCoordinateIsometry (𝕜 := 𝕜) (K := F) hdF
  let L := coordinateDiagonalLift (𝕜 := 𝕜) ιE ιF
  let z : Fin d → ℝ := fun i => A.singularValues (i : ℕ)
  let y : Fin d → ℝ := fun i => B.singularValues (i : ℕ)
  let K : Set (Fin d → ℝ) :=
    L ⁻¹' convexHull ℝ (twoSidedUnitaryOrbit B)
  have hKconv : Convex ℝ K :=
    (convex_convexHull ℝ (twoSidedUnitaryOrbit B)).linear_preimage L
  have hswap : ∀ q ∈ K, ∀ j l : Fin d,
      q ∘ Equiv.swap j l ∈ K := by
    intro q hq j l
    let P : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜]
        EuclideanSpace 𝕜 (Fin d) :=
      LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 (Equiv.swap j l)
    have hdiag : diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
          (q ∘ Equiv.swap j l) =
        P.symm.toLinearMap ∘ₗ
          diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ
            P.toLinearMap := by
      let b := EuclideanSpace.basisFun (Fin d) 𝕜
      refine b.toBasis.ext fun i => ?_
      simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
      rw [diagOp_apply_basis]
      have hPi : P (b i) = b (Equiv.swap j l i) := by
        simp [P, b]
      change ((q (Equiv.swap j l i) : ℝ) : 𝕜) • b i =
        P.symm (diagOp b q (P (b i)))
      rw [hPi, diagOp_apply_basis, map_smul]
      have hPsymm : P.symm (b (Equiv.swap j l i)) = b i := by
        rw [← hPi, LinearIsometryEquiv.symm_apply_apply]
      rw [hPsymm]
    obtain ⟨UF, VE, hfac⟩ := coordinateLift_unitary_factorization
      ιE ιF P.symm P
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q)
    change L (q ∘ Equiv.swap j l) ∈
      convexHull ℝ (twoSidedUnitaryOrbit B)
    change L q ∈ convexHull ℝ (twoSidedUnitaryOrbit B) at hq
    change coordinateLift ιE ιF
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
        (q ∘ Equiv.swap j l)) ∈ _
    rw [hdiag, hfac]
    exact twoSidedAction_mem_convexHull hq UF VE
  have hneg : ∀ q ∈ K, ∀ j : Fin d,
      Function.update q j (-(q j)) ∈ K := by
    intro q hq j
    let R := ((𝕜 ∙ (EuclideanSpace.basisFun (Fin d) 𝕜) j)ᗮ).reflection
    have hdiag : diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
          (Function.update q j (-(q j))) =
        diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ R.toLinearMap := by
      refine (EuclideanSpace.basisFun (Fin d) 𝕜).toBasis.ext fun i => ?_
      simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
      rcases eq_or_ne i j with rfl | hij
      · rw [Submodule.reflection_orthogonalComplement_singleton_eq_neg,
          map_neg, diagOp_apply_basis, diagOp_apply_basis,
          Function.update_self, RCLike.ofReal_neg, neg_smul]
      · have hmem : (EuclideanSpace.basisFun (Fin d) 𝕜) i ∈
            (𝕜 ∙ (EuclideanSpace.basisFun (Fin d) 𝕜) j)ᗮ :=
          Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
            ((EuclideanSpace.basisFun (Fin d) 𝕜).orthonormal.2 (Ne.symm hij))
        rw [Submodule.reflection_mem_subspace_eq_self hmem,
          diagOp_apply_basis, diagOp_apply_basis, Function.update_of_ne hij]
    obtain ⟨UF, VE, hfac0⟩ := coordinateLift_unitary_factorization
      ιE ιF (LinearIsometryEquiv.refl 𝕜 _) R
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q)
    have hid : (LinearIsometryEquiv.refl 𝕜
          (EuclideanSpace 𝕜 (Fin d))).toLinearMap ∘ₗ
          diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ R.toLinearMap =
        diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ R.toLinearMap := by
      ext x
      rfl
    rw [hid] at hfac0
    have hfac : coordinateLift ιE ιF
          (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ R.toLinearMap) =
        UF.toLinearMap ∘ₗ coordinateLift ιE ιF
          (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q) ∘ₗ VE.toLinearMap :=
      hfac0
    change L (Function.update q j (-(q j))) ∈
      convexHull ℝ (twoSidedUnitaryOrbit B)
    change L q ∈ convexHull ℝ (twoSidedUnitaryOrbit B) at hq
    change coordinateLift ιE ιF
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
        (Function.update q j (-(q j)))) ∈ _
    rw [hdiag, hfac]
    exact twoSidedAction_mem_convexHull hq UF VE
  have hrankA : finrank 𝕜 A.range ≤ d := by
    apply le_min
    · have hnull := A.finrank_range_add_finrank_ker
      omega
    · exact Submodule.finrank_le _
  have hrankB : finrank 𝕜 B.range ≤ d := by
    apply le_min
    · have hnull := B.finrank_range_add_finrank_ker
      omega
    · exact Submodule.finrank_le _
  have hLy : L y ∈ twoSidedUnitaryOrbit B := by
    have hsigma : (L y).singularValues = B.singularValues := by
      change (coordinateLift ιE ιF (singularValueDiagonal d B)).singularValues =
        B.singularValues
      rw [singularValues_coordinateLift,
        singularValues_singularValueDiagonal B hrankB]
    obtain ⟨U, V, hfac⟩ :=
      exists_unitary_factorization_of_singularValues_eq hsigma
    exact ⟨U, V, hfac⟩
  have hyK : y ∈ K := subset_convexHull ℝ _ hLy
  have hzanti : Antitone z := fun i j hij =>
    A.singularValues_antitone (Fin.le_def.mp hij)
  have hz0 : ∀ i, 0 ≤ z i := fun i => A.singularValues_nonneg _
  have hy0 : ∀ i, 0 ≤ y i := fun i => B.singularValues_nonneg _
  have hpre : ∀ m : ℕ,
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m), z i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m), y i := by
    intro m
    rcases le_or_gt m d with hm | hm
    · rw [sum_filter_lt_eq_sum_fin hm (fun k => A.singularValues k),
        sum_filter_lt_eq_sum_fin hm (fun k => B.singularValues k)]
      exact h m
    · have huniv : (Finset.univ.filter
          fun i : Fin d => (i : ℕ) < m) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => lt_trans i.isLt hm
      rw [huniv]
      exact h d
  have hzK : z ∈ K :=
    mem_convex_of_prefix_sums_le hKconv hswap hneg hzanti hz0 hy0 hpre hyK
  have hsigmaA : A.singularValues = (L z).singularValues := by
    symm
    change (coordinateLift ιE ιF (singularValueDiagonal d A)).singularValues =
      A.singularValues
    rw [singularValues_coordinateLift,
      singularValues_singularValueDiagonal A hrankA]
  obtain ⟨U, V, hfac⟩ :=
    exists_unitary_factorization_of_singularValues_eq hsigmaA
  change L z ∈ convexHull ℝ (twoSidedUnitaryOrbit B) at hzK
  rw [hfac]
  exact twoSidedAction_mem_convexHull hzK U V


/-- Fan dominance in rectangular form.
-/
theorem apply_le_of_kyFanSum_le {A B : E →ₗ[𝕜] F}
    (h : ∀ k, rectangularKyFanSum k A ≤ rectangularKyFanSum k B) : N A ≤ N B := by
  let d : ℕ := min (finrank 𝕜 E) (finrank 𝕜 F)
  have hdE : d ≤ finrank 𝕜 E := by
    dsimp [d]
    exact min_le_left _ _
  have hdF : d ≤ finrank 𝕜 F := by
    dsimp [d]
    exact min_le_right _ _
  let ιE := initialCoordinateIsometry (𝕜 := 𝕜) (K := E) hdE
  let ιF := initialCoordinateIsometry (𝕜 := 𝕜) (K := F) hdF
  let XA := singularValueDiagonal d A
  let XB := singularValueDiagonal d B
  have hrankA : finrank 𝕜 A.range ≤ d := by
    have hdom : finrank 𝕜 A.range ≤ finrank 𝕜 E := by
      have hranknull := A.finrank_range_add_finrank_ker
      omega
    have hcod : finrank 𝕜 A.range ≤ finrank 𝕜 F := Submodule.finrank_le _
    dsimp [d]
    exact le_min hdom hcod
  have hrankB : finrank 𝕜 B.range ≤ d := by
    have hdom : finrank 𝕜 B.range ≤ finrank 𝕜 E := by
      have hranknull := B.finrank_range_add_finrank_ker
      omega
    have hcod : finrank 𝕜 B.range ≤ finrank 𝕜 F := Submodule.finrank_le _
    dsimp [d]
    exact le_min hdom hcod
  have hσA : XA.singularValues = A.singularValues := by
    simpa only [XA] using singularValues_singularValueDiagonal A hrankA
  have hσB : XB.singularValues = B.singularValues := by
    simpa only [XB] using singularValues_singularValueDiagonal B hrankB
  have hNA : N A = coordinateSquareNorm N ιE ιF XA :=
    apply_eq_coordinateSquareNorm N ιE ιF A XA hσA
  have hNB : N B = coordinateSquareNorm N ιE ιF XB :=
    apply_eq_coordinateSquareNorm N ιE ιF B XB hσB
  rw [hNA, hNB]
  apply UnitarilyInvariantNorm.apply_le_of_kyFanSum_le
  intro k
  rw [kyFanSum_eq_sum_fin, kyFanSum_eq_sum_fin, hσA, hσB]
  exact h k

/-- Nonnegative real scaling commutes with rectangular Ky Fan prefix sums.

This public form is used when a sharp Sylvester inequality is converted into
unitary-orbit convex-hull membership.  The proof is coefficientwise scaling of
the singular-value sequence. -/
theorem rectangularKyFanSum_real_smul
    (k : ℕ) (A : E →ₗ[𝕜] F) {r : ℝ} (hr : 0 ≤ r) :
    rectangularKyFanSum k (((r : 𝕜)) • A) =
      r * rectangularKyFanSum k A := by
  unfold rectangularKyFanSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => singularValues_real_smul A hr i

/-- Convex-hull domination by a two-sided unitary orbit implies domination in
any rectangular unitarily invariant norm.

The proof extracts the existing finite orbit certificate with mass one and
then applies the certificate norm bound. -/
theorem apply_le_of_mem_convexHull_twoSidedUnitaryOrbit
    {A B : E →ₗ[𝕜] F}
    (h : A ∈ convexHull ℝ (twoSidedUnitaryOrbit B)) :
    N A ≤ N B := by
  have hcert : HasFiniteUnitaryOrbitCertificate 1 A B :=
    hasFiniteUnitaryOrbitCertificate_of_smul_mem_convexHull
      (m := 1) (mass := 1) zero_le_one le_rfl h (by simp)
  simpa using N.apply_le_of_finiteUnitaryOrbitCertificate hcert


end RectangularUnitarilyInvariantNorm

end DavisKahanTheory

end TauCeti
