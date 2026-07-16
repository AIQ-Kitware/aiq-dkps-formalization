/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Basic
import DavisKahan.Experimental.InfiniteDimensional.Core.UnboundedSpectral
import ForMathlib.Analysis.CStarAlgebra.SelfAdjointGapInverse
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The genuine-spectrum Sylvester estimate and the general `sin Θ` theorem

The separation predicates in `Core/AbstractSpectrum.lean` are point-spectrum
based and therefore vacuous for operators with empty point spectrum; the
theorems stated over them are unprovable in infinite dimensions (see
`docs/planning/davis-kahan-full-paper-goal.md`, statement-soundness finding of
2026-07-15).  This module is the honest layer: hypotheses are phrased through
the Banach-algebra spectrum, either of the ambient operator or of its
compression to a reducing subspace.

Main results, all fully proved:

* `norm_sylvester_le_of_spectrum_intervalExterior`: the constant-one
  interval/exterior Sylvester estimate.  If the self-adjoint `B` has spectrum
  in `[a, b]` while the self-adjoint `A` has spectrum outside
  `(a - d, b + d)`, then `A X - X B = C` forces `d ‖X‖ ≤ ‖C‖`.  The proof is
  the shift-and-invert argument: center at `c = (a+b)/2`, invert `A - c`
  through the continuous functional calculus with inverse norm at most
  `(r + d)⁻¹` where `r = (b-a)/2`, bound `‖B - c‖ ≤ r`, and absorb.
* `sinTheta_genuineSpectrum`: the fully general bounded operator-norm
  Davis--Kahan `sin Θ` theorem with genuine spectra: if `U` reduces the
  self-adjoint `A` with the spectrum of the compression `A|_U` in `[a, b]`,
  and `V` reduces the self-adjoint `B` with the spectrum of `B|_{Vᗮ}` outside
  `(a - d, b + d)`, then `d * directedGap U V ≤ ‖B - A‖`.

Complex scalars are required because Mathlib registers the continuous
functional calculus on Hilbert-space operators only over `ℂ`; the real case
is expected to follow by a norm-preserving complexification transfer.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

set_option maxHeartbeats 1600000 in
/-- **Constant-one interval/exterior Sylvester estimate, genuine spectra.**
If the spectrum of the self-adjoint `B` lies in `[a, b]` while the spectrum
of the self-adjoint `A` avoids `(a - d, b + d)`, then any solution of
`A X - X B = C` satisfies `d ‖X‖ ≤ ‖C‖`. -/
theorem norm_sylvester_le_of_spectrum_intervalExterior
    {A : F →L[ℂ] F} {B : E →L[ℂ] E} {X C : E →L[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hBspec : spectrum ℝ B ⊆ Set.Icc a b)
    (hAspec : ∀ x ∈ spectrum ℝ A, x ≤ a - d ∨ b + d ≤ x)
    (hEq : A ∘L X - X ∘L B = C) :
    d * ‖X‖ ≤ ‖C‖ := by
  set c : ℝ := (a + b) / 2 with hc
  set r : ℝ := (b - a) / 2 with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hrd : (0 : ℝ) < r + d := by linarith
  set A₁ : F →L[ℂ] F := A - algebraMap ℝ (F →L[ℂ] F) c with hA₁
  set B₁ : E →L[ℂ] E := B - algebraMap ℝ (E →L[ℂ] E) c with hB₁
  have hA₁sa : IsSelfAdjoint A₁ :=
    hA.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
  have hB₁sa : IsSelfAdjoint B₁ :=
    hB.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
  -- spectral position of the shifted operators
  have hA₁spec : ∀ x ∈ spectrum ℝ A₁, r + d ≤ |x| := by
    intro x hx
    rw [hA₁, ← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_sub.mp hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [← hyz]
    rcases hAspec y hy with h1 | h1
    · have hle : y - c ≤ -(r + d) := by rw [hc, hrdef]; linarith
      calc r + d ≤ -(y - c) := by linarith
        _ ≤ |y - c| := neg_le_abs _
    · have hge : r + d ≤ y - c := by rw [hc, hrdef]; linarith
      exact hge.trans (le_abs_self _)
  have hB₁spec : spectrum ℝ B₁ ⊆ Set.Icc (-r) r := by
    intro x hx
    rw [hB₁, ← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_sub.mp hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hmem := hBspec hy
    rw [Set.mem_Icc] at hmem
    rw [← hyz, Set.mem_Icc]
    constructor
    · rw [hc, hrdef]; linarith [hmem.1]
    · rw [hc, hrdef]; linarith [hmem.2]
  have hB₁norm : ‖B₁‖ ≤ r :=
    ForMathlib.IsSelfAdjoint.norm_le_of_spectrum_subset_Icc hB₁sa hr0 hB₁spec
  obtain ⟨J, hJ1, _hJ2, hJnorm⟩ :=
    ForMathlib.IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap hA₁sa
      hrd hA₁spec
  -- the shifted Sylvester equation
  have hEq₁ : A₁ ∘L X - X ∘L B₁ = C := by
    have h1 : algebraMap ℝ (F →L[ℂ] F) c ∘L X =
        X ∘L algebraMap ℝ (E →L[ℂ] E) c := by
      ext x
      simp [Algebra.algebraMap_eq_smul_one]
    calc A₁ ∘L X - X ∘L B₁
        = (A ∘L X - X ∘L B) -
            (algebraMap ℝ (F →L[ℂ] F) c ∘L X -
              X ∘L algebraMap ℝ (E →L[ℂ] E) c) := by
          rw [hA₁, hB₁, ContinuousLinearMap.sub_comp,
            ContinuousLinearMap.comp_sub]
          abel
      _ = C := by rw [h1, sub_self, sub_zero, hEq]
  -- absorb through the inverse
  have hJ1' : J ∘L A₁ = ContinuousLinearMap.id ℂ F := by
    rw [← ContinuousLinearMap.mul_def, hJ1, ContinuousLinearMap.one_def]
  have hXeq : X = J ∘L (C + X ∘L B₁) := by
    have h2 : A₁ ∘L X = C + X ∘L B₁ := by rw [← hEq₁]; abel
    calc X = (J ∘L A₁) ∘L X := by
          rw [hJ1', ContinuousLinearMap.id_comp]
      _ = J ∘L (A₁ ∘L X) := by rw [ContinuousLinearMap.comp_assoc]
      _ = J ∘L (C + X ∘L B₁) := by rw [h2]
  have hnorm : ‖X‖ ≤ (r + d)⁻¹ * (‖C‖ + ‖X‖ * r) := by
    calc ‖X‖ = ‖J ∘L (C + X ∘L B₁)‖ := by rw [← hXeq]
      _ ≤ ‖J‖ * ‖C + X ∘L B₁‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖J‖ * (‖C‖ + ‖X‖ * ‖B₁‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (norm_add_le _ _).trans
            (add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le _ _))
      _ ≤ (r + d)⁻¹ * (‖C‖ + ‖X‖ * r) := by
          refine mul_le_mul hJnorm ?_ (by positivity)
            (inv_nonneg.mpr hrd.le)
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hB₁norm (norm_nonneg _))
  have hkey := mul_le_mul_of_nonneg_left hnorm hrd.le
  rw [← mul_assoc, mul_inv_cancel₀ hrd.ne', one_mul] at hkey
  nlinarith [norm_nonneg X]

section Compression

/-- Compression of an ambient operator to a subspace admitting an orthogonal
projection.  For a reducing subspace of a self-adjoint operator this is the
honest restriction, and its Banach-algebra spectrum is the correct
interpretation of "the spectrum of `A` on `U`". -/
noncomputable def compressOperator (U : Submodule ℂ E)
    [U.HasOrthogonalProjection] (T : E →L[ℂ] E) : U →L[ℂ] U :=
  U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL

/-- Compression preserves self-adjointness. -/
theorem isSelfAdjoint_compressOperator {T : E →L[ℂ] E}
    (hT : IsSelfAdjoint T) (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    [CompleteSpace U] :
    IsSelfAdjoint (compressOperator U T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', compressOperator,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
    ← ContinuousLinearMap.star_eq_adjoint, hT.star_eq,
    ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
/-- The orthogonal complement of a reducing subspace is reducing. -/
theorem Reduces.orthogonalComplement {T : E →L[ℂ] E} {V : Submodule ℂ E}
    [V.HasOrthogonalProjection] (hV : Reduces T V) : Reduces T Vᗮ := by
  refine ⟨hV.2, ?_⟩
  intro y hy
  rw [Submodule.orthogonal_orthogonal] at hy ⊢
  exact hV.1 y hy

omit [CompleteSpace E] in
/-- The cross-block compression satisfies the Sylvester equation between the
two diagonal compressions. -/
theorem compress_sylvester_of_reduces
    {A B : E →L[ℂ] E} {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V) :
    compressOperator Vᗮ B ∘L (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) -
        (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) ∘L compressOperator U A =
      Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL := by
  have hVperp : Reduces B Vᗮ := Reduces.orthogonalComplement hV
  ext x
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    compressOperator, AddSubgroupClass.coe_sub, Submodule.subtypeL_apply,
    Submodule.coe_orthogonalProjectionOnto_apply]
  rw [← ContinuousLinearMap.starProjection_apply_comm_of_reduces B Vᗮ hVperp,
    Submodule.starProjection_eq_self_iff.mpr
      (Vᗮ.starProjection_apply_mem (B (x : E))),
    ContinuousLinearMap.starProjection_apply_comm_of_reduces A U hU,
    Submodule.starProjection_eq_self_iff.mpr x.2, map_sub]

/-- The cross-block compression has the norm of the directed projection
composition. -/
theorem norm_crossCompression_eq
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] :
    ‖Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL‖ =
      ‖Vᗮ.starProjection ∘L U.starProjection‖ := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun x => ?_
    have hkey : ((Vᗮ.orthogonalProjectionOnto ((x : E)) : ↥Vᗮ) : E) =
        (Vᗮ.starProjection ∘L U.starProjection) (x : E) := by
      show Vᗮ.starProjection (x : E) =
        Vᗮ.starProjection (U.starProjection (x : E))
      rw [Submodule.starProjection_eq_self_iff.mpr x.2]
    show ‖((Vᗮ.orthogonalProjectionOnto ((x : E)) : ↥Vᗮ) : E)‖ ≤
      ‖Vᗮ.starProjection ∘L U.starProjection‖ * ‖(x : E)‖
    rw [hkey]
    exact (Vᗮ.starProjection ∘L U.starProjection).le_opNorm _
  · refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun y => ?_
    have hkey : (Vᗮ.starProjection ∘L U.starProjection) y =
        (((Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL)
          (U.orthogonalProjectionOnto y) : ↥Vᗮ) : E) := rfl
    rw [hkey]
    calc ‖(((Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL)
          (U.orthogonalProjectionOnto y) : ↥Vᗮ) : E)‖
        = ‖(Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL)
            (U.orthogonalProjectionOnto y)‖ := rfl
      _ ≤ ‖Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL‖ *
            ‖U.orthogonalProjectionOnto y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL‖ * ‖y‖ := by
          refine mul_le_mul_of_nonneg_left ?_
            (ContinuousLinearMap.opNorm_nonneg _)
          show ‖((U.orthogonalProjectionOnto y : ↥U) : E)‖ ≤ ‖y‖
          exact U.norm_starProjection_apply_le y

end Compression

/-- **The fully general bounded operator-norm Davis--Kahan `sin Θ` theorem,
genuine spectra.**  If `U` reduces the self-adjoint `A` with the spectrum of
the compression `A|_U` contained in `[a, b]`, and `V` reduces the
self-adjoint `B` with the spectrum of the compression `B|_{Vᗮ}` outside the
open interval `(a - d, b + d)`, then `d * directedGap U V ≤ ‖B - A‖`. -/
theorem sinTheta_genuineSpectrum
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x) :
    d * directedGap U V ≤ ‖B - A‖ := by
  haveI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  haveI : CompleteSpace (Vᗮ : Submodule ℂ E) :=
    (Vᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hsyl := compress_sylvester_of_reduces hU hV
  have hest := norm_sylvester_le_of_spectrum_intervalExterior
    (isSelfAdjoint_compressOperator hB Vᗮ)
    (isSelfAdjoint_compressOperator hA U)
    hd hab hUspec hVspec hsyl
  have hCnorm : ‖Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL‖ ≤
      ‖B - A‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun x => ?_
    show ‖((Vᗮ.orthogonalProjectionOnto ((B - A) (x : E)) : ↥Vᗮ) : E)‖ ≤
      ‖B - A‖ * ‖(x : E)‖
    calc ‖((Vᗮ.orthogonalProjectionOnto ((B - A) (x : E)) : ↥Vᗮ) : E)‖
        = ‖Vᗮ.starProjection ((B - A) (x : E))‖ := rfl
      _ ≤ ‖(B - A) (x : E)‖ := Vᗮ.norm_starProjection_apply_le _
      _ ≤ ‖B - A‖ * ‖(x : E)‖ := (B - A).le_opNorm _
  calc d * directedGap U V
      = d * ‖Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL‖ := by
        rw [norm_crossCompression_eq]
        rfl
    _ ≤ ‖Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL‖ := hest
    _ ≤ ‖B - A‖ := hCnorm

/-- **Symmetric two-sided genuine-spectrum `sin Θ` theorem.**  When both
directed spectral configurations hold — the spectrum of `A|_U` in `[a, b]`
with `B|_{Vᗮ}` outside `(a - d, b + d)`, and the spectrum of `B|_V` in
`[a', b']` with `A|_{Uᗮ}` outside `(a' - d, b' + d)` — the full projection
gap (the maximum of the two directed gaps) obeys the same bound:
`d * subspaceGap U V ≤ ‖B - A‖`. -/
theorem sinTheta_genuineSpectrum_symmetric
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {a b a' b' d : ℝ} (hd : 0 < d) (hab : a ≤ b) (hab' : a' ≤ b')
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x)
    (hVspec' : spectrum ℝ (compressOperator V B) ⊆ Set.Icc a' b')
    (hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Uᗮ A),
      x ≤ a' - d ∨ b' + d ≤ x) :
    d * subspaceGap U V ≤ ‖B - A‖ := by
  have h1 : d * directedGap U V ≤ ‖B - A‖ :=
    sinTheta_genuineSpectrum hA hB hU hV hd hab hUspec hVspec
  have h2 : d * directedGap V U ≤ ‖A - B‖ :=
    sinTheta_genuineSpectrum hB hA hV hU hd hab' hVspec' hUspec'
  rw [show A - B = -(B - A) by abel, norm_neg] at h2
  have hmax : subspaceGap U V = max (directedGap U V) (directedGap V U) := by
    show ‖U.starProjection - V.starProjection‖ =
      max ‖Vᗮ.starProjection ∘L U.starProjection‖
        ‖Uᗮ.starProjection ∘L V.starProjection‖
    rw [Submodule.norm_starProjection_sub_eq_max,
      Submodule.starProjection_orthogonal' V,
      Submodule.starProjection_orthogonal' U]
  rw [hmax, mul_max_of_nonneg _ _ hd.le]
  exact max_le h1 h2

section IdealScope

open ForMathlib.DavisKahan.Experimental.ExactSinTheta

universe v'

variable {E₁ F₁ : Type v'}
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]

set_option maxHeartbeats 1600000 in
/-- **Ideal-gauge interval/exterior Sylvester estimate, genuine spectra.**
If the spectrum of the self-adjoint `B` lies in `[a, b]` while the spectrum
of the self-adjoint `A` avoids `(a - d, b + d)`, and `C` lies in a
rectangular symmetric ideal family, then any solution of `A X - X B = C`
lies in the family with `d · gauge X ≤ gauge C` — through the
shift-and-invert data and the Neumann-iteration ideal engine. -/
theorem mem_and_gauge_sylvester_le_of_spectrum_intervalExterior
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    {A : F₁ →L[ℂ] F₁} {B : E₁ →L[ℂ] E₁} {X C : E₁ →L[ℂ] F₁}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hBspec : spectrum ℝ B ⊆ Set.Icc a b)
    (hAspec : ∀ x ∈ spectrum ℝ A, x ≤ a - d ∨ b + d ≤ x)
    (hEq : A ∘L X - X ∘L B = C)
    (hC : N.Mem C) :
    N.Mem X ∧ d * N.gauge X ≤ N.gauge C := by
  set c : ℝ := (a + b) / 2 with hc
  set r : ℝ := (b - a) / 2 with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hrd : (0 : ℝ) < r + d := by linarith
  set A₁ : F₁ →L[ℂ] F₁ := A - algebraMap ℝ (F₁ →L[ℂ] F₁) c with hA₁
  set B₁ : E₁ →L[ℂ] E₁ := B - algebraMap ℝ (E₁ →L[ℂ] E₁) c with hB₁
  have hA₁sa : IsSelfAdjoint A₁ :=
    hA.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
  have hB₁sa : IsSelfAdjoint B₁ :=
    hB.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
  have hA₁spec : ∀ x ∈ spectrum ℝ A₁, r + d ≤ |x| := by
    intro x hx
    rw [hA₁, ← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_sub.mp hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [← hyz]
    rcases hAspec y hy with h1 | h1
    · have hle : y - c ≤ -(r + d) := by rw [hc, hrdef]; linarith
      calc r + d ≤ -(y - c) := by linarith
        _ ≤ |y - c| := neg_le_abs _
    · have hge : r + d ≤ y - c := by rw [hc, hrdef]; linarith
      exact hge.trans (le_abs_self _)
  have hB₁spec : spectrum ℝ B₁ ⊆ Set.Icc (-r) r := by
    intro x hx
    rw [hB₁, ← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_sub.mp hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hmem := hBspec hy
    rw [Set.mem_Icc] at hmem
    rw [← hyz, Set.mem_Icc]
    constructor
    · rw [hc, hrdef]; linarith [hmem.1]
    · rw [hc, hrdef]; linarith [hmem.2]
  have hB₁norm : ‖B₁‖ ≤ r :=
    ForMathlib.IsSelfAdjoint.norm_le_of_spectrum_subset_Icc hB₁sa hr0 hB₁spec
  obtain ⟨J, hJ1, hJ2, hJnorm⟩ :=
    ForMathlib.IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap hA₁sa
      hrd hA₁spec
  have hEq₁ : A₁ ∘L X - X ∘L B₁ = C := by
    have h1 : algebraMap ℝ (F₁ →L[ℂ] F₁) c ∘L X =
        X ∘L algebraMap ℝ (E₁ →L[ℂ] E₁) c := by
      ext x
      simp [Algebra.algebraMap_eq_smul_one]
    calc A₁ ∘L X - X ∘L B₁
        = (A ∘L X - X ∘L B) -
            (algebraMap ℝ (F₁ →L[ℂ] F₁) c ∘L X -
              X ∘L algebraMap ℝ (E₁ →L[ℂ] E₁) c) := by
          rw [hA₁, hB₁, ContinuousLinearMap.sub_comp,
            ContinuousLinearMap.comp_sub]
          abel
      _ = C := by rw [h1, sub_self, sub_zero, hEq]
  -- package the inverse for the Neumann ideal engine
  have hEq' : HasUnboundedBoundedSylvesterEquation
      (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded A₁) B₁ X C :=
    ClosedSylvesterEquation.ofBounded hEq₁
  refine sylvester_mem_and_gauge_le_of_unbounded_bound_inverse N
    ⟨J, fun y => Submodule.mem_top, ?_, ?_⟩ B₁ hr0 hd hJnorm hB₁norm hEq' hC
  · intro y
    show A₁ (J y) = y
    simpa using DFunLike.congr_fun hJ2 y
  · intro x
    show J (A₁ (x : F₁)) = (x : F₁)
    simpa using DFunLike.congr_fun hJ1 (x : F₁)

end IdealScope

section SinThetaIdealScope

open ForMathlib.DavisKahan.Experimental.ExactSinTheta

/-- **The bounded Davis--Kahan `sin Θ` theorem at unitary-invariant ideal
scope, genuine spectra.**  Under the directed spectral configuration of
`sinTheta_genuineSpectrum`, if the perturbation `B - A` lies in a
rectangular symmetric ideal family, then so does the directed projection
composition `P_{Vᗮ} P_U`, with `d · gauge (P_{Vᗮ} P_U) ≤ gauge (B - A)` —
the ideal-gauge strengthening of `d * directedGap U V ≤ ‖B - A‖`. -/
theorem sinTheta_genuineSpectrum_gauge
    (N : RectangularSymmetricIdealFamily (𝕜 := ℂ))
    {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {a b d : ℝ} (hd : 0 < d) (hab : a ≤ b)
    (hUspec : spectrum ℝ (compressOperator U A) ⊆ Set.Icc a b)
    (hVspec : ∀ x ∈ spectrum ℝ (compressOperator Vᗮ B),
      x ≤ a - d ∨ b + d ≤ x)
    (hMem : N.Mem (B - A)) :
    N.Mem (Vᗮ.starProjection ∘L U.starProjection) ∧
      d * N.gauge (Vᗮ.starProjection ∘L U.starProjection) ≤
        N.gauge (B - A) := by
  haveI : CompleteSpace U :=
    (U.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  haveI : CompleteSpace (Vᗮ : Submodule ℂ E) :=
    (Vᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hsyl := compress_sylvester_of_reduces hU hV
  have hCmem : N.Mem (Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL) :=
    N.comp_mem _ _ hMem
  have hmain := mem_and_gauge_sylvester_le_of_spectrum_intervalExterior N
    (isSelfAdjoint_compressOperator hB Vᗮ)
    (isSelfAdjoint_compressOperator hA U)
    hd hab hUspec hVspec hsyl hCmem
  have hfact : Vᗮ.starProjection ∘L U.starProjection =
      Vᗮ.subtypeL ∘L (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) ∘L
        U.orthogonalProjectionOnto := by
    ext x
    rfl
  constructor
  · rw [hfact]
    exact N.comp_mem _ _ hmain.1
  · have hgle : N.gauge (Vᗮ.starProjection ∘L U.starProjection) ≤
        N.gauge (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) := by
      rw [hfact]
      exact N.gauge_comp_le_of_contractions _ _ hmain.1
        Vᗮ.norm_subtypeL_le U.orthogonalProjectionOnto_norm_le
    have hCle : N.gauge (Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL)
        ≤ N.gauge (B - A) :=
      N.gauge_comp_le_of_contractions _ _ hMem
        Vᗮ.orthogonalProjectionOnto_norm_le U.norm_subtypeL_le
    calc d * N.gauge (Vᗮ.starProjection ∘L U.starProjection)
        ≤ d * N.gauge (Vᗮ.orthogonalProjectionOnto ∘L U.subtypeL) :=
          mul_le_mul_of_nonneg_left hgle hd.le
      _ ≤ N.gauge (Vᗮ.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL) :=
          hmain.2
      _ ≤ N.gauge (B - A) := hCle

end SinThetaIdealScope

end DavisKahanExt
end ForMathlib
