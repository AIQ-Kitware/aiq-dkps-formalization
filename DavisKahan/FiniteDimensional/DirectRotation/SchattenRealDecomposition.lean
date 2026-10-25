/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealGradientBlocks
import DavisKahan.FiniteDimensional.DirectRotation.SchattenRealKernelBlocks
import ForTauCeti.Analysis.InnerProductSpace.AnticommutingInvolution

/-!
# The complete real small-block decomposition at Schatten transport minima

All positive gradient levels, including the maximal level, contribute
balanced real blocks of dimension two or four. The actual zero-gradient
space contributes real lines and planes. Their finite union is orthogonal
and spans the original real space. Each block preserves the actual real
transporter and source projection; the exceptional zero blocks are retained
explicitly rather than assigned an unwarranted source-rank balance.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition

open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open RealTransport
open scoped ENNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

local notation "𝓔" => RealComplexification E

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem signed_eigenspaces_isOrtho
    (A : 𝓔 →ₗ[ℂ] 𝓔) (hA : A.IsSymmetric) (g h : ℝ)
    (hg : 0 ≤ g) (hh : 0 ≤ h) (hne : g ≠ h) :
    ((Module.End.eigenspace A (g : ℂ)) ⊔ Module.End.eigenspace A (-g : ℂ)).IsOrtho
      ((Module.End.eigenspace A (h : ℂ)) ⊔ Module.End.eigenspace A (-h : ℂ)) := by
  have horth (a b : ℂ) (hab : a ≠ b) :
      (Module.End.eigenspace A a).IsOrtho (Module.End.eigenspace A b) := by
    rw [Submodule.isOrtho_iff_inner_eq]
    intro x hx y hy
    exact hA.orthogonalFamily_eigenspaces hab ⟨x, hx⟩ ⟨y, hy⟩
  have hneq (a b : ℝ) (hab : a ≠ b) : (a : ℂ) ≠ (b : ℂ) :=
    fun heq => hab (Complex.ofReal_injective heq)
  rw [Submodule.isOrtho_sup_left, Submodule.isOrtho_sup_right,
    Submodule.isOrtho_sup_right]
  refine ⟨⟨horth _ _ (hneq g h hne), horth _ _ ?_⟩,
    ⟨horth _ _ ?_, horth _ _ ?_⟩⟩
  · simpa only [Complex.ofReal_neg] using hneq g (-h) (by intro heq; apply hne; linarith)
  · simpa only [Complex.ofReal_neg] using hneq (-g) h (by intro heq; apply hne; linarith)
  · simpa only [Complex.ofReal_neg] using hneq (-g) (-h) (by intro heq; apply hne; linarith)

/-- Every actual real constrained local Schatten minimum has a complete
orthogonal decomposition into reducing real blocks of dimensions at most
four. Nonzero-gradient blocks have source rank exactly half their dimension;
zero-gradient blocks have dimension at most two and are explicitly tagged.
No principal-plane or nondegeneracy assumption is imposed on the ambient
transporter or projection pair. This is a decomposition theorem, not a
claim that real local minima are global. -/
theorem exists_complete_real_blocks_of_isLocalMinOn_real_transports
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K : Submodule ℂ 𝓔) [K.HasOrthogonalProjection]
    (hK : conjugateOperator K.starProjection = K.starProjection)
    (Q : 𝓔 →L[ℂ] 𝓔) (U : unitary (𝓔 →L[ℂ] 𝓔))
    (hU : conjugateOperator (U : 𝓔 →L[ℂ] 𝓔) = U)
    (htrans : (U : 𝓔 →L[ℂ] 𝓔) * K.starProjection * star (U : 𝓔 →L[ℂ] 𝓔) = Q)
    (hmin : IsLocalMinOn
      (fun W : 𝓔 →L[ℂ] 𝓔 => UnitarilyInvariantSeminorm.schatten ℂ 𝓔 𝓔 p
        (LinearMap.id - W.toLinearMap) ^ p.toReal)
      {W | W ∈ unitary (𝓔 →L[ℂ] 𝓔) ∧ W * K.starProjection * star W = Q ∧
        conjugateOperator W = W} (U : 𝓔 →L[ℂ] 𝓔)) :
    let G := schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)
    ∃ H : Finset (Submodule ℝ E),
      (∀ N ∈ H, N ≠ ⊥ ∧ Module.finrank ℝ N ≤ 4 ∧
        (∀ x ∈ N, realify K.starProjection x ∈ N) ∧
        (∀ x ∈ N, realify (U : 𝓔 →L[ℂ] 𝓔) x ∈ N) ∧
        (((Module.finrank ℝ N = 2 ∧ Module.finrank ℝ ↥(N ⊓ realSubmodule K) = 1) ∨
          (Module.finrank ℝ N = 4 ∧ Module.finrank ℝ ↥(N ⊓ realSubmodule K) = 2)) ∨
          (Module.finrank ℝ N ≤ 2 ∧ complexifySubmodule N ≤ G.toLinearMap.ker))) ∧
      (H : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧ H.sup id = ⊤ := by
  classical
  let G := schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)
  have hG : G.toLinearMap.IsSymmetric :=
    (isSelfAdjoint_schattenUnitaryGradient p.toReal (U : 𝓔 →L[ℂ] 𝓔)).isSymmetric
  have hP : IsStarProjection K.starProjection :=
    ⟨K.isIdempotentElem_starProjection, isSelfAdjoint_starProjection K⟩
  have hconj := gradient_reflection_conjugate_eq_neg_of_isLocalMinOn_real_transports
    p hp hp1 K.starProjection Q hP hK U hU htrans hmin
  have hR : (K.reflection : 𝓔 →L[ℂ] 𝓔) = (2 : ℂ) • K.starProjection - 1 := by
    simpa only [ofNat_smul_eq_nsmul] using Submodule.coe_reflection K
  rw [← hR] at hconj
  have hGR (x : 𝓔) : G (K.reflection x) = -K.reflection (G x) := by
    have h := congrArg (fun T : 𝓔 →L[ℂ] 𝓔 => T (K.reflection x)) hconj
    change K.reflection (G (K.reflection (K.reflection x))) = -G (K.reflection x) at h
    rw [K.reflection_reflection] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  let D (g : ℝ) : Submodule ℂ 𝓔 :=
    Module.End.eigenspace G.toLinearMap (g : ℂ) ⊔
      (Module.End.eigenspace G.toLinearMap (g : ℂ)).map K.reflection.toLinearMap
  have hD (g : ℝ) : D g =
      Module.End.eigenspace G.toLinearMap (g : ℂ) ⊔
        Module.End.eigenspace G.toLinearMap (-g : ℂ) := by
    dsimp only [D]
    rw [map_eigenspace_involution_eq K.reflection K.reflection_involutive
      G.toLinearMap hGR]
  let I := {mu : Module.End.Eigenvalues G.toLinearMap // 0 < mu.val.re}
  let g (i : I) : ℝ := i.val.val.re
  have hg (i : I) : 0 < g i := i.property
  have hreal (i : I) : (g i : ℂ) = i.val.val :=
    RCLike.conj_eq_iff_re.mp (hG.conj_eigenvalue_eq_self i.val.property)
  have hlevel (i : I) :
      ∃ H : Finset (Submodule ℝ E),
        (∀ N ∈ H, N ≠ ⊥ ∧ Module.finrank ℝ N ≤ 4 ∧
          (∀ x ∈ N, realify (U : 𝓔 →L[ℂ] 𝓔) x ∈ N) ∧
          (∀ x ∈ N, realify (K.reflection : 𝓔 →L[ℂ] 𝓔) x ∈ N) ∧
          ((Module.finrank ℝ N = 2 ∧ Module.finrank ℝ ↥(N ⊓ realSubmodule K) = 1) ∨
            (Module.finrank ℝ N = 4 ∧ Module.finrank ℝ ↥(N ⊓ realSubmodule K) = 2))) ∧
        (H : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧
        complexifySubmodule (H.sup id) = D (g i) := by
    have hspec : (g i : ℂ) ∈ spectrum ℂ G := by
      rw [ContinuousLinearMap.spectrum_eq, hreal]
      exact Module.End.hasEigenvalue_iff_mem_spectrum.mp i.val.property
    have hbound := positive_gradient_spectrum_le_max p.toReal (g i) hp1 hp2 (hg i) U hspec
    obtain ⟨V, J, F, hV, hJ, hJx, hF, hpair, hspan, H, hH, horth, hcover⟩ :=
      gradient_eigenspace_small_blocks_of_isLocalMinOn_real_transports
        p hp hp1 hp2 K hK Q U hU htrans hmin (g i) (hg i) hbound
    exact ⟨H, hH, horth, hcover⟩
  choose H hH horth hcover using hlevel
  obtain ⟨Z, hZ, hZorth, hZcover⟩ :=
    gradient_kernel_real_blocks_of_isLocalMinOn_real_transports
      p hp hp1 K hK Q U hU htrans hmin
  let T := Z ∪ Finset.univ.biUnion H
  have hsubZ (N) (hN : N ∈ Z) : N ≤ realSubmodule G.toLinearMap.ker := by
    have hle : N ≤ Z.sup id := Finset.le_sup (f := id) hN
    have heq := congrArg realSubmodule hZcover
    rw [realSubmodule_complexifySubmodule] at heq
    exact heq ▸ hle
  have hsubH (i : I) (N) (hN : N ∈ H i) : N ≤ realSubmodule (D (g i)) := by
    have hle : N ≤ (H i).sup id := Finset.le_sup (f := id) hN
    have heq := congrArg realSubmodule (hcover i)
    rw [realSubmodule_complexifySubmodule] at heq
    exact heq ▸ hle
  have horthZH (i : I) :
      (realSubmodule G.toLinearMap.ker).IsOrtho (realSubmodule (D (g i))) := by
    apply realSubmodule_isOrtho
    have h := signed_eigenspaces_isOrtho G.toLinearMap hG 0 (g i) le_rfl (hg i).le
      (by linarith [hg i])
    simpa only [hD, Complex.ofReal_zero, neg_zero, Module.End.eigenspace_zero,
      sup_idem] using h
  have horthHH (i j : I) (hne : i ≠ j) :
      (realSubmodule (D (g i))).IsOrtho (realSubmodule (D (g j))) := by
    apply realSubmodule_isOrtho
    rw [hD, hD]
    apply signed_eigenspaces_isOrtho G.toLinearMap hG _ _ (hg i).le (hg j).le
    intro heq
    apply hne
    apply Subtype.ext
    apply Subtype.ext
    exact (hreal i).symm.trans ((congrArg (fun r : ℝ => (r : ℂ)) heq).trans (hreal j))
  have hZT : ∀ N ∈ Z, N ∈ T := fun N hN => Finset.mem_union_left _ hN
  have hHT : ∀ i N, N ∈ H i → N ∈ T := by
    intro i N hN
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hN⟩)
  refine ⟨T, ?_, ?_, ?_⟩
  · intro N hN
    rcases Finset.mem_union.mp hN with hNZ | hNH
    · obtain ⟨hN0, hNdim, hPN, hUN⟩ := hZ N hNZ
      refine ⟨hN0, by omega, hPN, hUN, Or.inr ⟨hNdim, ?_⟩⟩
      intro z hz
      obtain ⟨hr, hi⟩ := mem_complexifySubmodule.mp hz
      have hrker := hsubZ N hNZ hr
      have hiker := hsubZ N hNZ hi
      rw [eq_ofReal_add_I_smul_ofReal z]
      exact G.toLinearMap.ker.add_mem hrker (G.toLinearMap.ker.smul_mem _ hiker)
    · obtain ⟨i, _, hNi⟩ := Finset.mem_biUnion.mp hNH
      obtain ⟨hN0, hNdim, hUN, hRN, hbalance⟩ := hH i N hNi
      refine ⟨hN0, hNdim, ?_, hUN, Or.inl hbalance⟩
      intro x hx
      have hPx : realify K.starProjection x = (1/2 : ℝ) •
          (realify (K.reflection : 𝓔 →L[ℂ] 𝓔) x + x) := by
        have h := congrArg (fun A : 𝓔 →L[ℂ] 𝓔 => re (A (ofReal x))) hR
        change realify (K.reflection : 𝓔 →L[ℂ] 𝓔) x =
          re ((2 : ℂ) • K.starProjection (ofReal x) - ofReal x) at h
        rw [re_sub, re_complex_smul, show Complex.re (2 : ℂ) = 2 by rfl,
          show Complex.im (2 : ℂ) = 0 by rfl, zero_smul, sub_zero, re_ofReal] at h
        change realify (K.reflection : 𝓔 →L[ℂ] 𝓔) x =
          (2 : ℝ) • realify K.starProjection x - x at h
        rw [h]
        module
      rw [hPx]
      exact N.smul_mem _ (N.add_mem (hRN x hx) hx)
  · intro N hN M hM hne
    rcases Finset.mem_union.mp hN with hNZ | hNH <;>
      rcases Finset.mem_union.mp hM with hMZ | hMH
    · exact hZorth hNZ hMZ hne
    · obtain ⟨i, _, hMi⟩ := Finset.mem_biUnion.mp hMH
      exact (horthZH i).mono (hsubZ N hNZ) (hsubH i M hMi)
    · obtain ⟨i, _, hNi⟩ := Finset.mem_biUnion.mp hNH
      exact (horthZH i).symm.mono (hsubH i N hNi) (hsubZ M hMZ)
    · obtain ⟨i, _, hNi⟩ := Finset.mem_biUnion.mp hNH
      obtain ⟨j, _, hMj⟩ := Finset.mem_biUnion.mp hMH
      by_cases hij : i = j
      · subst j
        exact horth i hNi hMj hne
      · exact (horthHH i j hij).mono (hsubH i N hNi) (hsubH j M hMj)
  · let W := complexifySubmodule (T.sup id)
    have hZM : G.toLinearMap.ker ≤ W := by
      rw [← hZcover]
      intro z hz
      obtain ⟨hr, hi⟩ := mem_complexifySubmodule.mp hz
      have hZT' : Z.sup id ≤ T.sup id := by
        apply Finset.sup_le
        intro N hN
        exact Finset.le_sup (f := id) (hZT N hN)
      exact mem_complexifySubmodule.mpr ⟨hZT' hr, hZT' hi⟩
    have hDM (r : ℝ) (hr : 0 < r) : D r ≤ W := by
      by_cases heigen : Module.End.HasEigenvalue G.toLinearMap (r : ℂ)
      · let i : I := ⟨⟨(r : ℂ), heigen⟩, by simpa using hr⟩
        have hgi : g i = r := by simp [g, i]
        rw [← hgi, ← hcover i]
        intro z hz
        obtain ⟨hre, him⟩ := mem_complexifySubmodule.mp hz
        have hHT' : (H i).sup id ≤ T.sup id := by
          apply Finset.sup_le
          intro N hN
          exact Finset.le_sup (f := id) (hHT i N hN)
        exact mem_complexifySubmodule.mpr ⟨hHT' hre, hHT' him⟩
      · have hzero : Module.End.eigenspace G.toLinearMap (r : ℂ) = ⊥ := by
          simpa only [Module.End.hasEigenvalue_iff, not_not] using heigen
        simp only [D, hzero, Submodule.map_bot, sup_bot_eq, bot_le]
    have hfull : W = ⊤ := by
      have hspan : (⨆ mu : Module.End.Eigenvalues G.toLinearMap,
          Module.End.eigenspace G.toLinearMap mu.val) = ⊤ :=
        Submodule.orthogonal_eq_bot_iff.mp hG.orthogonalComplement_iSup_eigenspaces_eq_bot'
      apply top_unique
      rw [← hspan]
      apply iSup_le
      intro mu
      have hmu : (mu.val.re : ℂ) = mu.val :=
        RCLike.conj_eq_iff_re.mp (hG.conj_eigenvalue_eq_self mu.property)
      rw [← hmu]
      rcases lt_trichotomy 0 mu.val.re with hpos | hzero | hneg
      · exact le_trans le_sup_left (hDM _ hpos)
      · rw [← hzero, Complex.ofReal_zero, Module.End.eigenspace_zero]
        exact hZM
      · have hnegpos : 0 < -mu.val.re := by linarith
        have hpair : Module.End.eigenspace G.toLinearMap (mu.val.re : ℂ) ≤
            D (-mu.val.re) := by
          rw [hD]
          simpa only [Complex.ofReal_neg, neg_neg] using
            (show Module.End.eigenspace G.toLinearMap (-(-mu.val.re) : ℂ) ≤
              Module.End.eigenspace G.toLinearMap (-mu.val.re : ℂ) ⊔
                Module.End.eigenspace G.toLinearMap (-(-mu.val.re) : ℂ) from le_sup_right)
        exact hpair.trans (hDM _ hnegpos)
    apply top_unique
    intro x _
    have hx : ofReal x ∈ W := hfull ▸ Submodule.mem_top
    exact (ofReal_mem_complexifySubmodule_iff (T.sup id) x).mp hx

end TauCeti.DavisKahan.FiniteDimensional.SchattenPhaseTransition
