/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.EigenblockSpan
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Geometry
public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
public import TauCeti.Analysis.InnerProductSpace.Spectral.Eigenframe

/-!
# Gap-separated ordered eigenframes

`Module.End.IsEigenfamily` and `LinearMap.IsSymmetric.IsOrderedEigenframe` are
canonical TauCeti declarations, accepted in SSP-D01 (#18942). This module
no longer defines parallel eigenfamily or ordered-frame representations.

It retains exactly the two additional gap-separated facts used in the
Yu--Wang--Samworth population-gap arguments:

* `LinearMap.IsSymmetric.IsOrderedEigenframe.span_eq_spanIndices` says that an
  ordered frame with a population gap spans the canonical eigenvector block;
  its vectors remain arbitrary within repeated eigenspaces.
* `LinearMap.IsSymmetric.IsOrderedEigenframe.pointInternalGap_span` lifts the
  same gap from ordered eigenvalues to the two restricted point spectra.

Neither gap result was included in SSP-D01. The corresponding-block,
restricted-spectrum and dimension interfaces now come directly from TauCeti.
-/

public section

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace

namespace LinearMap.IsSymmetric.IsOrderedEigenframe

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n d : ℕ} {T : E →ₗ[𝕜] E}
variable {hT : T.IsSymmetric} {hn : finrank 𝕜 E = n}
  {e : Fin d ↪ Fin n} {w : Fin d → E}

/-- **A gap-separated ordered eigenframe spans the canonical block.**

If every selected eigenvalue is `Δ`-separated from every unselected one, with
`Δ > 0`, then the eigenvalue of `w i` has *all* of its indices inside
`Set.range e`; so `w i` lies in the corresponding eigenspace, which is the span
of those basis vectors.  A dimension count upgrades the inclusion to equality.

This is why the population side of a population-gap perturbation theorem needs
no choice datum, and — read contrapositively — why the perturbed side does. -/
theorem span_eq_spanIndices (hw : IsOrderedEigenframe hT hn e w) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range e →
      Δ ≤ |hT.eigenvalues hn (e i) - hT.eigenvalues hn k|) :
    Submodule.span 𝕜 (Set.range w) = (hT.eigenvectorBasis hn).spanIndices (Set.range e) := by
  classical
  have hle : Submodule.span 𝕜 (Set.range w) ≤
      (hT.eigenvectorBasis hn).spanIndices (Set.range e) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    -- The level set of `w i`'s eigenvalue sits inside the selected indices.
    have hlevel : {k : Fin n | (hT.eigenvalues hn k : 𝕜) =
        ((hT.eigenvalues hn (e i) : ℝ) : 𝕜)} ⊆ Set.range e := by
      intro k hk
      by_contra hkn
      have hkeq : hT.eigenvalues hn k = hT.eigenvalues hn (e i) := by
        exact_mod_cast hk
      have := hgap i k hkn
      rw [hkeq, sub_self, abs_zero] at this
      exact absurd this (not_le.mpr hΔ)
    have hmem : w i ∈ eigenspace T ((hT.eigenvalues hn (e i) : ℝ) : 𝕜) :=
      Module.End.mem_eigenspace_iff.mpr
        ((isOrderedEigenframe_iff.mp hw).apply_eq i)
    rw [← hT.spanIndices_eigenvalueLevel hn] at hmem
    exact (OrthonormalBasis.spanIndices_mono _ hlevel) hmem
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hdim : finrank 𝕜 (Submodule.span 𝕜 (Set.range w)) = d := by
    simpa only [Fintype.card_fin] using hw.finrank_span
  rw [hdim]
  have hrange : (Set.range e) = ↑(Finset.univ.map e) := by
    ext k; simp
  rw [hrange, OrthonormalBasis.finrank_spanIndices]
  simp

/-- **The intrinsic gap.**  A `Δ`-separated ordered eigenframe spans a subspace
with `PointInternalGap T · Δ`: both the selected and the complementary spectrum are
read off the sorted eigenvalue list, and the index separation is exactly the
hypothesis. -/
theorem pointInternalGap_span (hw : IsOrderedEigenframe hT hn e w) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ (i : Fin d) (k : Fin n), k ∉ Set.range e →
      Δ ≤ |hT.eigenvalues hn (e i) - hT.eigenvalues hn k|) :
    TauCeti.PointInternalGap T (Submodule.span 𝕜 (Set.range w)) Δ := by
  classical
  have hfamily := isOrderedEigenframe_iff.mp hw
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hfamily.map_span_le (Submodule.mem_map_of_mem hx)
  · intro lam μ hlam hμ
    -- The selected side: `lam` is one of the frame's own eigenvalues.
    obtain ⟨i, rfl⟩ := hfamily.restrictedPointSpectrum_span_subset hlam
    -- The complementary side: `Uᗮ` is the span of the unselected basis vectors.
    rw [hw.span_eq_spanIndices hΔ hgap] at hμ
    set S : Finset (Fin n) := Finset.univ.map e with hS
    have hrange : (Set.range e) = (↑S : Set (Fin n)) := by rw [hS]; ext k; simp
    have hcompl : ((↑S : Set (Fin n))ᶜ) = (↑(Sᶜ) : Set (Fin n)) := by ext k; simp
    have hcomplSpan :
        (hT.eigenvectorBasis hn).spanIndices (↑(Sᶜ) : Set (Fin n)) =
          Submodule.span 𝕜
            (Set.range fun k : {x // x ∈ Sᶜ} => hT.eigenvectorBasis hn ↑k) := by
      rw [OrthonormalBasis.spanIndices_eq_span, Set.image_eq_range]
      rfl
    rw [hrange, OrthonormalBasis.orthogonal_spanIndices, hcompl, hcomplSpan] at hμ
    have hcomplFamily : Module.End.IsEigenfamily T
        (fun k : {x // x ∈ Sᶜ} => hT.eigenvalues hn ↑k)
        (fun k : {x // x ∈ Sᶜ} => hT.eigenvectorBasis hn ↑k) :=
      ⟨(hT.eigenvectorBasis hn).orthonormal.comp _ Subtype.val_injective,
        fun k => hT.apply_eigenvectorBasis hn ↑k⟩
    obtain ⟨k, rfl⟩ := hcomplFamily.restrictedPointSpectrum_span_subset hμ
    refine hgap i ↑k ?_
    rw [hrange]
    exact fun hk => (Finset.mem_compl.mp k.2) hk


end LinearMap.IsSymmetric.IsOrderedEigenframe
