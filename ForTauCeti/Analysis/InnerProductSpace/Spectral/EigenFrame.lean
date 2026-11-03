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

The gap-separated `span_eq_spanIndices` theorem is now consumed directly from
TauCeti (#26824, DKPS adaptation). This module retains only
`LinearMap.IsSymmetric.IsOrderedEigenframe.pointInternalGap_span`, which lifts
that gap to the local restricted-spectrum predicate used by paper consumers.
The corresponding-block, restricted-spectrum and dimension interfaces also
come directly from TauCeti.
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
