/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.Projection.Block
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum

/-!
# Eigenspace pairing by an anticommuting isometric involution

If an isometric involution `J` anticommutes with a linear operator `G`, it
maps the `g`-eigenspace isometrically onto the `-g`-eigenspace. The construction
uses the existing submodule-map isometry and an equality of its image with
the opposite eigenspace. In finite dimension the two multiplicities agree.

This is a classical spectral symmetry. It supplies the pairing step after
constrained Schatten stationarity, and requires neither self-adjointness nor
finite dimensionality until the multiplicity corollary.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Anticommutation with an involution becomes commutation after squaring
the operator. The involution hypothesis is not needed for this identity. -/
theorem commute_square_of_anticommute_isometry
    (J : E ≃ₗᵢ[𝕜] E) (G : E →ₗ[𝕜] E)
    (hanti : ∀ x, G (J x) = -J (G x)) :
    Commute J.toLinearMap (G * G) := by
  ext x
  change J (G (G x)) = G (G (J x))
  rw [hanti, map_neg, hanti, neg_neg]

/-- An anticommuting isometric involution exchanges opposite eigenspaces,
in both directions. -/
theorem involution_mem_eigenspace_neg_iff
    (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J) (G : E →ₗ[𝕜] E)
    (hanti : ∀ x, G (J x) = -J (G x)) (g : 𝕜) (x : E) :
    J x ∈ Module.End.eigenspace G (-g) ↔ x ∈ Module.End.eigenspace G g := by
  have hmap (c : 𝕜) (y : E) (hy : y ∈ Module.End.eigenspace G c) :
      J y ∈ Module.End.eigenspace G (-c) := by
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    rw [hanti, hy, map_smul, neg_smul]
  constructor
  · intro hx
    simpa only [hJ x, neg_neg] using hmap (-g) (J x) hx
  · exact hmap g x

/-- The image of an eigenspace under an anticommuting isometric involution
is exactly the opposite eigenspace. -/
theorem map_eigenspace_involution_eq
    (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J) (G : E →ₗ[𝕜] E)
    (hanti : ∀ x, G (J x) = -J (G x)) (g : 𝕜) :
    (Module.End.eigenspace G g).map J.toLinearMap = Module.End.eigenspace G (-g) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (involution_mem_eigenspace_neg_iff J hJ G hanti g x).2 hx
  · intro hy
    refine ⟨J y, ?_, hJ y⟩
    change J y ∈ Module.End.eigenspace G g
    simpa only [neg_neg] using
      (involution_mem_eigenspace_neg_iff J hJ G hanti (-g) y).2 hy

/-- The isometric pairing of opposite eigenspaces induced by `J`. -/
def eigenspaceNegEquivOfInvolution
    (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J) (G : E →ₗ[𝕜] E)
    (hanti : ∀ x, G (J x) = -J (G x)) (g : 𝕜) :
    Module.End.eigenspace G g ≃ₗᵢ[𝕜] Module.End.eigenspace G (-g) :=
  (LinearIsometryEquiv.submoduleMap (Module.End.eigenspace G g) J).trans
    (LinearIsometryEquiv.ofEq _ _ (map_eigenspace_involution_eq J hJ G hanti g))

/-- The pairing acts by the original involution on vectors. -/
@[simp]
theorem eigenspaceNegEquivOfInvolution_apply
    (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J) (G : E →ₗ[𝕜] E)
    (hanti : ∀ x, G (J x) = -J (G x)) (g : 𝕜) (x : Module.End.eigenspace G g) :
    (eigenspaceNegEquivOfInvolution J hJ G hanti g x : E) = J x := by rfl

/-- Opposite eigenvalues have equal finite multiplicity. -/
theorem finrank_eigenspace_eq_neg_of_involution [FiniteDimensional 𝕜 E]
    (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J) (G : E →ₗ[𝕜] E)
    (hanti : ∀ x, G (J x) = -J (G x)) (g : 𝕜) :
    Module.finrank 𝕜 (Module.End.eigenspace G g) =
      Module.finrank 𝕜 (Module.End.eigenspace G (-g)) :=
  (eigenspaceNegEquivOfInvolution J hJ G hanti g).toLinearEquiv.finrank_eq

/-- An anticommuting isometric involution reverses arbitrary real
point-spectral selections. This includes the positive and negative spaces. -/
theorem map_pointSpectralSubspace_involution_eq
    (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J) (G : Module.End 𝕜 E)
    (hanti : ∀ x, G (J x) = -J (G x)) (s : Set ℝ) :
    (G.pointSpectralSubspace s).map J.toLinearMap =
      G.pointSpectralSubspace {r : ℝ | -r ∈ s} := by
  have hle (s : Set ℝ) : (G.pointSpectralSubspace s).map J.toLinearMap ≤
      G.pointSpectralSubspace {r : ℝ | -r ∈ s} := by
    rw [Module.End.pointSpectralSubspace_eq_iSup, Submodule.map_iSup]
    apply iSup_le
    intro r
    rw [Submodule.map_iSup]
    apply iSup_le
    intro hr
    rw [map_eigenspace_involution_eq J hJ G hanti]
    have hcast : -(r : 𝕜) = ((-r : ℝ) : 𝕜) := (RCLike.ofReal_neg r).symm
    rw [hcast]
    exact Module.End.eigenspace_le_pointSpectralSubspace (by simpa using hr)
  apply le_antisymm (hle s)
  intro y hy
  have hdouble : {r : ℝ | -r ∈ {r : ℝ | -r ∈ s}} = s := by ext r; simp
  have hJy : J y ∈ G.pointSpectralSubspace s := by
    have h := hle {r : ℝ | -r ∈ s} (Submodule.mem_map_of_mem hy)
    rw [hdouble] at h
    change J y ∈ G.pointSpectralSubspace s at h
    exact h
  exact ⟨J y, hJy, hJ y⟩

/-- If reflection across a subspace negates an operator by conjugation,
the square of that operator commutes with the orthogonal projection. -/
theorem commute_square_of_reflection_conjugate_eq_neg
    (G : E →L[𝕜] E) (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (hconj : (K.reflection : E →L[𝕜] E) * G * (K.reflection : E →L[𝕜] E) = -G) :
    Commute K.starProjection (G * G) := by
  have hanti (x : E) : G (K.reflection x) = -K.reflection (G x) := by
    have h := congrArg (fun A : E →L[𝕜] E => A (K.reflection x)) hconj
    change K.reflection (G (K.reflection (K.reflection x))) = -G (K.reflection x) at h
    rw [K.reflection_reflection] at h
    simpa only [neg_neg] using congrArg Neg.neg h.symm
  apply K.commute_reflection_iff.1
  have hcomm := commute_square_of_anticommute_isometry K.reflection G.toLinearMap hanti
  ext x
  exact congrArg (fun A : E →ₗ[𝕜] E => A x) hcomm.eq

end TauCeti
