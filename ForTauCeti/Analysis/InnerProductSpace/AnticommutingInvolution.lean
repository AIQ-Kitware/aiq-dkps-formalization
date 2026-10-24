/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
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

section Unitary

variable [CompleteSpace E]

/-- The adjoint of a unitary acts on a unit-circle eigenvector by the
conjugate scalar. This does not require a spectral basis or finite dimension. -/
theorem unitary_star_apply_of_apply_eq_smul
    (U : unitary (E →L[𝕜] E)) (mu : 𝕜) (hmu : ‖mu‖ = 1)
    (x : E) (hx : (U : E →L[𝕜] E) x = mu • x) :
    star (U : E →L[𝕜] E) x = star mu • x := by
  have hmod : star mu * mu = 1 := by
    rw [RCLike.star_def, RCLike.conj_mul, hmu]
    norm_num
  apply (Unitary.linearIsometryEquiv U).injective
  change (U : E →L[𝕜] E) (star (U : E →L[𝕜] E) x) =
    (U : E →L[𝕜] E) (star mu • x)
  rw [map_smul, hx, smul_smul, hmod, one_smul]
  exact congrArg (fun T : E →L[𝕜] E => T x) (Unitary.mul_star_self_of_mem U.property)

/-- Eigenvectors of a unitary at distinct unit-circle eigenvalues are
orthogonal. No finite-dimensional spectral theorem is needed. -/
theorem unitary_eigenvectors_inner_eq_zero_of_ne
    (U : unitary (E →L[𝕜] E)) (mu nu : 𝕜) (hmu : ‖mu‖ = 1) (hne : mu ≠ nu)
    (x y : E) (hx : (U : E →L[𝕜] E) x = mu • x)
    (hy : (U : E →L[𝕜] E) y = nu • y) : inner 𝕜 x y = 0 := by
  have hs := unitary_star_apply_of_apply_eq_smul U mu hmu x hx
  have h := (U : E →L[𝕜] E).adjoint_inner_left y x
  change inner 𝕜 (star (U : E →L[𝕜] E) x) y = inner 𝕜 x ((U : E →L[𝕜] E) y) at h
  rw [hs, hy, inner_smul_left, inner_smul_right] at h
  simp only [RCLike.star_def, RCLike.conj_conj] at h
  by_contra hn
  exact hne (mul_right_cancel₀ hn h)

/-- The real part of a unitary acts on a unit-circle eigenvector by the
real part of its eigenvalue, without a finite-dimensional hypothesis. -/
theorem unitary_real_part_apply_of_apply_eq_smul
    (U : unitary (E →L[𝕜] E)) (C : E →L[𝕜] E)
    (hsum : (U : E →L[𝕜] E) + star (U : E →L[𝕜] E) = C + C)
    (mu : 𝕜) (hmu : ‖mu‖ = 1) (x : E)
    (hx : (U : E →L[𝕜] E) x = mu • x) :
    C x = (RCLike.re mu : 𝕜) • x := by
  apply smul_right_injective E (by norm_num : (2 : 𝕜) ≠ 0)
  change (2 : 𝕜) • C x = (2 : 𝕜) • ((RCLike.re mu : 𝕜) • x)
  calc
    _ = C x + C x := two_smul 𝕜 (C x)
    _ = (U : E →L[𝕜] E) x + star (U : E →L[𝕜] E) x :=
      (congrArg (fun A : E →L[𝕜] E => A x) hsum).symm
    _ = (mu + star mu) • x := by
      rw [hx, unitary_star_apply_of_apply_eq_smul U mu hmu x hx, add_smul]
    _ = _ := by rw [RCLike.star_def, RCLike.add_conj, smul_smul]

/-- An isometric involution reversing a unitary exchanges its conjugate
eigenspaces. -/
theorem map_unitary_eigenspace_involution_eq
    (U : unitary (E →L[𝕜] E)) (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hrev : ∀ x, (U : E →L[𝕜] E) (J x) = J (star (U : E →L[𝕜] E) x))
    (mu : 𝕜) (hmu : ‖mu‖ = 1) :
    (Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap mu).map J.toLinearMap =
      Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (star mu) := by
  have hmap (lam : 𝕜) (hlam : ‖lam‖ = 1) (x : E)
      (hx : x ∈ Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap lam) :
      J x ∈ Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (star lam) := by
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change (U : E →L[𝕜] E) (J x) = star lam • J x
    rw [hrev, unitary_star_apply_of_apply_eq_smul U lam hlam x hx, map_smul]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hmap mu hmu x hx
  · intro hy
    refine ⟨J y, ?_, hJ y⟩
    change J y ∈ Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap mu
    simpa only [star_star] using hmap (star mu) (by simpa only [norm_star] using hmu) y hy

/-- The actual pairing of conjugate unitary eigenspaces is the restriction
of the reversing involution. -/
def unitaryEigenspaceStarEquivOfInvolution
    (U : unitary (E →L[𝕜] E)) (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hrev : ∀ x, (U : E →L[𝕜] E) (J x) = J (star (U : E →L[𝕜] E) x))
    (mu : 𝕜) (hmu : ‖mu‖ = 1) :
    Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap mu ≃ₗᵢ[𝕜]
      Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap (star mu) :=
  (LinearIsometryEquiv.submoduleMap
    (Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap mu) J).trans
      (LinearIsometryEquiv.ofEq _ _ (map_unitary_eigenspace_involution_eq U J hJ hrev mu hmu))

@[simp]
theorem unitaryEigenspaceStarEquivOfInvolution_apply
    (U : unitary (E →L[𝕜] E)) (J : E ≃ₗᵢ[𝕜] E) (hJ : Function.Involutive J)
    (hrev : ∀ x, (U : E →L[𝕜] E) (J x) = J (star (U : E →L[𝕜] E) x))
    (mu : 𝕜) (hmu : ‖mu‖ = 1)
    (x : Module.End.eigenspace (U : E →L[𝕜] E).toLinearMap mu) :
    (unitaryEigenspaceStarEquivOfInvolution U J hJ hrev mu hmu x : E) = J x := by rfl

end Unitary

end TauCeti
