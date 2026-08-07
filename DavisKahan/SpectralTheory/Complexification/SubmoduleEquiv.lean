/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.SpectralTheory.Complexification.Subspace

/-!
# Complexifying a real subspace commutes with taking the subspace

Every real Davis--Kahan wrapper that has to talk about a *compression* or a
*restriction* runs into the following mismatch.  A real configuration carries a
subspace `Z : Submodule ℝ E` and an operator on `↥Z`.  Complexifying that
operator lands on

  `RealComplexification ↥Z`,

but every complex theorem in this repository that mentions the complexified
subspace speaks about

  `↥(complexifySubmodule Z)`.

These are canonically the same Hilbert space -- both are "pairs of vectors of
`Z`" -- but they are *not* definitionally equal: the first is built by
complexifying the subtype, the second by cutting the complexification down to a
submodule.  Nothing transports between them until the isometry is supplied.

This module supplies it, as `complexifySubmoduleEquiv`, a `ℂ`-linear isometric
equivalence.  Everything is coordinatewise: `re` and `im` are preserved on the
nose (`re_complexifySubmoduleEquiv`, `im_complexifySubmoduleEquiv`), and the
isometry is the two `norm_sq` identities matched against each other.

This is deliberately an *equivalence* rather than an attempt to force
definitional equality.  Downstream only ever needs equality of approximation
singular values, and a unitary conjugation delivers that, so a clean isometry is
both sufficient and much cheaper than fighting subtype coercions extensionally.

It is the shared adapter for two separate open lifts:

* the real `sin 2Θ` theorem stated with spectral hypotheses, whose
  `compressOperator Z A` hypotheses live on `↥Z`; and
* the real `tan Θ` (Theorem 6.3) family, whose trial compression and residual
  both live on the trial subspace.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace Foundation
namespace RealComplexification

open scoped InnerProductSpace
open TauCeti.RealComplexification

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The underlying `ℂ`-linear equivalence between the complexification of a real
subspace and the corresponding submodule of the complexification. -/
noncomputable def complexifySubmoduleLinearEquiv (Z : Submodule ℝ E) :
    RealComplexification Z ≃ₗ[ℂ] complexifySubmodule Z where
  toFun w :=
    ⟨mk ((re w).val) ((im w).val), by
      rw [mem_complexifySubmodule]
      exact ⟨(re w).2, (im w).2⟩⟩
  invFun z :=
    mk ⟨re (z : RealComplexification E),
        ((mem_complexifySubmodule).1 z.2).1⟩
      ⟨im (z : RealComplexification E),
        ((mem_complexifySubmodule).1 z.2).2⟩
  map_add' w w' := by
    apply Subtype.ext
    apply TauCeti.RealComplexification.ext <;> simp
  map_smul' c w := by
    apply Subtype.ext
    apply TauCeti.RealComplexification.ext <;>
      simp [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_add]
  left_inv w := by
    apply TauCeti.RealComplexification.ext <;> apply Subtype.ext <;> simp
  right_inv z := by
    apply Subtype.ext
    apply TauCeti.RealComplexification.ext <;> simp

@[simp] theorem coe_complexifySubmoduleLinearEquiv (Z : Submodule ℝ E)
    (w : RealComplexification Z) :
    ((complexifySubmoduleLinearEquiv Z w : RealComplexification E)) =
      mk ((re w).val) ((im w).val) := rfl

/-- **Complexifying a real subspace commutes with taking the subspace.**  The
complexification of `↥Z` is `ℂ`-linearly isometric to the submodule
`complexifySubmodule Z` of the complexification, coordinatewise. -/
noncomputable def complexifySubmoduleEquiv (Z : Submodule ℝ E) :
    RealComplexification Z ≃ₗᵢ[ℂ] complexifySubmodule Z where
  toLinearEquiv := complexifySubmoduleLinearEquiv Z
  norm_map' w := by
    have hsrc : ‖w‖ ^ 2 = ‖(re w).val‖ ^ 2 + ‖(im w).val‖ ^ 2 := by
      rw [TauCeti.RealComplexification.norm_sq w]
      rfl
    have htgt : ‖complexifySubmoduleLinearEquiv Z w‖ ^ 2 =
        ‖(re w).val‖ ^ 2 + ‖(im w).val‖ ^ 2 := by
      show ‖mk ((re w).val) ((im w).val)‖ ^ 2 = _
      rw [TauCeti.RealComplexification.norm_sq]
      simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (htgt.trans hsrc.symm)

@[simp] theorem coe_complexifySubmoduleEquiv (Z : Submodule ℝ E)
    (w : RealComplexification Z) :
    ((complexifySubmoduleEquiv Z w : RealComplexification E)) =
      mk ((re w).val) ((im w).val) := rfl

/-- The equivalence preserves real coordinates. -/
@[simp] theorem re_complexifySubmoduleEquiv (Z : Submodule ℝ E)
    (w : RealComplexification Z) :
    re ((complexifySubmoduleEquiv Z w : RealComplexification E)) =
      (re w).val := rfl

/-- The equivalence preserves imaginary coordinates. -/
@[simp] theorem im_complexifySubmoduleEquiv (Z : Submodule ℝ E)
    (w : RealComplexification Z) :
    im ((complexifySubmoduleEquiv Z w : RealComplexification E)) =
      (im w).val := rfl

/-- **The adapter is exactly the complexification of the inclusion.**  This is
the compatibility that makes the equivalence useful rather than merely
existent: transporting along it agrees with complexifying `Z.subtypeL`. -/
theorem coe_complexifySubmoduleEquiv_eq_complexify_subtypeL (Z : Submodule ℝ E)
    (w : RealComplexification Z) :
    ((complexifySubmoduleEquiv Z w : RealComplexification E)) =
      complexify Z.subtypeL w :=
  rfl

variable [CompleteSpace E]

/-- **Compressing to a complexified subspace is the complexification of the
compression.**  Stated pointwise through the adapter, so no subtype coercion has
to be pushed through a composition.

This is the transport identity the real Theorem 6.3 wrappers and the spectral
form of the real `sin 2Θ` theorem both need: it says the complex theorem's
`compressOperator (complexifySubmodule Z) (complexify A)` is unitarily conjugate,
via `complexifySubmoduleEquiv`, to the complexification of the real compression
`Z.orthogonalProjectionOnto ∘L A ∘L Z.subtypeL`.  Spectra and approximation
singular values are therefore the same on both sides. -/
theorem orthogonalProjectionOnto_complexify_apply
    (Z : Submodule ℝ E) [Z.HasOrthogonalProjection] (A : E →L[ℝ] E)
    (w : RealComplexification Z) :
    (complexifySubmodule Z).orthogonalProjectionOnto
        ((complexify A) (complexifySubmoduleEquiv Z w)) =
      complexifySubmoduleEquiv Z
        (complexify (Z.orthogonalProjectionOnto ∘L A ∘L Z.subtypeL) w) := by
  apply Subtype.ext
  have hL : ((complexifySubmodule Z).orthogonalProjectionOnto
        ((complexify A) (complexifySubmoduleEquiv Z w)) :
      RealComplexification E) =
      (complexifySubmodule Z).starProjection
        ((complexify A) (complexifySubmoduleEquiv Z w)) := rfl
  rw [hL, starProjection_complexifySubmodule]
  apply TauCeti.RealComplexification.ext <;> rfl

end RealComplexification
end Foundation
end Experimental
end DavisKahan
end TauCeti
