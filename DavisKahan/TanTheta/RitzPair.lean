/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.TanTheta.Theorem63UnboundedCompression
import DavisKahan.TanTheta.UnboundedSpectrum

/-!
# The unbounded Ritz pair, and the reducing complement

The most general unbounded tangent theorem asks its caller for four separate
facts tying an `UnboundedCompressionTrialData` to the ambient operator and to the
chosen subspace:

```
(hZA     : ∀ z, ((z : U) : E) ∈ A.domain)
(haction : ∀ z, D.action z = A ⟨_, hZA z⟩)
(hVdom   : ∀ x : A.domain, Vᗮ.starProjection (x : E) ∈ A.domain)
(hVcomm  : ∀ x : A.domain, Vᗮ.starProjection (A x) = A ⟨_, hVdom x⟩)
```

None of that is Davis--Kahan mathematics.  The first two say the compression data
*is* the compression of `A`; the second two say `Vᗮ` reduces `A`.  Both are
properties of ordinary mathematical objects and belong in the objects.

* `UnboundedRitzPair A U` is compression data together with the two facts that
  make it `A`'s Ritz pair on `U`.
* `ReducingComplement A V` is the domain-aware statement that `Vᗮ` reduces `A`.

`UnboundedRitzPair.ofTrialBlock` builds the first from an
`UnboundedTrialBlock`, so a caller who already has the bounded-compression
bundle -- the common case -- constructs nothing by hand.

What deliberately does *not* move into these objects is the mathematics: the
semiboundedness of the compression, the coercivity on the unwanted subspace, and
the crossed-defect condition (3.5) stay hypotheses of the theorem, because they
are what the theorem is about.
-/

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahan.ExactSinTheta TauCeti.DavisKahan.ExactTanTheta
  TauCeti.DavisKahan.TanTheta

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **An unbounded Ritz pair for `A` on the trial subspace `Z`.**

Compression data together with exactly the two facts that make it the Ritz pair
of the ambient operator: the compression's domain sits inside `A`'s domain, and
the compression's ambient action is `A`'s. -/
structure UnboundedRitzPair (A : H →ₗ.[𝕜] H) (Z : Submodule 𝕜 H)
    [Z.HasOrthogonalProjection] [CompleteSpace Z] where
  /-- The compression and residual data. -/
  trial : UnboundedCompressionTrialData Z
  /-- Trial vectors in the compression's domain lie in the ambient domain. -/
  mem_domain : ∀ z : trial.compression.domain, ((z : Z) : H) ∈ A.domain
  /-- The compression's ambient action `A₀ z + R z` is the ambient action. -/
  action_eq : ∀ z : trial.compression.domain,
    trial.action z = A ⟨((z : Z) : H), mem_domain z⟩

/-- **`Vᗮ` reduces `A`, in the domain-aware sense.**

The projection onto `Vᗮ` preserves the domain of `A` and commutes with `A` on
it.  This is the hypothesis the tangent theorems use to move the ambient
operator past the complementary projection. -/
structure ReducingComplement (A : H →ₗ.[𝕜] H) (V : Submodule 𝕜 H)
    [V.HasOrthogonalProjection] where
  /-- The complementary projection preserves the domain. -/
  mapsDomain : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain
  /-- The complementary projection commutes with the operator on the domain. -/
  commutes : ∀ x : A.domain,
    Vᗮ.starProjection (A x) = A ⟨Vᗮ.starProjection ((x : H)), mapsDomain x⟩

namespace UnboundedRitzPair

variable {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H}
  [Z.HasOrthogonalProjection] [CompleteSpace Z]

/-- **Every bounded trial block is an unbounded Ritz pair.**

The common case: the caller holds an `UnboundedTrialBlock`, whose compression is
a bounded self-adjoint operator on the trial subspace and whose residual is the
ambient action's orthogonal part.  Nothing is assumed beyond what that bundle
already carries. -/
noncomputable def ofTrialBlock (D : UnboundedTrialBlock A Z) :
    UnboundedRitzPair A Z where
  trial :=
    { compression := D.operator.toLinearMap.toPMap ⊤
      compression_isSelfAdjoint :=
        TauCeti.DavisKahanExt.ofBounded_isSelfAdjoint _
          ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
            D.operator_selfAdjoint)
      residual := D.residual
      residual_orthogonal := fun z z' =>
        (Submodule.mem_orthogonal' _ _).mp (D.residual_mem_orthogonal z) _ z'.2 }
  mem_domain := fun z => D.domain_le (z : Z).2
  action_eq := fun z => by
    show ((D.operator (z : Z) : Z) : H) + D.residual ((z : Z)) = _
    rw [D.residual_apply]
    abel

/-- The Ritz pair built from a trial block keeps the block's residual. -/
@[simp]
theorem ofTrialBlock_residual (D : UnboundedTrialBlock A Z) :
    (ofTrialBlock D).trial.residual = D.residual := rfl

end UnboundedRitzPair

namespace ReducingComplement

variable {A : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [V.HasOrthogonalProjection]

/-- **A reducing subspace gives a reducing complement.**

`TauCeti.LinearPMap.ReducesSubspace A V` is the repository's generic vocabulary
for "`V` reduces `A`": both projections preserve the domain and both summands are
invariant.  `ReducingComplement` is the single consequence the tangent theorems
consume -- that the complementary projection commutes with `A` on the domain --
and this is the bridge, so a caller who already holds a `ReducesSubspace`, for
instance from a spectral subspace, does not meet a competing reduction
vocabulary. -/
theorem ofReducesSubspace (h : TauCeti.LinearPMap.ReducesSubspace A V) :
    ReducingComplement A V where
  mapsDomain x := h.orthogonalProjection_mem_domain x
  commutes x := by
    have hVdom : V.starProjection ((x : H)) ∈ A.domain := h.projection_mem_domain x
    have hVpdom : Vᗮ.starProjection ((x : H)) ∈ A.domain :=
      h.orthogonalProjection_mem_domain x
    have hsplit :
        (⟨V.starProjection ((x : H)), hVdom⟩ : A.domain)
            + ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ = x := by
      apply Subtype.ext
      show V.starProjection ((x : H)) + Vᗮ.starProjection ((x : H)) = (x : H)
      rw [Submodule.starProjection_orthogonal_apply]
      abel
    have hmap : A x = A ⟨V.starProjection ((x : H)), hVdom⟩
        + A ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ := by
      have hadd := A.map_add (⟨V.starProjection ((x : H)), hVdom⟩ : A.domain)
        ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩
      rwa [hsplit] at hadd
    have hinV : A (⟨V.starProjection ((x : H)), hVdom⟩ : A.domain) ∈ V :=
      h.invariant _ (V.starProjection_apply_mem _)
    have hinVp : A (⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ : A.domain) ∈ Vᗮ :=
      h.orthogonal_invariant _ (Vᗮ.starProjection_apply_mem _)
    rw [hmap, map_add]
    have h0 : Vᗮ.starProjection (A (⟨V.starProjection ((x : H)), hVdom⟩ : A.domain)) = 0 := by
      rw [Submodule.starProjection_orthogonal_apply,
        Submodule.starProjection_eq_self_iff.mpr hinV, sub_self]
    have h1 : Vᗮ.starProjection (A (⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ : A.domain))
        = A ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ :=
      Submodule.starProjection_eq_self_iff.mpr hinVp
    rw [h0, h1, zero_add]

end ReducingComplement

end DavisKahan
end TauCeti
