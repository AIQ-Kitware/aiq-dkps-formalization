/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.Geometry.Angle.CosineKernel
import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction
import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSchatten
import ForTauCeti.Analysis.InnerProductSpace.NuclearTrace

/-!
# Exact cost splitting across the actual right-angle defect

A feasible unitary preserving the principal cosine restricts to both its
kernel and the orthogonal complement. If it is self-adjoint on the kernel,
the kernel cost is exactly `a * dim(ker C)` for `0 ≤ b ≤ a`. The proof
constructs the actual restrictions and uses reflection anticommutation to
remove their trace term. Real and complex scalars and zero summands are allowed.
-/

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- The right-angle part of a feasible cosine-preserving reflecting
transporter contributes exactly `a * dim(ker C)` to the weighted nuclear
cost. The remaining term is the cost of its actual orthogonal restriction. -/
theorem weighted_transport_split_cosine_kernel
    (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a)
    (K L : Submodule 𝕜 E) (T : E ≃ₗᵢ[𝕜] E) (hT : K.map T.toLinearMap = L)
    (hTC : Commute (T : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L))
    (hself : ∀ x : E, Proposition35.section3CosAngleOperator K L x = 0 →
      T x = star (T : E →L[𝕜] E) x) :
    let N := (Proposition35.section3CosAngleOperator K L).ker
    ∃ (T₀ : N ≃ₗᵢ[𝕜] N) (Tpos : Nᗮ ≃ₗᵢ[𝕜] Nᗮ),
      (∀ x : N, (T₀ x : E) = T x) ∧
      (∀ x : Nᗮ, (Tpos x : E) = T x) ∧
      IsSelfAdjoint (T₀ : N →L[𝕜] N) ∧
      UnitarilyInvariantSeminorm.nuclear 𝕜 E E
          ((a : 𝕜) • T.toLinearMap - (b : 𝕜) • LinearMap.id) =
        UnitarilyInvariantSeminorm.nuclear 𝕜 Nᗮ Nᗮ
            ((a : 𝕜) • Tpos.toLinearMap - (b : 𝕜) • LinearMap.id) +
          a * Module.finrank 𝕜 N := by
  let C := Proposition35.section3CosAngleOperator K L
  let N := C.ker
  have hinv : ∀ x ∈ N, T x ∈ N := by
    intro x hx
    change C x = 0 at hx
    change C (T x) = 0
    have h := DFunLike.congr_fun hTC.eq x
    change T (C x) = C (T x) at h
    rw [hx, map_zero] at h
    exact h.symm
  obtain ⟨T₀, hT₀, hT₀s, hred⟩ :=
    T.exists_restriction_of_finite_invariant N hinv
  have hinvp : ∀ x ∈ Nᗮ, T x ∈ Nᗮ :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem T.toLinearMap).mp
      hred.orthogonal_mem_invtSubmodule
  obtain ⟨Tpos, hTpos, _, _⟩ := T.exists_restriction_of_finite_invariant Nᗮ hinvp
  have hself₀ : IsSelfAdjoint (T₀ : N →L[𝕜] N) := by
    change star (T₀ : N →L[𝕜] N) = (T₀ : N →L[𝕜] N)
    rw [show star (T₀ : N →L[𝕜] N) = (T₀.symm : N →L[𝕜] N) from T₀.adjoint_eq_symm]
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change (T₀.symm x : E) = (T₀ x : E)
    rw [hT₀s, hT₀]
    change (T.symm : E →L[𝕜] E) x = T x
    rw [← T.adjoint_eq_symm]
    exact (hself x x.property).symm
  have hJinv : ∀ x ∈ N, K.reflection x ∈ N := by
    intro x hx
    exact Proposition35.reflection_mem_cosine_kernel K L x hx
  obtain ⟨J₀, hJ₀, _, _⟩ :=
    K.reflection.exists_restriction_of_finite_invariant N hJinv
  have hJJ : Function.Involutive J₀ := by
    intro x
    apply Subtype.ext
    rw [hJ₀, hJ₀, K.reflection_reflection]
  have hanti (x : N) : T₀ (J₀ x) = -J₀ (T₀ x) := by
    apply Subtype.ext
    change (T₀ (J₀ x) : E) = -(J₀ (T₀ x) : E)
    rw [hT₀, hJ₀, hJ₀, hT₀]
    exact Proposition35.transport_anticommutes_reflection_on_cosine_kernel K L T hT hTC x
      x.property
  have htrace := trace_eq_zero_of_anticommute_involution T₀.toLinearMap J₀ hJJ hanti
  have hcost₀ := nuclear_weighted_selfAdjoint_unitary a b hb hab
    (Unitary.linearIsometryEquiv.symm T₀) hself₀
  change UnitarilyInvariantSeminorm.nuclear 𝕜 N N
      ((a : 𝕜) • T₀.toLinearMap - (b : 𝕜) • LinearMap.id) =
    a * Module.finrank 𝕜 N - b * RCLike.re (LinearMap.trace 𝕜 N T₀.toLinearMap) at hcost₀
  rw [htrace, map_zero, mul_zero, sub_zero] at hcost₀
  let A := (a : 𝕜) • T.toLinearMap - (b : 𝕜) • (LinearMap.id : E →ₗ[𝕜] E)
  have hAinv : ∀ x ∈ N, A x ∈ N := by
    intro x hx
    exact N.sub_mem (N.smul_mem _ (hinv x hx)) (N.smul_mem _ hx)
  have hAinvp : ∀ x ∈ Nᗮ, A x ∈ Nᗮ := by
    intro x hx
    exact Nᗮ.sub_mem (Nᗮ.smul_mem _ (hinvp x hx)) (Nᗮ.smul_mem _ hx)
  have hAred : N.IsReducing A := (N.isReducing_iff A).mpr
    ⟨(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mpr hAinv,
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mpr hAinvp⟩
  have hA₀ : A.restrict hAinv =
      (a : 𝕜) • T₀.toLinearMap - (b : 𝕜) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (a : 𝕜) • T x - (b : 𝕜) • (x : E) =
      (a : 𝕜) • (T₀ x : E) - (b : 𝕜) • (x : E)
    rw [hT₀]
  have hApos : A.restrict hAinvp =
      (a : 𝕜) • Tpos.toLinearMap - (b : 𝕜) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (a : 𝕜) • T x - (b : 𝕜) • (x : E) =
      (a : 𝕜) • (Tpos x : E) - (b : 𝕜) • (x : E)
    rw [hTpos]
  have hsplit := nuclear_eq_add_restrict_of_isReducing A N hAred
  change UnitarilyInvariantSeminorm.nuclear 𝕜 E E A =
    UnitarilyInvariantSeminorm.nuclear 𝕜 N N (A.restrict hAinv) +
      UnitarilyInvariantSeminorm.nuclear 𝕜 Nᗮ Nᗮ (A.restrict hAinvp) at hsplit
  rw [hA₀, hApos, hcost₀, add_comm] at hsplit
  exact ⟨T₀, Tpos, hT₀, hTpos, hself₀, hsplit⟩

/-- Reflecting choices on the right-angle kernel do not change the cost
when two feasible cosine-preserving unitaries agree on its complement. -/
theorem weighted_transport_cost_eq_of_eq_on_cosine_kernel_orthogonal
    (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a)
    (K L : Submodule 𝕜 E) (T S : E ≃ₗᵢ[𝕜] E)
    (hT : K.map T.toLinearMap = L) (hS : K.map S.toLinearMap = L)
    (hTC : Commute (T : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L))
    (hSC : Commute (S : E →L[𝕜] E) (Proposition35.section3CosAngleOperator K L))
    (hselfT : ∀ x : E, Proposition35.section3CosAngleOperator K L x = 0 →
      T x = star (T : E →L[𝕜] E) x)
    (hselfS : ∀ x : E, Proposition35.section3CosAngleOperator K L x = 0 →
      S x = star (S : E →L[𝕜] E) x)
    (hagree : ∀ x ∈ (Proposition35.section3CosAngleOperator K L).kerᗮ, T x = S x) :
    UnitarilyInvariantSeminorm.nuclear 𝕜 E E
        ((a : 𝕜) • T.toLinearMap - (b : 𝕜) • LinearMap.id) =
      UnitarilyInvariantSeminorm.nuclear 𝕜 E E
        ((a : 𝕜) • S.toLinearMap - (b : 𝕜) • LinearMap.id) := by
  obtain ⟨_, Tpos, _, hTpos, _, hcostT⟩ :=
    weighted_transport_split_cosine_kernel a b hb hab K L T hT hTC hselfT
  obtain ⟨_, Spos, _, hSpos, _, hcostS⟩ :=
    weighted_transport_split_cosine_kernel a b hb hab K L S hS hSC hselfS
  have heq : Tpos = Spos := by
    ext x
    exact (hTpos x).trans ((hagree x x.property).trans (hSpos x).symm)
  rw [hcostT, hcostS, heq]

end TauCeti.DavisKahan.FiniteDimensional
