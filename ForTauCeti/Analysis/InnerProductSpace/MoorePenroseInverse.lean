/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.InnerProductSpace.MoorePenrose

/-!
# Commutation and factorization through the Moore–Penrose inverse

The construction, Penrose equations, uniqueness, and adjoint compatibility are
provided by TauCeti. This donor retains the self-adjoint commutation theorem
and the kernel-inclusion factorization used by the direct-rotation proofs.

## Provenance

Retained extensions of the Kitware DKPS module introduced at `caa0966`,
originally `ForMathlib.Analysis.InnerProductSpace.MoorePenroseInverse`.
The complete original source is preserved at `e4637c3919ae`.
The accepted construction is `LinearMap.moorePenroseInverse` (TauCeti #13805);
this migration makes no claim of proof descent for that implementation.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **For a self-adjoint map the two Penrose projections agree**: `A A⁺ = A⁺ A`.

Both are the orthogonal projection onto `range A`; algebraically, `A⁺A` is
self-adjoint (fourth Penrose identity) and its adjoint is `A⋆ A⁺⋆ = A A⁺`. -/
theorem comp_moorePenroseInverse_comm_of_isSymmetric {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) :
    A ∘ₗ LinearMap.moorePenroseInverse A = LinearMap.moorePenroseInverse A ∘ₗ A := by
  have h := ((LinearMap.isMoorePenroseInverse_moorePenroseInverse A).isSymmetric_comp').adjoint_eq
  rwa [LinearMap.adjoint_comp, hA.adjoint_eq,
    ← LinearMap.moorePenroseInverse_adjoint, hA.adjoint_eq] at h

/-- **Commutation passes to the Moore--Penrose inverse of a self-adjoint map**:
if `A` is self-adjoint and `B A = A B`, then `B A⁺ = A⁺ B`.

Only `B A = A B` is assumed: because `A⋆ = A`, taking adjoints gives `B⋆ A = A B⋆`
for free, and the two together force `B` to commute with the Penrose projection
`P = A A⁺ = A⁺ A`.  Indeed `P B P = B P` and `P B⋆ P = B⋆ P` hold by the first
Penrose identity alone, and adjoining the second turns it into `P B P = P B`.
With `B P = P B` in hand,
`A⁺ B = A⁺ P B = A⁺ B P = A⁺ B A A⁺ = A⁺ A B A⁺ = P B A⁺ = B P A⁺ = B A⁺`.

Self-adjointness is not decorative: for a general `A`, commuting with `A` alone
does not make `B` commute with `A⁺`. -/
theorem moorePenroseInverse_comm_of_isSymmetric {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hAB : B ∘ₗ A = A ∘ₗ B) :
    B ∘ₗ LinearMap.moorePenroseInverse A = LinearMap.moorePenroseInverse A ∘ₗ B := by
  have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
  have hadjmul : ∀ f g : E →ₗ[𝕜] E,
      LinearMap.adjoint (f * g) = LinearMap.adjoint g * LinearMap.adjoint f :=
    fun f g => LinearMap.adjoint_comp f g
  set G := LinearMap.moorePenroseInverse A with hG
  have h1 : A * G * A = A := by
    have := (LinearMap.isMoorePenroseInverse_moorePenroseInverse A).comp_comp_self
    simpa [hmul, mul_assoc] using this
  have h2 : G * A * G = G := by
    have := (LinearMap.isMoorePenroseInverse_moorePenroseInverse A).comp_comp_self'
    simpa [hmul, mul_assoc] using this
  have hP : A * G = G * A := by
    have := comp_moorePenroseInverse_comm_of_isSymmetric hA
    simpa [hmul] using this
  have hab : B * A = A * B := by simpa [hmul] using hAB
  have hab' : LinearMap.adjoint B * A = A * LinearMap.adjoint B := by
    have h := congrArg LinearMap.adjoint hAB
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, hA.adjoint_eq] at h
    simpa [hmul] using h.symm
  -- Name the Penrose projection so that adjoints do not descend into it.
  obtain ⟨P, hPdef⟩ : ∃ P : E →ₗ[𝕜] E, P = A * G := ⟨_, rfl⟩
  have hPsym : LinearMap.adjoint P = P := by
    have h := ((LinearMap.isMoorePenroseInverse_moorePenroseInverse A).isSymmetric_comp).adjoint_eq
    rw [hPdef]
    simpa [hmul] using h
  -- `P C P = C P` for anything commuting with `A`; only the first Penrose
  -- identity is used.
  have hkey : ∀ C : E →ₗ[𝕜] E, C * A = A * C → P * C * P = C * P := by
    intro C hC
    rw [hPdef]
    calc A * G * C * (A * G)
        = A * (G * (C * A)) * G := by noncomm_ring
      _ = A * (G * (A * C)) * G := by rw [hC]
      _ = A * G * A * (C * G) := by noncomm_ring
      _ = A * (C * G) := by rw [h1]
      _ = (A * C) * G := by noncomm_ring
      _ = (C * A) * G := by rw [hC]
      _ = C * (A * G) := by noncomm_ring
  have hPB : A * G * B = B * (A * G) := by
    have hBstar := hkey (LinearMap.adjoint B) hab'
    have hadj := congrArg LinearMap.adjoint hBstar
    rw [hadjmul, hadjmul, hadjmul, hPsym, LinearMap.adjoint_adjoint] at hadj
    -- `hadj : P * (B * P) = P * B`
    have hleft : P * B * P = P * B := by rw [mul_assoc]; exact hadj
    have := hleft.symm.trans (hkey B hab)
    rw [hPdef] at this
    exact this
  have hfinal : G * B = B * G := by
    calc G * B = (G * A * G) * B := by rw [h2]
      _ = G * (A * G * B) := by noncomm_ring
      _ = G * (B * (A * G)) := by rw [hPB]
      _ = G * (B * A) * G := by noncomm_ring
      _ = G * (A * B) * G := by rw [hab]
      _ = (G * A) * B * G := by noncomm_ring
      _ = (A * G) * B * G := by rw [hP]
      _ = (A * G * B) * G := by noncomm_ring
      _ = (B * (A * G)) * G := by rw [hPB]
      _ = B * ((G * A) * G) := by rw [hP]; noncomm_ring
      _ = B * G := by rw [h2]
  simpa [hmul] using hfinal.symm

/-- A map that vanishes on `ker A` factors through the initial projection
`A⁺ A`.  This is the finite-dimensional form of the universal property of the
Moore--Penrose initial projection and is the useful orientation for angular
factorizations. -/
theorem comp_moorePenroseInverse_comp_eq_of_ker_le
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G]
    (A : E →ₗ[𝕜] F) (B : E →ₗ[𝕜] G) (hker : A.ker ≤ B.ker) :
    B ∘ₗ LinearMap.moorePenroseInverse A ∘ₗ A = B := by
  ext x
  have hx : x - A.moorePenroseInverse (A x) ∈ A.ker := by
    rw [LinearMap.mem_ker, map_sub,
      (LinearMap.isMoorePenroseInverse_moorePenroseInverse A).apply_apply_apply, sub_self]
  have hBx := LinearMap.mem_ker.mp (hker hx)
  rw [map_sub, sub_eq_zero] at hBx
  exact hBx.symm

end TauCeti
