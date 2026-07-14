/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Sylvester.SpectralDistance
import DavisKahan.Experimental.InfiniteDimensional.Core.Compatibility

/-!
# Compatibility bridges for the historical continuous-linear-map API
-/

namespace ForMathlib
namespace DavisKahanExt

open DavisKahan

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Finite-dimensional rectangular unitarily invariant Sylvester estimate.

For self-adjoint `A` and `B` with spectra separated by `d > 0`, every
rectangular unitarily invariant seminorm satisfies
`d * N X ≤ (π / 2) * N C` whenever `A X - X B = C`.

All reciprocal-multiplier analysis, including the sharp `π / 2` constant,
is supplied unconditionally by the Haagerup--Zsidó kernel through
`DavisKahanTheory.kyFan_reciprocalMultiplier_le`.  Coordinate expansion,
singular-value control, the orbit barycenter, and this
continuous-linear-map bridge contain no further analytic argument.-/
theorem ideal_sylvester_le
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (N : DavisKahanTheory.RectangularUnitarilyInvariantNorm 𝕜 E F)
    {A : F →L[𝕜] F} {B : E →L[𝕜] E} {X C : E →L[𝕜] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * N X.toLinearMap ≤ (Real.pi / 2) * N C.toLinearMap := by
  let A' : F →ₗ[𝕜] F := A.toLinearMap
  let B' : E →ₗ[𝕜] E := B.toLinearMap
  let X' : E →ₗ[𝕜] F := X.toLinearMap
  let C' : E →ₗ[𝕜] F := C.toLinearMap
  have hA' : A'.IsSymmetric := by
    intro x y
    exact hA x y
  have hB' : B'.IsSymmetric := by
    intro x y
    exact hB x y
  have hsep' : DavisKahanTheory.SpectraSeparated A' ⊤ B' ⊤ d := by
    intro a b ha hb
    rcases ha with ⟨x, -, ⟨hx0, hxeig⟩⟩
    rcases hb with ⟨y, -, ⟨hy0, hyeig⟩⟩
    exact hsep a ⟨x, Submodule.mem_top, hx0, hxeig⟩
      b ⟨y, Submodule.mem_top, hy0, hyeig⟩
  have hEq' : A' ∘ₗ X' - X' ∘ₗ B' = C' := by
    ext x
    have hpoint := congrArg (fun T : E →L[𝕜] F => T x) hEq
    change A (X x) - X (B x) = C x at hpoint
    simpa [A', B', X', C'] using hpoint
  simpa [X', C'] using
    DavisKahanTheory.uiNorm_sylvester_le_of_spectralDistance
      N hA' hB' hd hsep' hEq'

/-- **Unconditional complex sharp Sylvester estimate.**  Identical to
`ideal_sylvester_le` at `𝕜 = ℂ`, but proved through the explicit
Haagerup--Zsidó kernel with no open obligation. -/
theorem ideal_sylvester_le_complex
    {EC FC : Type*}
    [NormedAddCommGroup EC] [InnerProductSpace ℂ EC] [FiniteDimensional ℂ EC]
    [NormedAddCommGroup FC] [InnerProductSpace ℂ FC] [FiniteDimensional ℂ FC]
    (N : DavisKahanTheory.RectangularUnitarilyInvariantNorm ℂ EC FC)
    {A : FC →L[ℂ] FC} {B : EC →L[ℂ] EC} {X C : EC →L[ℂ] FC}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * N X.toLinearMap ≤ (Real.pi / 2) * N C.toLinearMap := by
  let A' : FC →ₗ[ℂ] FC := A.toLinearMap
  let B' : EC →ₗ[ℂ] EC := B.toLinearMap
  let X' : EC →ₗ[ℂ] FC := X.toLinearMap
  let C' : EC →ₗ[ℂ] FC := C.toLinearMap
  have hA' : A'.IsSymmetric := by
    intro x y
    exact hA x y
  have hB' : B'.IsSymmetric := by
    intro x y
    exact hB x y
  have hsep' : DavisKahanTheory.SpectraSeparated A' ⊤ B' ⊤ d := by
    intro a b ha hb
    rcases ha with ⟨x, -, ⟨hx0, hxeig⟩⟩
    rcases hb with ⟨y, -, ⟨hy0, hyeig⟩⟩
    exact hsep a ⟨x, Submodule.mem_top, hx0, hxeig⟩
      b ⟨y, Submodule.mem_top, hy0, hyeig⟩
  have hEq' : A' ∘ₗ X' - X' ∘ₗ B' = C' := by
    ext x
    have hpoint := congrArg (fun T : EC →L[ℂ] FC => T x) hEq
    change A (X x) - X (B x) = C x at hpoint
    simpa [A', B', X', C'] using hpoint
  simpa [X', C'] using
    DavisKahanTheory.uiNorm_sylvester_le_of_spectralDistance_complex
      N hA' hB' hd hsep' hEq'

/-- **Unconditional real sharp Sylvester estimate.**  Identical to
`ideal_sylvester_le` at `𝕜 = ℝ`, proved through the doubled orthogonal
descent from the explicit Haagerup--Zsidó kernel. -/
theorem ideal_sylvester_le_real
    {ER FR : Type*}
    [NormedAddCommGroup ER] [InnerProductSpace ℝ ER] [FiniteDimensional ℝ ER]
    [NormedAddCommGroup FR] [InnerProductSpace ℝ FR] [FiniteDimensional ℝ FR]
    (N : DavisKahanTheory.RectangularUnitarilyInvariantNorm ℝ ER FR)
    {A : FR →L[ℝ] FR} {B : ER →L[ℝ] ER} {X C : ER →L[ℝ] FR}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) :
    d * N X.toLinearMap ≤ (Real.pi / 2) * N C.toLinearMap := by
  let A' : FR →ₗ[ℝ] FR := A.toLinearMap
  let B' : ER →ₗ[ℝ] ER := B.toLinearMap
  let X' : ER →ₗ[ℝ] FR := X.toLinearMap
  let C' : ER →ₗ[ℝ] FR := C.toLinearMap
  have hA' : A'.IsSymmetric := by
    intro x y
    exact hA x y
  have hB' : B'.IsSymmetric := by
    intro x y
    exact hB x y
  have hsep' : DavisKahanTheory.SpectraSeparated A' ⊤ B' ⊤ d := by
    intro a b ha hb
    rcases ha with ⟨x, -, ⟨hx0, hxeig⟩⟩
    rcases hb with ⟨y, -, ⟨hy0, hyeig⟩⟩
    exact hsep a ⟨x, Submodule.mem_top, hx0, hxeig⟩
      b ⟨y, Submodule.mem_top, hy0, hyeig⟩
  have hEq' : A' ∘ₗ X' - X' ∘ₗ B' = C' := by
    ext x
    have hpoint := congrArg (fun T : ER →L[ℝ] FR => T x) hEq
    change A (X x) - X (B x) = C x at hpoint
    simpa [A', B', X', C'] using hpoint
  simpa [X', C'] using
    DavisKahanTheory.uiNorm_sylvester_le_of_spectralDistance_real
      N hA' hB' hd hsep' hEq'

end DavisKahanExt
end ForMathlib
