/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.Ideals.KyFanNorm
import DavisKahan.Sources.DavisKahan1970.Section4Real
import DavisKahan.Sources.DavisKahan1970.Section5
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNormLaws
import DavisKahan.Sylvester.ScalarTransport
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport
import DavisKahan.OperatorIdeal.NormalizedUnitaryInvariantNorm

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Reading the ideal-gauge results at the paper's own unitarily invariant norm

Several results Davis and Kahan state "for every unitary-invariant norm" are
proved here at an arbitrary `KyFanDominantIdealFamily`, and stated source-facing
at an arbitrary `SymmetricNormingFunction`.  The two are different Lean objects,
and a reviewer comparing a Lean statement with the paper is entitled to ask which
one is the printed quantifier.

**Neither is, on its own, and it does not matter, because a bound proved in one
holds in the other.**  Both bridges are theorems here:

* `symmetricNorming_of_kyFanDominant` -- an estimate holding at every
  Fan-dominant ideal gauge holds at every symmetric norming function.  Instantiate
  at the finite Ky Fan gauges, which are such families, to get Ky Fan
  majorization, then apply Fan dominance
  (`SymmetricNormingFunction.mul_gauge_le_of_all_mul_kyFan_le`).
* `kyFanDominant_of_symmetricNorming` -- the converse.  Instantiate at
  `kyFanNormingFunction k`, the Ky Fan gauge presented as a coherent symmetric
  norming function (`Ideals/KyFanNorm.lean`), to get the same majorization, then
  apply the family's own dominance field.

So both quantifiers are equivalent to weak Ky Fan majorization, which is exactly
the criterion the paper's Section 1 states it will use: "Fan dominance is used in
the strong form: `‖K‖ ≤ ‖L‖` for every unitary-invariant norm iff the inequality
holds for every Ky Fan norm."

That equivalence is what makes the source-facing endpoints cover the *printed*
norm class rather than only the Gohberg--Krein symmetrically normed ideals.  A
unitarily invariant norm on `B(H)` such as `T ↦ ‖T‖ + ‖π(T)‖`, with `π` the Calkin
quotient map, agrees with the operator norm on finite-rank operators and so is not
the prefix-supremum extension of any symmetric gauge -- it is *not* a
`SymmetricNormingFunction`.  It is a Fan-dominant ideal family, though, so the
displayed estimates hold in it, by `kyFanDominant_of_symmetricNorming` applied to
the source-facing endpoint.

This module adds no mathematics beyond the two bridges: each endpoint is the
already proved ideal-gauge theorem, read at the source's norm.

## Main results

* `symmetricNorming_of_kyFanDominant` and `kyFanDominant_of_symmetricNorming`;
* `corollary4_1_compact_nonacute_symmetricNorming_complex` and `..._real`;
* `proposition4_3_compact_nonacute_symmetricNorming_complex` and `..._real`;
* `theorem5_2_symmetricNorming_complex` and `theorem5_2_symmetricNorming_real`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Corollary 4.1, Proposition 4.3,
  Theorem 5.2.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan.ExactSinTheta


open TauCeti.DavisKahan
open TauCeti.ApproximationNumber

noncomputable section

universe u v

/-! ## The bridge -/

/-- **Fan dominance turns an ideal-gauge estimate into a source-norm estimate.**

If `d · gauge X ≤ gauge Y` holds in every Fan-dominant unitarily invariant ideal
gauge, then it holds at every normalized unitarily invariant norm in the source's
sense, and `X` lies in that norm's ideal whenever `Y` does.

The proof instantiates the hypothesis at the finite Ky Fan gauges, which are
themselves such families, and then applies Fan dominance. -/
theorem symmetricNorming_of_kyFanDominant
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {X Y : E →L[𝕜] F} {d : ℝ} (hd : 0 < d)
    (hY : N.Mem Y)
    (h : ∀ M : KyFanDominantIdealFamily.{u, v} 𝕜,
      M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y) :
    N.Mem X ∧ d * N.gauge X ≤ N.gauge Y := by
  refine N.mul_gauge_le_of_all_mul_kyFan_le hd hY (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [kyFanApproximationGauge, kyFanApproximationGauge,
      ContinuousLinearMap.kyFanGauge_zero_index,
      ContinuousLinearMap.kyFanGauge_zero_index, mul_zero]
  · have hM := h (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk)
      (KyFanDominantIdealFamily.kyFan_mem k hk Y)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at hM
    exact hM.2

/-- **The converse bridge: a source-norm estimate holds at every Fan-dominant
ideal gauge.**

If `d · N(X) ≤ N(Y)` holds at every normalized unitarily invariant norm in the
source's sense, then it holds at every Fan-dominant unitarily invariant ideal
gauge, and `X` lies in that gauge's ideal whenever `Y` does.

The proof instantiates the hypothesis at `kyFanNormingFunction k`, the Ky Fan
gauge presented as a coherent symmetric norming function; every bounded operator
lies in its ideal, so the hypothesis applies unconditionally and yields Ky Fan
majorization, which is what a Fan-dominant family consumes.

With `symmetricNorming_of_kyFanDominant` this says the two norm quantifiers used
in this development are equivalent: each is weak Ky Fan majorization, the
criterion the paper's Section 1 announces it will use.  In particular a
source-facing endpoint stated over `SymmetricNormingFunction` is not confined to
the symmetrically normed ideals: it delivers the same bound in every unitarily
invariant norm that is Fan dominant, including norms on `B(H)` such as
`‖·‖ + ‖π(·)‖` that no symmetric gauge generates. -/
theorem kyFanDominant_of_symmetricNorming
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (M : KyFanDominantIdealFamily.{u, v} 𝕜) {X Y : E →L[𝕜] F} {d : ℝ} (hd : 0 < d)
    (hY : M.Mem Y)
    (h : ∀ N : SymmetricNormingFunction, N.Mem Y → N.Mem X ∧ d * N.gauge X ≤ N.gauge Y) :
    M.Mem X ∧ d * M.gauge X ≤ M.gauge Y := by
  refine mem_and_scaled_gauge_le_of_all_scaled_kyFan_le M hd hY (fun k => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [kyFanApproximationGauge, kyFanApproximationGauge,
      ContinuousLinearMap.kyFanGauge_zero_index,
      ContinuousLinearMap.kyFanGauge_zero_index, mul_zero]
  · have hN := (h (kyFanNormingFunction k hk) (kyFanNormingFunction_mem k hk Y)).2
    rwa [kyFanNormingFunction_gauge, kyFanNormingFunction_gauge] at hN

/-- **The two norm quantifiers of this development are equivalent.**

Read together, `symmetricNorming_of_kyFanDominant` and
`kyFanDominant_of_symmetricNorming` say that "`d · N(X) ≤ N(Y)` at every source
norming function" and "`d · M(X) ≤ M(Y)` at every Fan-dominant ideal gauge" are the
same assertion, modulo the membership side condition each carries.  Registering
this as a theorem rather than a remark is the point: a reviewer asking which
quantifier is the paper's does not have to choose. -/
theorem symmetricNorming_iff_kyFanDominant
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {X Y : E →L[𝕜] F} {d : ℝ} (hd : 0 < d) :
    (∀ N : SymmetricNormingFunction, N.Mem Y → N.Mem X ∧ d * N.gauge X ≤ N.gauge Y) ↔
      (∀ M : KyFanDominantIdealFamily.{u, v} 𝕜,
        M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y) :=
  ⟨fun h M hY => kyFanDominant_of_symmetricNorming M hd hY h,
    fun h N hY => symmetricNorming_of_kyFanDominant N hd hY (fun M hM => h M hM)⟩

/-! ## Corollary 4.1 and Proposition 4.3 at the source norm -/

section Complex

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, Corollary 4.1, at every source unitarily invariant
norm**: `N((1 − V)P)` is minimized, among unitaries carrying `P H` onto `Q H`, by
the direct rotation.

`corollary4_1_compact_nonacute_complex` is the same statement at an arbitrary
Fan-dominant ideal gauge; this is it read at the paper's norm object, which is the
quantifier the printed corollary uses. -/
theorem corollary4_1_compact_nonacute_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - W) ∘L DavisKahan.projection U)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L DavisKahan.projection U) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
          DavisKahan.projection U) ≤
        N.gauge ((1 - W) ∘L DavisKahan.projection U) := by
  obtain ⟨hmem, hle⟩ := symmetricNorming_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        corollary4_1_compact_nonacute_complex M U V hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

/-- **Davis--Kahan 1970, Proposition 4.3, at every source unitarily invariant
norm**: the squared displacement `N((1 − V⋆)(1 − V))` is minimized by the direct
rotation. -/
theorem proposition4_3_compact_nonacute_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (U V : Submodule ℂ H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℂ]
      DavisKahan.halmosTargetDefect U V)
    (W : H →L[ℂ] H) (hWunitary : W ∈ unitary (H →L[ℂ] H))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) := by
  obtain ⟨hmem, hle⟩ := symmetricNorming_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        proposition4_3_compact_nonacute_idealGauge M U V hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

end Complex

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Davis--Kahan 1970, Corollary 4.1 over `ℝ`, at every source unitarily
invariant norm.** -/
theorem corollary4_1_compact_nonacute_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℝ]
      DavisKahan.halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - W) ∘L DavisKahan.projection U)) :
    N.Mem ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L DavisKahan.projection U) ∧
      N.gauge ((1 - DavisKahan.nonacuteDirectRotation U V J) ∘L
          DavisKahan.projection U) ≤
        N.gauge ((1 - W) ∘L DavisKahan.projection U) := by
  obtain ⟨hmem, hle⟩ := symmetricNorming_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        corollary4_1_compact_nonacute_real U V M hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

/-- **Davis--Kahan 1970, Proposition 4.3 over `ℝ`, at every source unitarily
invariant norm.** -/
theorem proposition4_3_compact_nonacute_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (U V : Submodule ℝ E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (TauCeti.principalSineOperator U V))
    (J : DavisKahan.halmosSourceDefect U V ≃ₗᵢ[ℝ]
      DavisKahan.halmosTargetDefect U V)
    (W : E →L[ℝ] E) (hWunitary : W ∈ unitary (E →L[ℝ] E))
    (hWmap : W * DavisKahan.projection U = DavisKahan.projection V * W)
    (hWmem : N.Mem ((1 - star W) * (1 - W))) :
    N.Mem ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
        (1 - DavisKahan.nonacuteDirectRotation U V J)) ∧
      N.gauge ((1 - star (DavisKahan.nonacuteDirectRotation U V J)) *
          (1 - DavisKahan.nonacuteDirectRotation U V J)) ≤
        N.gauge ((1 - star W) * (1 - W)) := by
  obtain ⟨hmem, hle⟩ := symmetricNorming_of_kyFanDominant N one_pos hWmem
    (fun M hM => by
      obtain ⟨h₁, h₂⟩ :=
        proposition4_3_compact_nonacute_real_idealGauge U V M hcompact J W hWunitary hWmap hM
      exact ⟨h₁, by rw [one_mul]; exact h₂⟩)
  exact ⟨hmem, by rw [one_mul] at hle; exact hle⟩

end Real

/-! ## Theorem 5.2 at the source norm -/

section Sylvester

/-- **Davis--Kahan 1970, Theorem 5.2, at every source unitarily invariant
norm**: for closed self-adjoint `A ≥ c + δ > c ≥ B` and a bounded solution of
`A X = X B + R`, `δ N(X) ≤ N(R)`, and `X` lies in the norm's ideal whenever `R`
does. -/
theorem theorem5_2_symmetricNorming_complex
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℂ] E} {c δ : ℝ} (hδ : 0 < δ)
    (hAlow : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hsyl : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge R :=
  symmetricNorming_of_kyFanDominant N hδ hR
    (fun M hM => theorem5_2 M hA hB hδ hAlow hBhigh hsyl hM)

/-- **Davis--Kahan 1970, Theorem 5.2 over a real Hilbert space, at every source
unitarily invariant norm.**

The real endpoint takes the whole `FormBoundedSylvesterGap`, which is the weaker
separation hypothesis and therefore the stronger theorem: the printed ordered
configuration `A ≥ c + δ > c ≥ B` is its `leftAboveRightBelow` constructor. -/
theorem theorem5_2_symmetricNorming_real
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℝ] E} {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A B δ)
    (hsyl : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge R :=
  symmetricNorming_of_kyFanDominant N hδ hR
    (fun M hM => DavisKahan.Sylvester.davisKahan1970_sylvester_real
      M hA hB hδ hgap hsyl hM)

/-- **Davis--Kahan 1970, Theorem 5.2 over a real Hilbert space, at the printed ordered
separation.**

`A ≥ c + δ > c ≥ B` in the printed form -- one semibound each way -- rather than the
`FormBoundedSylvesterGap` abstraction, which also covers the interval/exterior and reversed
configurations and is therefore a broader hypothesis than Theorem 5.2 prints.

`theorem5_2_symmetricNorming_real` is the general theorem and is not weakened; this is its
instance at the printed hypothesis, and it is what the source row's canonical evidence names.
The complex endpoint `theorem5_2_symmetricNorming_complex` was already in this shape. -/
theorem theorem5_2_orderedGap_symmetricNorming_real
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (N : SymmetricNormingFunction) {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X R : F →L[ℝ] E} {c δ : ℝ} (hδ : 0 < δ)
    (hAlow : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBhigh : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hsyl : TauCeti.LinearPMap.SylvesterEquation A B X R)
    (hR : N.Mem R) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge R :=
  theorem5_2_symmetricNorming_real N hA hB hδ
    (DavisKahan.Sylvester.FormBoundedSylvesterGap.leftAboveRightBelow c hAlow hBhigh) hsyl hR

end Sylvester

/-! ## The source's own norm class

`NormalizedUnitaryInvariantNorm` is the Lean type for the object Davis--Kahan
quantify over in Section 1.  The theorem below is the source's own reduction,
formalized: an estimate established for every `SymmetricNormingFunction` holds
for every normalized unitarily invariant norm.

The route is exactly the one the paper announces at (1.11)-(1.13).  A source norm
is Fan dominant by construction, so it is a `KyFanDominantIdealFamily`; and
`kyFanDominant_of_symmetricNorming` transports an estimate across that class by
instantiating at the Ky Fan gauges.  Nothing analytic is rebuilt here.

This is what lets a source-facing façade quantify over the literal source class
while its proof discharges through the existing machinery in one step. -/

/-- **The Fan-dominance bridge into the source's norm class.**

An estimate `d ‖X‖ ≤ ‖Y‖` proved for every symmetric norming function holds for
every normalized unitarily invariant norm -- which is the class Davis--Kahan
actually quantify over. -/
theorem normalizedUnitaryInvariant_of_symmetricNorming
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜) {X Y : E →L[𝕜] F} {d : ℝ}
    (hd : 0 < d) (hY : N.Mem Y)
    (h : ∀ M : SymmetricNormingFunction, M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y) :
    N.Mem X ∧ d * N.gauge X ≤ N.gauge Y :=
  kyFanDominant_of_symmetricNorming N.toKyFanDominantIdealFamily hd hY h

/-- The converse direction, for completeness: an estimate proved for every
normalized unitarily invariant norm says nothing weaker than one proved for every
Fan-dominant family, provided the family is normalized.

Stated as the projection it is, so a reader can see that the source class sits
*inside* the Fan-dominant one and the façades are therefore genuinely weaker
statements than the theorems that prove them -- which is the point of registering
them separately. -/
theorem normalizedUnitaryInvariant_toKyFanDominant
    {𝕜 : Type u} [RCLike 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (N : NormalizedUnitaryInvariantNorm.{u, v} 𝕜) {X Y : E →L[𝕜] F} {d : ℝ}
    (h : ∀ M : KyFanDominantIdealFamily.{u, v} 𝕜,
      M.Mem Y → M.Mem X ∧ d * M.gauge X ≤ M.gauge Y)
    (hY : N.Mem Y) :
    N.Mem X ∧ d * N.gauge X ≤ N.gauge Y :=
  h N.toKyFanDominantIdealFamily hY

end

end DavisKahan1970
end TauCeti
