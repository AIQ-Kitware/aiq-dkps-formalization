/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedResidual
import DavisKahan.DoubleAngle.KyFanOrthonormal
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# The unbounded, residual-form `tan 2Θ` theorem at every Ky Fan prefix

`TanTwoThetaUnboundedResidual.lean` proves the unbounded residual `tan 2Θ`
estimate at the operator norm, that is at the Ky Fan prefix `ν = 1`.  This
module proves the prefixes `ν ≥ 2`, on an exact double-angle eigenfamily.

## The route, and why it is the reflection picture

Both proofs start from the same object: the reducing reflection `Z = 2Q - 1` of
the perturbed operator, its even block `C = cos 2Θ` and odd block `S = sin 2Θ`
relative to `𝔛₀ ⊕ 𝔛₁`, and the unbounded Davis--Kahan equation (7.6)

`A (S x) + B (C x) = S (A x) + C (B x)`,   `x ∈ D(A)`,

which is `TauCeti.sylvester_offDiagonalPart_of_mem`.

At the operator norm that equation is paired with a *near-maximiser* of `‖S ·‖`
inside a bounded spectral cutoff, and the leakage term is killed by letting the
near-maximiser improve at a fixed cutoff level.  The device does not survive to
`ν ≥ 2`, because a Ky Fan prefix needs `ν` mutually orthogonal directions rather
than one near-optimal direction.

What replaces it is an exact algebraic cancellation.  Pair (7.6) at `x` with
`S x` rather than with a normalised near-maximiser.  If `S² x = q² x` then

* `Re ⟪A (S x), S x⟫ ≥ b ‖S x‖² = b q²`, because `S x ∈ 𝔛₁ ∩ D(A)`;
* `Re ⟪S (A x), S x⟫ = Re ⟪A x, S² x⟫ = q² Re ⟪A x, x⟫ ≤ a q²`, because `S` is
  self-adjoint and `x` is an eigenvector of `S²`.

**Both unbounded terms are evaluated where the form hypotheses apply directly,
and no residual is ever paired with `A`.**  The coupling between a residual and
a band radius that obstructs the graph-coordinate route does not arise here,
because there is no residual.

## Main results

* `gap_mul_sq_le_paired_of_doubleAngleEigenvector` — equation (7.6) at an exact
  eigenvector of `S²`, with both unbounded terms discharged.
* `doubleAngleEigenvalue_lt_one` — the pole is excluded *for free*: `q < 1`, so
  `cos 2θ ≠ 0`, with no cutoff and no limit.
* `gap_mul_sum_tangent_le_kyFan_of_doubleAngleEigenfamily` — the `ν ≥ 2`
  endpoint `δ ∑ᵢ qᵢ / √(1 - qᵢ²) ≤ 2 · kyFanApproximationGauge n B`.

The four orthonormal systems the Ky Fan step consumes — `xᵢ`, `S xᵢ / qᵢ`,
`C xᵢ / cᵢ` and `C (S xᵢ) / (qᵢ cᵢ)` — are *exactly* orthonormal, which is again
a consequence of the eigenvector relation together with `C² + S² = 1`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Section 7 for the `tan 2Θ`
  theorem and the reflection `Z = 2Q - 1`, equation (7.6) for the block system,
  and the Appendix to Section 6 for the unbounded passage.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators

open TauCeti.DavisKahan.Experimental.ExactSinTheta

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {U : Submodule ℂ H} [U.HasOrthogonalProjection]
variable {A : H →ₗ.[ℂ] H} {B Z : H →L[ℂ] H} {a b τ : ℝ}

/-- The squared length of the odd block at an exact `S²`-eigenvector is the
eigenvalue. -/
theorem norm_sq_offDiagonalPart_of_doubleAngleEigenvector
    (hZsa : IsSelfAdjoint Z) {x : H} (hx1 : ‖x‖ = 1) {q : ℝ}
    (heig : U.offDiagonalPart Z (U.offDiagonalPart Z x) =
      ((q ^ 2 : ℝ) : ℂ) • x) :
    ‖U.offDiagonalPart Z x‖ ^ 2 = q ^ 2 := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have h : ⟪U.offDiagonalPart Z x, U.offDiagonalPart Z x⟫_ℂ =
      ((q ^ 2 : ℝ) : ℂ) := by
    rw [hSsym x (U.offDiagonalPart Z x), heig, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hx1]
    norm_num
  have h2 : ((‖U.offDiagonalPart Z x‖ ^ 2 : ℝ) : ℂ) = ((q ^ 2 : ℝ) : ℂ) := by
    rw [← h, inner_self_eq_norm_sq_to_K]
    norm_cast
  exact_mod_cast h2

/-- **Equation (7.6) at an exact double-angle eigenvector.**

If `x` is a unit vector of the trial subspace lying in `D(A)` and `S² x = q² x`
for the odd block `S = U.offDiagonalPart Z`, then

`δ q² ≤ Re ⟪B x, C (S x)⟫ - Re ⟪B (C x), S x⟫`,   `δ = b - a`.

Both terms on the right are bounded: no norm of `A` occurs anywhere.  The proof
pairs the unbounded Davis--Kahan block equation with `S x` and uses the
eigenvector relation once, to replace `S (S x)` by `q² x`, which is what turns
the second unbounded term into the trial-side form bound. -/
theorem gap_mul_sq_le_paired_of_doubleAngleEigenvector
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    {x : A.domain} (hxU : (x : H) ∈ U) (hx1 : ‖(x : H)‖ = 1) {q : ℝ}
    (heig : U.offDiagonalPart Z (U.offDiagonalPart Z (x : H)) =
      ((q ^ 2 : ℝ) : ℂ) • (x : H)) :
    (b - a) * q ^ 2 ≤
      RCLike.re ⟪B (x : H),
          U.diagonalPart Z (U.offDiagonalPart Z (x : H))⟫_ℂ -
        RCLike.re ⟪B (U.diagonalPart Z (x : H)),
          U.offDiagonalPart Z (x : H)⟫_ℂ := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hSmem : U.offDiagonalPart Z (x : H) ∈ A.domain :=
    TauCeti.mem_domain_offDiagonalPart hred hZdom x
  have hSU : U.offDiagonalPart Z (x : H) ∈ Uᗮ :=
    TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z hxU
  have hnormS : ‖U.offDiagonalPart Z (x : H)‖ ^ 2 = q ^ 2 :=
    norm_sq_offDiagonalPart_of_doubleAngleEigenvector (U := U) hZsa hx1 heig
  have hsyl := TauCeti.sylvester_offDiagonalPart_of_mem hred hB hZdom hZcomm x hxU
  have hpair := congrArg
    (fun w : H => RCLike.re ⟪w, U.offDiagonalPart Z (x : H)⟫_ℂ) hsyl
  simp only [inner_add_left, map_add] at hpair
  have hlow : b * q ^ 2 ≤
      RCLike.re ⟪A ⟨U.offDiagonalPart Z (x : H), hSmem⟩,
        U.offDiagonalPart Z (x : H)⟫_ℂ := by
    have h := hUb ⟨U.offDiagonalPart Z (x : H), hSmem⟩ hSU
    calc b * q ^ 2 = b * ‖U.offDiagonalPart Z (x : H)‖ ^ 2 := by rw [hnormS]
      _ ≤ _ := h
  have hhigh : RCLike.re ⟪U.offDiagonalPart Z (A x),
      U.offDiagonalPart Z (x : H)⟫_ℂ ≤ a * q ^ 2 := by
    have hswap : ⟪U.offDiagonalPart Z (A x), U.offDiagonalPart Z (x : H)⟫_ℂ =
        ((q ^ 2 : ℝ) : ℂ) * ⟪A x, (x : H)⟫_ℂ := by
      rw [hSsym (A x) (U.offDiagonalPart Z (x : H)), heig, inner_smul_right]
    rw [hswap]
    have hx := hUa x hxU
    rw [hx1, one_pow, mul_one] at hx
    rw [← Complex.real_smul, RCLike.smul_re]
    nlinarith [sq_nonneg q, hx]
  have hmove : RCLike.re ⟪U.diagonalPart Z (B (x : H)),
      U.offDiagonalPart Z (x : H)⟫_ℂ =
      RCLike.re ⟪B (x : H),
        U.diagonalPart Z (U.offDiagonalPart Z (x : H))⟫_ℂ := by
    rw [hCsym (B (x : H)) (U.offDiagonalPart Z (x : H))]
  rw [hmove] at hpair
  linarith [hpair, hlow, hhigh]

/-- The two double-angle Pythagoras identities at an exact `S²`-eigenvector:
`‖C x‖² = 1 - q²` and `‖C (S x)‖² = q² (1 - q²)`. -/
theorem norm_sq_diagonalPart_of_doubleAngleEigenvector
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    {x : H} (hxU : x ∈ U) (hx1 : ‖x‖ = 1) {q : ℝ}
    (heig : U.offDiagonalPart Z (U.offDiagonalPart Z x) =
      ((q ^ 2 : ℝ) : ℂ) • x) :
    ‖U.diagonalPart Z x‖ ^ 2 = 1 - q ^ 2 ∧
      ‖U.diagonalPart Z (U.offDiagonalPart Z x)‖ ^ 2 =
        q ^ 2 * (1 - q ^ 2) := by
  have hZnorm : ∀ v : H, ‖Z v‖ = ‖v‖ :=
    TauCeti.norm_apply_of_isSelfAdjoint_of_mul_self hZsa hZ2
  have hSU : U.offDiagonalPart Z x ∈ Uᗮ :=
    TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z hxU
  have hnormS : ‖U.offDiagonalPart Z x‖ ^ 2 = q ^ 2 :=
    norm_sq_offDiagonalPart_of_doubleAngleEigenvector (U := U) hZsa hx1 heig
  have hnormSS : ‖U.offDiagonalPart Z (U.offDiagonalPart Z x)‖ ^ 2 =
      q ^ 2 * q ^ 2 := by
    rw [heig, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg q), hx1, mul_one]
    ring
  refine ⟨?_, ?_⟩
  · have h := TauCeti.norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem
      (U := U) hZnorm hxU
    rw [hx1, one_pow, hnormS] at h
    linarith
  · have h :=
      TauCeti.norm_sq_diagonalPart_add_norm_sq_offDiagonalPart_of_mem_orthogonal
        (U := U) hZnorm hSU
    rw [hnormSS, hnormS] at h
    nlinarith [h]

/-- **The pole is excluded at an exact double-angle eigenvector, for free.**

`q < 1`, so `cos 2θ = √(1 - q²)` is nonzero and the tangent may be formed.  No
cutoff, no limit and no explicit constant are needed: if `q` were `1` then both
even blocks would vanish and equation (7.6) would force `δ ≤ 0`. -/
theorem doubleAngleEigenvalue_lt_one
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    {x : A.domain} (hxU : (x : H) ∈ U) (hx1 : ‖(x : H)‖ = 1) {q : ℝ}
    (hq : 0 < q)
    (heig : U.offDiagonalPart Z (U.offDiagonalPart Z (x : H)) =
      ((q ^ 2 : ℝ) : ℂ) • (x : H)) :
    q < 1 := by
  obtain ⟨hCx, hCSx⟩ := norm_sq_diagonalPart_of_doubleAngleEigenvector
    (U := U) hZsa hZ2 hxU hx1 heig
  by_contra hcon
  have hcon : 1 ≤ q := not_lt.mp hcon
  have hnn := sq_nonneg ‖U.diagonalPart Z (x : H)‖
  have hq1 : q ^ 2 = 1 := by nlinarith [hCx, hnn]
  have hCx0 : U.diagonalPart Z (x : H) = 0 := by
    refine norm_eq_zero.mp ?_
    nlinarith [norm_nonneg (U.diagonalPart Z (x : H)), hCx, hq1]
  have hCSx0 : U.diagonalPart Z (U.offDiagonalPart Z (x : H)) = 0 := by
    refine norm_eq_zero.mp ?_
    nlinarith [norm_nonneg (U.diagonalPart Z (U.offDiagonalPart Z (x : H))),
      hCSx, hq1]
  have hmain := gap_mul_sq_le_paired_of_doubleAngleEigenvector hred hB hZsa
    hZdom hZcomm hUa hUb hxU hx1 heig
  rw [hCx0, hCSx0] at hmain
  simp only [map_zero, inner_zero_right, inner_zero_left, sub_zero] at hmain
  nlinarith [hmain, hq1, hab]

/-- The Gram identities an orthonormal family of exact `S²`-eigenvectors
satisfies.  Everything the Ky Fan step needs is an exact consequence of
`C² + S² = 1` and the eigenvector relation; nothing here is approximate. -/
theorem inner_of_doubleAngleEigenfamily
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) {n : ℕ} (x : Fin n → H)
    (hx : Orthonormal ℂ x) {q : Fin n → ℝ}
    (heig : ∀ i, U.offDiagonalPart Z (U.offDiagonalPart Z (x i)) =
      (((q i) ^ 2 : ℝ) : ℂ) • x i)
    (i j : Fin n) :
    ⟪U.offDiagonalPart Z (x i), U.offDiagonalPart Z (x j)⟫_ℂ =
        (((q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) ∧
      ⟪U.diagonalPart Z (x i), U.diagonalPart Z (x j)⟫_ℂ =
        ((1 - (q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) ∧
      ⟪U.diagonalPart Z (U.offDiagonalPart Z (x i)),
          U.diagonalPart Z (U.offDiagonalPart Z (x j))⟫_ℂ =
        (((q j) ^ 2 * (1 - (q j) ^ 2) : ℝ) : ℂ) *
          (if i = j then (1 : ℂ) else 0) := by
  classical
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hite : ⟪x i, x j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    (orthonormal_iff_ite.mp hx) i j
  have hpyth : ∀ v : H, U.diagonalPart Z (U.diagonalPart Z v) +
      U.offDiagonalPart Z (U.offDiagonalPart Z v) = v := by
    intro v
    have h := TauCeti.diagonalPart_sq_add_offDiagonalPart_sq (U := U) hZ2
    have h2 := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using h2
  have hSS : ⟪U.offDiagonalPart Z (x i), U.offDiagonalPart Z (x j)⟫_ℂ =
      (((q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    rw [hSsym (x i) (U.offDiagonalPart Z (x j)), heig j, inner_smul_right, hite]
  refine ⟨hSS, ?_, ?_⟩
  · have hCC : ⟪U.diagonalPart Z (x i), U.diagonalPart Z (x j)⟫_ℂ =
        ⟪x i, U.diagonalPart Z (U.diagonalPart Z (x j))⟫_ℂ :=
      hCsym (x i) (U.diagonalPart Z (x j))
    have hsplit : U.diagonalPart Z (U.diagonalPart Z (x j)) =
        x j - (((q j) ^ 2 : ℝ) : ℂ) • x j := by
      have h := hpyth (x j)
      rw [heig j] at h
      linear_combination (norm := module) h
    rw [hCC, hsplit, inner_sub_right, inner_smul_right, hite]
    push_cast
    ring
  · have hCC : ⟪U.diagonalPart Z (U.offDiagonalPart Z (x i)),
        U.diagonalPart Z (U.offDiagonalPart Z (x j))⟫_ℂ =
        ⟪U.offDiagonalPart Z (x i),
          U.diagonalPart Z (U.diagonalPart Z
            (U.offDiagonalPart Z (x j)))⟫_ℂ :=
      hCsym _ _
    have hSSS : U.offDiagonalPart Z (U.offDiagonalPart Z
        (U.offDiagonalPart Z (x j))) =
        (((q j) ^ 2 : ℝ) : ℂ) • U.offDiagonalPart Z (x j) := by
      rw [← map_smul, ← heig j]
    have hsplit : U.diagonalPart Z (U.diagonalPart Z
        (U.offDiagonalPart Z (x j))) =
        U.offDiagonalPart Z (x j) -
          (((q j) ^ 2 : ℝ) : ℂ) • U.offDiagonalPart Z (x j) := by
      have h := hpyth (U.offDiagonalPart Z (x j))
      rw [hSSS] at h
      linear_combination (norm := module) h
    rw [hCC, hsplit, inner_sub_right, inner_smul_right, hSS]
    push_cast
    ring

omit [CompleteSpace H] in
/-- Normalising a family whose Gram matrix is `cⱼ²` times the identity gives an
orthonormal family. -/
theorem orthonormal_scaled_of_inner_eq {n : ℕ} {f : Fin n → H}
    {c : Fin n → ℝ} (hc : ∀ i, 0 < c i)
    (h : ∀ i j, ⟪f i, f j⟫_ℂ =
      (((c j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0)) :
    Orthonormal ℂ fun i => (((c i : ℝ) : ℂ)⁻¹ • f i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_smul_left, inner_smul_right, h i j]
  rcases eq_or_ne i j with rfl | hne
  · rw [if_pos rfl, mul_one, ← Complex.ofReal_inv, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_eq_one]
    have hci := (hc i).ne'
    field_simp
  · simp [hne]

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Ky Fan prefix, on an
exact double-angle eigenfamily.**

`A` is a possibly unbounded self-adjoint operator reduced by the trial subspace
`𝔛₀ = U`, the perturbation `B` is bounded and fully off-diagonal (the source's
residual case `H₀ = H₁ = 0`), `Z` is the reducing reflection `2Q - 1` of
`A + B`, the quadratic form of `A` is at most `a` on `𝔛₀` and at least `b` on
`𝔛₁`, and `δ = b - a > 0`.

If `x₀, …, x_{n-1}` is an orthonormal family in `𝔛₀ ∩ D(A)` of exact
eigenvectors of `sin² 2Θ` with eigenvalues `qᵢ² `, `qᵢ > 0`, then

`δ ∑ᵢ tan 2θᵢ ≤ 2 · kyFanApproximationGauge n B`,  `tan 2θᵢ = qᵢ / √(1 - qᵢ²)`.

The constant is the sharp `2` and the right-hand side is the residual, so this
is `δ N(tan 2Θ₀) ≤ 2 N(R)` at every Ky Fan gauge.

Scope, stated honestly.  At `n = 1` this is *weaker* than
`tanTwoTheta_unbounded_residual_opNorm`, which needs no eigenvector: it bounds
`δ ‖sin 2Θ₀ x‖` against `2 ‖B‖ ‖cos 2Θ₀ x‖` at every trial vector.  What is new
here is `n ≥ 2`, which that theorem does not reach at all; the price is the
eigenfamily hypothesis, and removing it is the remaining work. -/
theorem gap_mul_sum_tangent_le_kyFan_of_doubleAngleEigenfamily
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    {n : ℕ} (x : Fin n → A.domain)
    (hxU : ∀ i, ((x i : A.domain) : H) ∈ U)
    (hxon : Orthonormal ℂ fun i => ((x i : A.domain) : H))
    {q : Fin n → ℝ} (hq : ∀ i, 0 < q i)
    (heig : ∀ i, U.offDiagonalPart Z (U.offDiagonalPart Z
        ((x i : A.domain) : H)) =
      (((q i) ^ 2 : ℝ) : ℂ) • ((x i : A.domain) : H)) :
    (b - a) * ∑ i, q i / √(1 - (q i) ^ 2) ≤
      2 * kyFanApproximationGauge n B := by
  classical
  have hx1 : ∀ i, ‖((x i : A.domain) : H)‖ = 1 := fun i => hxon.norm_eq_one i
  have hq1 : ∀ i, q i < 1 := fun i =>
    doubleAngleEigenvalue_lt_one hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab
      (hxU i) (hx1 i) (hq i) (heig i)
  have hc0 : ∀ i, 0 < 1 - (q i) ^ 2 := by
    intro i
    nlinarith [hq i, hq1 i]
  have hcpos : ∀ i, 0 < √(1 - (q i) ^ 2) := fun i => Real.sqrt_pos.mpr (hc0 i)
  have hgram := fun i j => inner_of_doubleAngleEigenfamily (U := U) hZsa hZ2
    (fun i => ((x i : A.domain) : H)) hxon heig i j
  -- the three auxiliary orthonormal systems
  have hyon : Orthonormal ℂ fun i =>
      (((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z ((x i : A.domain) : H)) :=
    orthonormal_scaled_of_inner_eq hq fun i j => (hgram i j).1
  have huon : Orthonormal ℂ fun i =>
      (((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z ((x i : A.domain) : H)) :=
    orthonormal_scaled_of_inner_eq hcpos fun i j => by
      rw [Real.sq_sqrt (hc0 j).le]
      exact (hgram i j).2.1
  have hvon : Orthonormal ℂ fun i =>
      ((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H))) :=
    orthonormal_scaled_of_inner_eq
      (fun i => mul_pos (hq i) (hcpos i)) fun i j => by
        rw [mul_pow, Real.sq_sqrt (hc0 j).le]
        exact (hgram i j).2.2
  have hnegon : Orthonormal ℂ fun i =>
      -(((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z ((x i : A.domain) : H)) := by
    have h := orthonormal_signFlip hyon (fun _ => false)
    simpa using h
  -- the per-index estimate, divided by `qᵢ cᵢ`
  have hstep : ∀ i, (b - a) * (q i / √(1 - (q i) ^ 2)) ≤
      RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((x i : A.domain) : H)⟫_ℂ +
      RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
          U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ := by
    intro i
    have hqc : 0 < q i * √(1 - (q i) ^ 2) := mul_pos (hq i) (hcpos i)
    have hmain := gap_mul_sq_le_paired_of_doubleAngleEigenvector hred hB hZsa
      hZdom hZcomm hUa hUb (hxU i) (hx1 i) (heig i)
    have hterm1 : RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((x i : A.domain) : H)⟫_ℂ =
        (q i * √(1 - (q i) ^ 2))⁻¹ *
          RCLike.re ⟪B ((x i : A.domain) : H),
            U.diagonalPart Z (U.offDiagonalPart Z
              ((x i : A.domain) : H))⟫_ℂ := by
      rw [inner_smul_left, ← Complex.ofReal_inv, Complex.conj_ofReal,
        ← Complex.real_smul, RCLike.smul_re, inner_re_symm]
    have hterm2 : RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
        U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ =
        -((q i * √(1 - (q i) ^ 2))⁻¹ *
          RCLike.re ⟪B (U.diagonalPart Z ((x i : A.domain) : H)),
            U.offDiagonalPart Z ((x i : A.domain) : H)⟫_ℂ) := by
      rw [mul_inv]
      simp only [map_smul, inner_neg_left, inner_smul_left, inner_smul_right,
        ← Complex.ofReal_inv, Complex.conj_ofReal]
      rw [mul_neg, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.real_smul,
        map_neg, RCLike.smul_re, inner_re_symm]
      ring
    rw [hterm1, hterm2]
    have hdiv : (b - a) * (q i / √(1 - (q i) ^ 2)) =
        (q i * √(1 - (q i) ^ 2))⁻¹ * ((b - a) * (q i) ^ 2) := by
      field_simp
    rw [hdiv]
    have hpos : (0 : ℝ) ≤ (q i * √(1 - (q i) ^ 2))⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmain hpos]
  have hsum1 : ∑ i, RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
      U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
      B ((x i : A.domain) : H)⟫_ℂ ≤ kyFanApproximationGauge n B :=
    sum_le_kyFanApproximationGauge_of_orthonormal B hvon hxon (fun _ => le_rfl)
  have hsum2 : ∑ i, RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
      U.offDiagonalPart Z ((x i : A.domain) : H)),
      B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ ≤
      kyFanApproximationGauge n B :=
    sum_le_kyFanApproximationGauge_of_orthonormal B hnegon huon (fun _ => le_rfl)
  calc (b - a) * ∑ i, q i / √(1 - (q i) ^ 2)
      = ∑ i, (b - a) * (q i / √(1 - (q i) ^ 2)) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, (RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((x i : A.domain) : H)⟫_ℂ +
          RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
            U.offDiagonalPart Z ((x i : A.domain) : H)),
            B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
              U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (∑ i, RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((x i : A.domain) : H)⟫_ℂ) +
        ∑ i, RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
          U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
            U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ :=
        Finset.sum_add_distrib
    _ ≤ 2 * kyFanApproximationGauge n B := by linarith [hsum1, hsum2]

/-- A trial-subspace eigenbasis for `sin² 2Θ` realising the Ky Fan prefixes of a
candidate tangent operator.

`T` is the candidate `tan 2Θ₀`; the last clause says its Ky Fan prefix of length
`k` is realised, from below, by an orthonormal family of exact `sin² 2Θ`
eigenvectors inside `𝔛₀ ∩ D(A)`.  This is the only way the tangent's singular
values enter: nothing about `T` beyond its approximation numbers is used. -/
def IsDoubleAngleEigenbasis (A : H →ₗ.[ℂ] H) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (Z T : H →L[ℂ] H) : Prop :=
  ∀ k : ℕ, ∃ (y : Fin k → A.domain) (q : Fin k → ℝ),
    (∀ i, ((y i : A.domain) : H) ∈ U) ∧
      (Orthonormal ℂ fun i => ((y i : A.domain) : H)) ∧
      (∀ i, 0 < q i) ∧
      (∀ i, U.offDiagonalPart Z (U.offDiagonalPart Z ((y i : A.domain) : H)) =
        (((q i) ^ 2 : ℝ) : ℂ) • ((y i : A.domain) : H)) ∧
      kyFanApproximationGauge k T ≤ ∑ i, q i / √(1 - (q i) ^ 2)

/-- **The unbounded residual `tan 2Θ` theorem at every Ky Fan gauge.**

`δ · kyFanApproximationGauge k T ≤ 2 · kyFanApproximationGauge k B` for every
prefix length `k`, whenever `T` is a tangent operator whose prefixes are
realised by exact `sin² 2Θ` eigenfamilies of the trial subspace. -/
theorem gap_mul_kyFan_le_two_mul_kyFan_of_doubleAngleEigenbasis
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : IsDoubleAngleEigenbasis A U Z T) (k : ℕ) :
    (b - a) * kyFanApproximationGauge k T ≤
      2 * kyFanApproximationGauge k B := by
  obtain ⟨y, q, hyU, hyon, hqpos, hyeig, hle⟩ := hT k
  have hmain := gap_mul_sum_tangent_le_kyFan_of_doubleAngleEigenfamily hred hB
    hZsa hZ2 hZdom hZcomm hUa hUb hab y hyU hyon hqpos hyeig
  have hδ : (0 : ℝ) ≤ b - a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hle hδ, hmain]

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Fan-dominant
unitarily invariant ideal gauge.**

`δ N(tan 2Θ₀) ≤ 2 N(R)` in the scaled form the repository uses for sharp
constants: the tangent carries the factor `δ / 2` and is compared with the
residual `B` itself, so no gauge of a scalar multiple of `B` is needed.  Ideal
membership of the scaled tangent is concluded, not assumed. -/
theorem mem_and_gauge_le_of_doubleAngleEigenbasis
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : IsDoubleAngleEigenbasis A U Z T) (hBmem : N.Mem B) :
    N.Mem ((((b - a) / 2 : ℝ) : ℂ) • T) ∧
      N.gauge ((((b - a) / 2 : ℝ) : ℂ) • T) ≤ N.gauge B := by
  refine mem_and_gauge_le_of_all_kyFanApproximationGauge_le N hBmem fun k => ?_
  rw [kyFanApproximationGauge_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b - a) / 2)]
  have h := gap_mul_kyFan_le_two_mul_kyFan_of_doubleAngleEigenbasis hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab hT k
  linarith

/-!
## Approximate double-angle eigenfamilies

Everything above is conditional on an *exact* eigenfamily of `sin² 2Θ` inside
`𝔛₀ ∩ D(A)`, and such a family need not exist: the compressed block
`Ω S² Ω` is a bounded self-adjoint operator and may have empty point spectrum.
What a spectral selection does produce is an *approximate* eigenfamily inside a
bounded cutoff `Ω`, and the results below are the exact-eigenfamily arguments
re-run against one.

Two structural facts make the passage possible and are recorded here because
neither is visible from the exact statements.

* **Only the compressed residual is ever paired with `A`.**  A vector `x` fixed
  by the cutoff has `A x` fixed by the cutoff too, so `⟪A x, S² x⟫ = ⟪A x, Ω S²
  Ω x⟫`.  The defect that has to be small is therefore
  `‖Ω S² Ω x - q² x‖`, not `‖S² x - q² x‖`.
* **Normalisation destroys orthonormality but not contractivity.**  At an exact
  eigenfamily the three systems `S xᵢ / qᵢ`, `C xᵢ / cᵢ` and `C (S xᵢ) / (qᵢ cᵢ)`
  are exactly orthonormal.  At an approximate one they are not, and for the
  third the defect is genuinely *not* controlled by the compressed residual:
  `‖C S g‖² = ‖S g‖² - ‖S² g‖²` and `‖S² g‖ ≥ ‖Ω S² g‖` only one way.  That
  inequality has the favourable sign, so the system is still a contraction, and
  `sum_le_kyFanApproximationGauge_of_contraction` consumes exactly that.
-/

/-- The Gram defect of the odd block at an approximate double-angle
eigenvector: `| ‖S x‖² - q² | ≤ ε`.  Only the *compressed* defect enters,
because `x` is fixed by the cutoff. -/
theorem abs_norm_sq_offDiagonalPart_sub_le_of_approximate
    (hZsa : IsSelfAdjoint Z) (Ω : TauCeti.BoundedCutoff A U τ) {x : H}
    (hxΩ : Ω.toProj x = x) (hx1 : ‖x‖ = 1) {q ε : ℝ}
    (heig : ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x)) -
      ((q ^ 2 : ℝ) : ℂ) • x‖ ≤ ε) :
    |‖U.offDiagonalPart Z x‖ ^ 2 - q ^ 2| ≤ ε := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hΩsym := TauCeti.inner_swap_of_isSelfAdjoint Ω.isSelfAdjoint
  have hd : RCLike.re ⟪x, Ω.toProj (U.offDiagonalPart Z
        (U.offDiagonalPart Z x)) - ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ =
      ‖U.offDiagonalPart Z x‖ ^ 2 - q ^ 2 := by
    have h1 : ⟪x, Ω.toProj (U.offDiagonalPart Z
        (U.offDiagonalPart Z x))⟫_ℂ =
        ⟪U.offDiagonalPart Z x, U.offDiagonalPart Z x⟫_ℂ := by
      rw [← hΩsym x (U.offDiagonalPart Z (U.offDiagonalPart Z x)), hxΩ,
        ← hSsym x (U.offDiagonalPart Z x)]
    rw [inner_sub_right, inner_smul_right, h1, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, hx1]
    simp [← Complex.ofReal_pow]
  calc |‖U.offDiagonalPart Z x‖ ^ 2 - q ^ 2|
      = |RCLike.re ⟪x, Ω.toProj (U.offDiagonalPart Z
          (U.offDiagonalPart Z x)) - ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ| := by rw [hd]
    _ ≤ ‖⟪x, Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x)) -
          ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x)) -
          ((q ^ 2 : ℝ) : ℂ) • x‖ := norm_inner_le_norm _ _
    _ ≤ ε := by rw [hx1, one_mul]; exact heig

/-- **Equation (7.6) at an approximate double-angle eigenvector.**

The exact-eigenvector estimate `gap_mul_sq_le_paired_of_doubleAngleEigenvector`
with the eigenvector relation replaced by the compressed defect bound
`‖Ω S² Ω x - q² x‖ ≤ ε`, at a unit vector `x` fixed by a bounded cutoff of level
`τ`.  The cost is a single additive error `(τ + |b|) ε`:

* `τ ε` from `⟪A x, Ω S² Ω x - q² x⟫`, which is where the unboundedness of `A`
  is met and where the cutoff is used;
* `|b| ε` from replacing `‖S x‖²` by `q²` in the trial-side form bound.

**No norm of `A` occurs**, and no uncompressed residual is ever paired with
`A`. -/
theorem gap_mul_sq_le_paired_of_approximateDoubleAngleEigenvector
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (Ω : TauCeti.BoundedCutoff A U τ) {x : H}
    (hxΩ : Ω.toProj x = x) (hx1 : ‖x‖ = 1) {q ε : ℝ}
    (heig : ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x)) -
      ((q ^ 2 : ℝ) : ℂ) • x‖ ≤ ε) :
    (b - a) * q ^ 2 ≤ (τ + |b|) * ε +
      (RCLike.re ⟪B x, U.diagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ -
        RCLike.re ⟪B (U.diagonalPart Z x), U.offDiagonalPart Z x⟫_ℂ) := by
  classical
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hΩsym := TauCeti.inner_swap_of_isSelfAdjoint Ω.isSelfAdjoint
  have hxdom : x ∈ A.domain := Ω.mem_domain_of_eq hxΩ
  have hxU : x ∈ U := Ω.mem_subspace_of_eq hxΩ
  have hSmem : U.offDiagonalPart Z x ∈ A.domain :=
    TauCeti.mem_domain_offDiagonalPart hred hZdom ⟨x, hxdom⟩
  have hSU : U.offDiagonalPart Z x ∈ Uᗮ :=
    TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z hxU
  have hsyl := TauCeti.sylvester_offDiagonalPart_of_mem hred hB hZdom hZcomm
    ⟨x, hxdom⟩ hxU
  have hpair := congrArg
    (fun w : H => RCLike.re ⟪w, U.offDiagonalPart Z x⟫_ℂ) hsyl
  simp only [inner_add_left, map_add] at hpair
  have hlow : b * ‖U.offDiagonalPart Z x‖ ^ 2 ≤
      RCLike.re ⟪A ⟨U.offDiagonalPart Z x, hSmem⟩, U.offDiagonalPart Z x⟫_ℂ :=
    hUb ⟨U.offDiagonalPart Z x, hSmem⟩ hSU
  have hgram : |‖U.offDiagonalPart Z x‖ ^ 2 - q ^ 2| ≤ ε :=
    abs_norm_sq_offDiagonalPart_sub_le_of_approximate hZsa Ω hxΩ hx1 heig
  have hblow : b * q ^ 2 - |b| * ε ≤ b * ‖U.offDiagonalPart Z x‖ ^ 2 := by
    have hkey : |b * (‖U.offDiagonalPart Z x‖ ^ 2 - q ^ 2)| ≤ |b| * ε := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hgram (abs_nonneg b)
    nlinarith [neg_le_of_abs_le hkey]
  have hAxfix : Ω.toProj (A ⟨x, hxdom⟩) = A ⟨x, hxdom⟩ := by
    have h := Ω.apply_mem_range x
    have hsub : (⟨Ω.toProj x, Ω.mem_domain x⟩ : A.domain) = ⟨x, hxdom⟩ :=
      Subtype.ext hxΩ
    rwa [hsub] at h
  have hAxnorm : ‖A ⟨x, hxdom⟩‖ ≤ τ := by
    have h := Ω.norm_apply_le x
    have hsub : (⟨Ω.toProj x, Ω.mem_domain x⟩ : A.domain) = ⟨x, hxdom⟩ :=
      Subtype.ext hxΩ
    rw [hsub, hxΩ, hx1, mul_one] at h
    exact h
  have hhigh : RCLike.re ⟪U.offDiagonalPart Z (A ⟨x, hxdom⟩),
      U.offDiagonalPart Z x⟫_ℂ ≤ a * q ^ 2 + τ * ε := by
    have h1 : ⟪U.offDiagonalPart Z (A ⟨x, hxdom⟩),
        U.offDiagonalPart Z x⟫_ℂ =
        ⟪A ⟨x, hxdom⟩, U.offDiagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ :=
      hSsym (A ⟨x, hxdom⟩) (U.offDiagonalPart Z x)
    have h2 : ⟪A ⟨x, hxdom⟩,
        U.offDiagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ =
        ⟪A ⟨x, hxdom⟩,
          Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x))⟫_ℂ := by
      rw [← hΩsym (A ⟨x, hxdom⟩)
        (U.offDiagonalPart Z (U.offDiagonalPart Z x)), hAxfix]
    have h3 : ⟪A ⟨x, hxdom⟩,
        Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x))⟫_ℂ =
        ((q ^ 2 : ℝ) : ℂ) * ⟪A ⟨x, hxdom⟩, x⟫_ℂ +
          ⟪A ⟨x, hxdom⟩, Ω.toProj (U.offDiagonalPart Z
            (U.offDiagonalPart Z x)) - ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ := by
      rw [inner_sub_right, inner_smul_right]
      ring
    rw [h1, h2, h3]
    have hform : RCLike.re ⟪A ⟨x, hxdom⟩, x⟫_ℂ ≤ a := by
      have h := hUa ⟨x, hxdom⟩ hxU
      rwa [hx1, one_pow, mul_one] at h
    have hleak : RCLike.re ⟪A ⟨x, hxdom⟩,
        Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z x)) -
          ((q ^ 2 : ℝ) : ℂ) • x⟫_ℂ ≤ τ * ε := by
      refine le_trans (le_abs_self _) ?_
      refine le_trans (Complex.abs_re_le_norm _) ?_
      refine le_trans (norm_inner_le_norm _ _) ?_
      exact mul_le_mul hAxnorm heig (norm_nonneg _)
        (le_trans (norm_nonneg _) hAxnorm)
    rw [map_add, ← Complex.real_smul, RCLike.smul_re]
    nlinarith [hform, hleak, sq_nonneg q]
  have hmove : RCLike.re ⟪U.diagonalPart Z (B x), U.offDiagonalPart Z x⟫_ℂ =
      RCLike.re ⟪B x, U.diagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ := by
    rw [hCsym (B x) (U.offDiagonalPart Z x)]
  linarith [hpair, hlow, hhigh, hblow, hmove]

/-- The double-angle Pythagoras identity at an arbitrary vector: `‖C v‖² =
‖v‖² - ‖S v‖²`, a consequence of `C² + S² = 1` alone. -/
theorem norm_sq_diagonalPart_apply (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (v : H) :
    ‖U.diagonalPart Z v‖ ^ 2 =
      ‖v‖ ^ 2 - ‖U.offDiagonalPart Z v‖ ^ 2 := by
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hpyth : U.diagonalPart Z (U.diagonalPart Z v) +
      U.offDiagonalPart Z (U.offDiagonalPart Z v) = v := by
    have h := TauCeti.diagonalPart_sq_add_offDiagonalPart_sq (U := U) hZ2
    have h2 := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using h2
  have hCC : ⟪U.diagonalPart Z v, U.diagonalPart Z v⟫_ℂ =
      ⟪v, U.diagonalPart Z (U.diagonalPart Z v)⟫_ℂ := hCsym v _
  have hSS : ⟪U.offDiagonalPart Z v, U.offDiagonalPart Z v⟫_ℂ =
      ⟪v, U.offDiagonalPart Z (U.offDiagonalPart Z v)⟫_ℂ := hSsym v _
  have hsum : ⟪U.diagonalPart Z v, U.diagonalPart Z v⟫_ℂ +
      ⟪U.offDiagonalPart Z v, U.offDiagonalPart Z v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [hCC, hSS, ← inner_add_right, hpyth]
  have h := congrArg RCLike.re hsum
  simp only [map_add, inner_self_eq_norm_sq_to_K] at h
  simp [← Complex.ofReal_pow] at h
  linarith

/-- **The compressed Gram estimate on a whole linear combination.**

For an orthonormal family `x` inside the cutoff range with compressed defects
`‖Ω S² Ω xᵢ - qᵢ² xᵢ‖ ≤ ε`, the odd block of `g = ∑ γᵢ xᵢ` satisfies

`| ‖S g‖² - ∑ᵢ |γᵢ|² qᵢ² | ≤ n ε ∑ᵢ |γᵢ|²`.

This is the statement that turns the three normalised systems into contraction
systems, and it is the only place the defect bound is used quantitatively. -/
theorem abs_norm_sq_offDiagonalPart_sum_sub_le
    (hZsa : IsSelfAdjoint Z) (Ω : TauCeti.BoundedCutoff A U τ)
    {n : ℕ} {x : Fin n → H}
    (hx : Orthonormal ℂ x) (hxΩ : ∀ i, Ω.toProj (x i) = x i)
    {q : Fin n → ℝ} {ε : ℝ}
    (heig : ∀ i, ‖Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (x i))) -
      ((q i ^ 2 : ℝ) : ℂ) • x i‖ ≤ ε)
    (γ : Fin n → ℂ) :
    |‖U.offDiagonalPart Z (∑ i, γ i • x i)‖ ^ 2 -
        ∑ i, ‖γ i‖ ^ 2 * q i ^ 2| ≤
      n * ε * ∑ i, ‖γ i‖ ^ 2 := by
  classical
  set g : H := ∑ i, γ i • x i with hgdef
  set d : Fin n → H := fun i =>
    Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z (x i))) -
      ((q i ^ 2 : ℝ) : ℂ) • x i with hddef
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hΩsym := TauCeti.inner_swap_of_isSelfAdjoint Ω.isSelfAdjoint
  have hgΩ : Ω.toProj g = g := by
    rw [hgdef, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hxΩ i]
  have hgnorm : ‖g‖ ^ 2 = ∑ i, ‖γ i‖ ^ 2 :=
    norm_sq_sum_smul_of_orthonormal hx γ
  have hsplit : Ω.toProj (U.offDiagonalPart Z (U.offDiagonalPart Z g)) =
      (∑ i, (γ i * ((q i ^ 2 : ℝ) : ℂ)) • x i) + ∑ i, γ i • d i := by
    rw [hgdef, map_sum, map_sum, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, map_smul, hddef]
    simp only [smul_sub, smul_smul]
    module
  have hDnorm : ‖∑ i, γ i • d i‖ ≤ n * ε * ‖g‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    have hbd : ∀ i : Fin n, ‖γ i • d i‖ ≤ ‖g‖ * ε := by
      intro i
      rw [norm_smul]
      have hγ : ‖γ i‖ ≤ ‖g‖ := by
        have h1 : ‖γ i‖ ^ 2 ≤ ∑ j, ‖γ j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖γ j‖ ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        nlinarith [norm_nonneg (γ i), norm_nonneg g, hgnorm, h1]
      exact mul_le_mul hγ (heig i) (norm_nonneg _) (norm_nonneg g)
    calc ∑ i, ‖γ i • d i‖ ≤ ∑ _i : Fin n, ‖g‖ * ε :=
          Finset.sum_le_sum fun i _ => hbd i
      _ = n * ε * ‖g‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hkey : ‖U.offDiagonalPart Z g‖ ^ 2 =
      RCLike.re ⟪g, Ω.toProj (U.offDiagonalPart Z
        (U.offDiagonalPart Z g))⟫_ℂ := by
    have h1 : ⟪g, Ω.toProj (U.offDiagonalPart Z
        (U.offDiagonalPart Z g))⟫_ℂ =
        ⟪U.offDiagonalPart Z g, U.offDiagonalPart Z g⟫_ℂ := by
      rw [← hΩsym g (U.offDiagonalPart Z (U.offDiagonalPart Z g)), hgΩ,
        ← hSsym g (U.offDiagonalPart Z g)]
    rw [h1, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [hkey, hsplit, inner_add_right, map_add]
  have hmain : RCLike.re ⟪g, ∑ i, (γ i * ((q i ^ 2 : ℝ) : ℂ)) • x i⟫_ℂ =
      ∑ i, ‖γ i‖ ^ 2 * q i ^ 2 := by
    have h := hx.inner_sum γ (fun i => γ i * ((q i ^ 2 : ℝ) : ℂ)) Finset.univ
    rw [hgdef, h, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, RCLike.conj_mul]
    simp [← Complex.ofReal_pow]
  rw [hmain]
  have herr : |RCLike.re ⟪g, ∑ i, γ i • d i⟫_ℂ| ≤ n * ε * ∑ i, ‖γ i‖ ^ 2 := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    refine le_trans (norm_inner_le_norm _ _) ?_
    calc ‖g‖ * ‖∑ i, γ i • d i‖ ≤ ‖g‖ * (n * ε * ‖g‖) :=
          mul_le_mul_of_nonneg_left hDnorm (norm_nonneg g)
      _ = n * ε * ‖g‖ ^ 2 := by ring
      _ = n * ε * ∑ i, ‖γ i‖ ^ 2 := by rw [hgnorm]
  simpa using herr

/-!
## Compressed double-angle eigenfamilies

The exact eigenfamily hypothesis asks `S² xᵢ = qᵢ² xᵢ` in all of `H`, and that
is more than the argument uses.  Diagonalising the *compression* `P_W S² P_W` of
`S²` to a finite-dimensional trial space `W ⊆ 𝔛₀ ∩ D(A)` — which is always
possible, `P_W S² P_W` being a self-adjoint operator on a finite-dimensional
space — gives an orthonormal basis `xᵢ` of `W` with

`S² xᵢ = qᵢ² xᵢ + rᵢ`,   `rᵢ ⊥ W`.

Two hypotheses on the leakage `rᵢ` are what the whole argument needs:

* `hgram`, that `rᵢ ⊥ xⱼ` for every `j`, which is the defining property of the
  compression;
* `hres`, that `Re ⟪A xᵢ, rᵢ⟫ ≤ 0`, which holds outright when `W` is
  `A`-invariant, and holds trivially when `rᵢ = 0`.

Both are implied by an exact eigenfamily (`rᵢ = 0`), so everything below is
strictly more general than the corresponding exact statement; see
`isCompressedDoubleAngleEigenbasis_of_isDoubleAngleEigenbasis`.

The Gram identities of the first three auxiliary systems survive *exactly* —
they only ever pair members of `W` — and only the fourth,
`C S xᵢ / (qᵢ cᵢ)`, acquires a defect.  That defect has a favourable sign: its
Gram operator is `1 - D⁻¹ R⋆ R D⁻¹ ≤ 1`, so the system is a contraction system
and `sum_le_kyFanApproximationGauge_of_contraction` applies with constant `1`.
**The sharp factor `2` is therefore untouched.**
-/

/-- The squared length of the odd block, from the diagonal compressed Gram
entry alone.  No eigenvector relation is needed: `‖S x‖² = ⟪x, S² x⟫`. -/
theorem norm_sq_offDiagonalPart_of_compressedDiagonal
    (hZsa : IsSelfAdjoint Z) {x : H} {q : ℝ}
    (hself : ⟪x, U.offDiagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ =
      ((q ^ 2 : ℝ) : ℂ)) :
    ‖U.offDiagonalPart Z x‖ ^ 2 = q ^ 2 := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have h : ⟪U.offDiagonalPart Z x, U.offDiagonalPart Z x⟫_ℂ =
      ((q ^ 2 : ℝ) : ℂ) := by
    rw [hSsym x (U.offDiagonalPart Z x)]
    exact hself
  have h2 : ((‖U.offDiagonalPart Z x‖ ^ 2 : ℝ) : ℂ) = ((q ^ 2 : ℝ) : ℂ) := by
    rw [← h, inner_self_eq_norm_sq_to_K]
    norm_cast
  exact_mod_cast h2

/-- **Equation (7.6) at a compressed double-angle eigenvector.**

The exact-eigenvector estimate `gap_mul_sq_le_paired_of_doubleAngleEigenvector`
with the global relation `S² x = q² x` replaced by the two compressed facts

* `⟪x, S² x⟫ = q²`, the diagonal Gram entry;
* `Re ⟪A x, S² x - q² x⟫ ≤ 0`, the leakage sign condition.

**No norm of `A` occurs and no error term appears**: the leakage is not
estimated, it is annihilated by the sign condition.  When `x` is an exact
eigenvector the leakage vanishes and both hypotheses are trivial. -/
theorem gap_mul_sq_le_paired_of_compressedDoubleAngleEigenvector
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    {x : A.domain} (hxU : (x : H) ∈ U) (hx1 : ‖(x : H)‖ = 1) {q : ℝ}
    (hself : ⟪(x : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z (x : H))⟫_ℂ = ((q ^ 2 : ℝ) : ℂ))
    (hres : RCLike.re ⟪A x, U.offDiagonalPart Z
        (U.offDiagonalPart Z (x : H)) - ((q ^ 2 : ℝ) : ℂ) • (x : H)⟫_ℂ ≤ 0) :
    (b - a) * q ^ 2 ≤
      RCLike.re ⟪B (x : H),
          U.diagonalPart Z (U.offDiagonalPart Z (x : H))⟫_ℂ -
        RCLike.re ⟪B (U.diagonalPart Z (x : H)),
          U.offDiagonalPart Z (x : H)⟫_ℂ := by
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hSmem : U.offDiagonalPart Z (x : H) ∈ A.domain :=
    TauCeti.mem_domain_offDiagonalPart hred hZdom x
  have hSU : U.offDiagonalPart Z (x : H) ∈ Uᗮ :=
    TauCeti.offDiagonalPart_mem_orthogonal_of_mem U Z hxU
  have hnormS : ‖U.offDiagonalPart Z (x : H)‖ ^ 2 = q ^ 2 :=
    norm_sq_offDiagonalPart_of_compressedDiagonal (U := U) hZsa hself
  have hsyl := TauCeti.sylvester_offDiagonalPart_of_mem hred hB hZdom hZcomm x hxU
  have hpair := congrArg
    (fun w : H => RCLike.re ⟪w, U.offDiagonalPart Z (x : H)⟫_ℂ) hsyl
  simp only [inner_add_left, map_add] at hpair
  have hlow : b * q ^ 2 ≤
      RCLike.re ⟪A ⟨U.offDiagonalPart Z (x : H), hSmem⟩,
        U.offDiagonalPart Z (x : H)⟫_ℂ := by
    have h := hUb ⟨U.offDiagonalPart Z (x : H), hSmem⟩ hSU
    calc b * q ^ 2 = b * ‖U.offDiagonalPart Z (x : H)‖ ^ 2 := by rw [hnormS]
      _ ≤ _ := h
  have hhigh : RCLike.re ⟪U.offDiagonalPart Z (A x),
      U.offDiagonalPart Z (x : H)⟫_ℂ ≤ a * q ^ 2 := by
    have hswap : ⟪U.offDiagonalPart Z (A x), U.offDiagonalPart Z (x : H)⟫_ℂ =
        ((q ^ 2 : ℝ) : ℂ) * ⟪A x, (x : H)⟫_ℂ +
          ⟪A x, U.offDiagonalPart Z (U.offDiagonalPart Z (x : H)) -
            ((q ^ 2 : ℝ) : ℂ) • (x : H)⟫_ℂ := by
      rw [hSsym (A x) (U.offDiagonalPart Z (x : H)), inner_sub_right,
        inner_smul_right]
      ring
    rw [hswap, map_add, ← Complex.real_smul, RCLike.smul_re]
    have hx := hUa x hxU
    rw [hx1, one_pow, mul_one] at hx
    nlinarith [sq_nonneg q, hx, hres]
  have hmove : RCLike.re ⟪U.diagonalPart Z (B (x : H)),
      U.offDiagonalPart Z (x : H)⟫_ℂ =
      RCLike.re ⟪B (x : H),
        U.diagonalPart Z (U.offDiagonalPart Z (x : H))⟫_ℂ := by
    rw [hCsym (B (x : H)) (U.offDiagonalPart Z (x : H))]
  rw [hmove] at hpair
  linarith [hpair, hlow, hhigh]

/-- The two double-angle Pythagoras facts at a compressed eigenvector.  The
first is still an identity; the second becomes an *inequality* in the direction
the contraction argument needs, the deficit being the leakage `‖S² x‖² - q⁴`. -/
theorem norm_sq_diagonalPart_of_compressedDiagonal
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    {x : H} (hx1 : ‖x‖ = 1) {q : ℝ}
    (hself : ⟪x, U.offDiagonalPart Z (U.offDiagonalPart Z x)⟫_ℂ =
      ((q ^ 2 : ℝ) : ℂ)) :
    ‖U.diagonalPart Z x‖ ^ 2 = 1 - q ^ 2 ∧
      ‖U.diagonalPart Z (U.offDiagonalPart Z x)‖ ^ 2 ≤
        q ^ 2 * (1 - q ^ 2) := by
  have hnormS : ‖U.offDiagonalPart Z x‖ ^ 2 = q ^ 2 :=
    norm_sq_offDiagonalPart_of_compressedDiagonal (U := U) hZsa hself
  have hCx := norm_sq_diagonalPart_apply (U := U) hZsa hZ2 x
  have hCSx := norm_sq_diagonalPart_apply (U := U) hZsa hZ2
    (U.offDiagonalPart Z x)
  have hbig : q ^ 2 * q ^ 2 ≤
      ‖U.offDiagonalPart Z (U.offDiagonalPart Z x)‖ ^ 2 := by
    have h1 : ‖((q ^ 2 : ℝ) : ℂ)‖ ≤
        ‖x‖ * ‖U.offDiagonalPart Z (U.offDiagonalPart Z x)‖ := by
      rw [← hself]
      exact norm_inner_le_norm _ _
    rw [hx1, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg q)] at h1
    nlinarith [h1, sq_nonneg q,
      norm_nonneg (U.offDiagonalPart Z (U.offDiagonalPart Z x))]
  refine ⟨by rw [hCx, hx1, hnormS]; ring, ?_⟩
  rw [hCSx, hnormS]
  nlinarith [hbig]

/-- **The pole is excluded at a compressed double-angle eigenvector, for
free.**  `q < 1`, exactly as in the exact-eigenvector case: if `q` were `1`
then `‖C x‖² = 0` and `‖C S x‖² ≤ 0`, and equation (7.6) would force
`δ ≤ 0`. -/
theorem compressedDoubleAngleEigenvalue_lt_one
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    {x : A.domain} (hxU : (x : H) ∈ U) (hx1 : ‖(x : H)‖ = 1) {q : ℝ}
    (hq : 0 < q)
    (hself : ⟪(x : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z (x : H))⟫_ℂ = ((q ^ 2 : ℝ) : ℂ))
    (hres : RCLike.re ⟪A x, U.offDiagonalPart Z
        (U.offDiagonalPart Z (x : H)) - ((q ^ 2 : ℝ) : ℂ) • (x : H)⟫_ℂ ≤ 0) :
    q < 1 := by
  obtain ⟨hCx, hCSx⟩ := norm_sq_diagonalPart_of_compressedDiagonal
    (U := U) hZsa hZ2 hx1 hself
  by_contra hcon
  have hcon : 1 ≤ q := not_lt.mp hcon
  have hnn := sq_nonneg ‖U.diagonalPart Z (x : H)‖
  have hq1 : q ^ 2 = 1 := by nlinarith [hCx, hnn]
  have hCx0 : U.diagonalPart Z (x : H) = 0 := by
    refine norm_eq_zero.mp ?_
    nlinarith [norm_nonneg (U.diagonalPart Z (x : H)), hCx, hq1]
  have hCSx0 : U.diagonalPart Z (U.offDiagonalPart Z (x : H)) = 0 := by
    refine norm_eq_zero.mp ?_
    nlinarith [norm_nonneg (U.diagonalPart Z (U.offDiagonalPart Z (x : H))),
      hCSx, hq1]
  have hmain := gap_mul_sq_le_paired_of_compressedDoubleAngleEigenvector hred hB
    hZsa hZdom hZcomm hUa hUb hxU hx1 hself hres
  rw [hCx0, hCSx0] at hmain
  simp only [map_zero, inner_zero_right, inner_zero_left, sub_zero] at hmain
  nlinarith [hmain, hq1, hab]

/-- `conj z * z = ‖z‖²` in the `Complex.ofReal` spelling.  `RCLike.conj_mul`
states this with the `RCLike.ofReal` coercion and the square outside the cast;
bridging the two by `exact_mod_cast` inside a large context is expensive, so it
is done once here. -/
theorem conj_mul_eq_ofReal_norm_sq (z : ℂ) :
    (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  exact_mod_cast RCLike.conj_mul z

/-- The Gram identities of the first two auxiliary systems at a *compressed*
eigenfamily.  These are still exact: `⟪S xᵢ, S xⱼ⟫` and `⟪C xᵢ, C xⱼ⟫` pair two
members of the trial space, so the leakage — which is orthogonal to it — never
appears.  Only the third system, handled separately, acquires a defect. -/
theorem inner_of_compressedDoubleAngleEigenfamily
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) {n : ℕ} (x : Fin n → H)
    (hx : Orthonormal ℂ x) {q : Fin n → ℝ}
    (hgram : ∀ i j, ⟪x j, U.offDiagonalPart Z
        (U.offDiagonalPart Z (x i))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0))
    (i j : Fin n) :
    ⟪U.offDiagonalPart Z (x i), U.offDiagonalPart Z (x j)⟫_ℂ =
        (((q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) ∧
      ⟪U.diagonalPart Z (x i), U.diagonalPart Z (x j)⟫_ℂ =
        ((1 - (q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) := by
  classical
  have hSsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_offDiagonalPart (U := U) hZsa)
  have hCsym := TauCeti.inner_swap_of_isSelfAdjoint
    (TauCeti.isSelfAdjoint_diagonalPart (U := U) hZsa)
  have hite : ⟪x i, x j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    (orthonormal_iff_ite.mp hx) i j
  have hpyth : ∀ v : H, U.diagonalPart Z (U.diagonalPart Z v) +
      U.offDiagonalPart Z (U.offDiagonalPart Z v) = v := by
    intro v
    have h := TauCeti.diagonalPart_sq_add_offDiagonalPart_sq (U := U) hZ2
    have h2 := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using h2
  have hSS : ⟪U.offDiagonalPart Z (x i), U.offDiagonalPart Z (x j)⟫_ℂ =
      (((q j) ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) := by
    rw [hSsym (x i) (U.offDiagonalPart Z (x j))]
    exact hgram j i
  refine ⟨hSS, ?_⟩
  have hCC : ⟪U.diagonalPart Z (x i), U.diagonalPart Z (x j)⟫_ℂ =
      ⟪x i, U.diagonalPart Z (U.diagonalPart Z (x j))⟫_ℂ :=
    hCsym (x i) (U.diagonalPart Z (x j))
  have hsplit : U.diagonalPart Z (U.diagonalPart Z (x j)) =
      x j - U.offDiagonalPart Z (U.offDiagonalPart Z (x j)) := by
    have h := hpyth (x j)
    linear_combination (norm := module) h
  rw [hCC, hsplit, inner_sub_right, hite, hgram j i]
  push_cast
  ring

/-- **The fourth auxiliary system is a contraction system, with constant `1`.**

For a compressed eigenfamily the normalised vectors `C S xᵢ / (qᵢ cᵢ)` are no
longer orthonormal: their Gram operator is `1 - D⁻¹ R⋆ R D⁻¹`, where `R` collects
the leakage vectors `rᵢ = S² xᵢ - qᵢ² xᵢ`.  That defect is *negative
semidefinite*, so every linear combination is still bounded by the Euclidean
norm of its coefficients — which is exactly the hypothesis of
`sum_le_kyFanApproximationGauge_of_contraction` with constant `1`.

The proof needs no Gram matrix.  Writing `g = ∑ᵢ βᵢ xᵢ` for the corresponding
element of the trial space, the combination is `C S g`, and

* `‖C S g‖² = ‖S g‖² - ‖S² g‖²` is the double-angle Pythagoras identity;
* `‖S g‖² = ∑ᵢ |βᵢ|² qᵢ²` is exact, by the first Gram identity;
* `‖S² g‖² ≥ ∑ᵢ |βᵢ|² qᵢ⁴`, because `∑ᵢ βᵢ qᵢ² xᵢ` is the trial-space part of
  `S² g`, and dropping the leakage only decreases the norm.

Subtracting gives `∑ᵢ |βᵢ|² qᵢ² (1 - qᵢ²) = ∑ᵢ |αᵢ|²`. -/
theorem sq_norm_sum_smul_diagonalPart_offDiagonalPart_le_of_compressed
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1) {n : ℕ} (x : Fin n → H)
    (hx : Orthonormal ℂ x) {q : Fin n → ℝ} (hq : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (hgram : ∀ i j, ⟪x j, U.offDiagonalPart Z
        (U.offDiagonalPart Z (x i))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0))
    (α : Fin n → ℂ) :
    ‖∑ i, α i • ((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z (U.offDiagonalPart Z (x i)))‖ ^ 2 ≤
      (1 : ℝ) ^ 2 * ∑ i, ‖α i‖ ^ 2 := by
  classical
  have hc0 : ∀ i, 0 < 1 - (q i) ^ 2 := fun i => by nlinarith [hq i, hq1 i]
  have hcpos : ∀ i, 0 < √(1 - (q i) ^ 2) := fun i => Real.sqrt_pos.mpr (hc0 i)
  have hcsq : ∀ i, √(1 - (q i) ^ 2) ^ 2 = 1 - (q i) ^ 2 :=
    fun i => Real.sq_sqrt (hc0 i).le
  have hqcpos : ∀ i, 0 < q i * √(1 - (q i) ^ 2) :=
    fun i => mul_pos (hq i) (hcpos i)
  have hqne : ∀ i, (((q i : ℝ) : ℂ)) ≠ 0 := by
    intro i
    simpa using (hq i).ne'
  have hqcne : ∀ i, ((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)) ≠ 0 := by
    intro i
    simpa using (hqcpos i).ne'
  obtain ⟨β, hβdef⟩ : ∃ β : Fin n → ℂ,
      β = fun i => α i * ((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ))⁻¹ := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : H, g = ∑ i, β i • x i := ⟨_, rfl⟩
  -- the combination is `C S g`
  have hcomb : ∑ i, α i • ((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
      U.diagonalPart Z (U.offDiagonalPart Z (x i))) =
      U.diagonalPart Z (U.offDiagonalPart Z g) := by
    rw [hgdef, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, smul_smul]
    simp only [hβdef]
  -- the first auxiliary system is orthonormal
  have hyon : Orthonormal ℂ fun i =>
      (((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)) :=
    orthonormal_scaled_of_inner_eq hq fun i j =>
      (inner_of_compressedDoubleAngleEigenfamily (U := U) hZsa hZ2 x hx
        hgram i j).1
  -- `‖S g‖² = ∑ |βᵢ|² qᵢ²`
  have hSg : U.offDiagonalPart Z g = ∑ i, (β i * ((q i : ℝ) : ℂ)) •
      (((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z (x i)) := by
    rw [hgdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_smul, mul_assoc, mul_inv_cancel₀ (hqne i), mul_one]
  have hnormSg : ‖U.offDiagonalPart Z g‖ ^ 2 = ∑ i, ‖β i‖ ^ 2 * q i ^ 2 := by
    rw [hSg, norm_sq_sum_smul_of_orthonormal hyon]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq i)]
    ring
  -- `‖S² g‖² ≥ ∑ |βᵢ|² qᵢ⁴`
  obtain ⟨p, hpdef⟩ : ∃ p : H, p = ∑ i, (β i * (((q i) ^ 2 : ℝ) : ℂ)) • x i :=
    ⟨_, rfl⟩
  have hpnorm : ‖p‖ ^ 2 = ∑ i, ‖β i‖ ^ 2 * q i ^ 4 := by
    rw [hpdef, norm_sq_sum_smul_of_orthonormal hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (q i))]
    ring
  have hSSg : U.offDiagonalPart Z (U.offDiagonalPart Z g) =
      ∑ j, β j • U.offDiagonalPart Z (U.offDiagonalPart Z (x j)) := by
    rw [hgdef, map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul]
  have hxi : ∀ i, ⟪x i, U.offDiagonalPart Z (U.offDiagonalPart Z g)⟫_ℂ =
      β i * (((q i) ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [hSSg, inner_sum, Finset.sum_eq_single i]
    · rw [inner_smul_right, hgram i i, if_pos rfl, mul_one]
    · intro j _ hj
      rw [inner_smul_right, hgram j i, if_neg (Ne.symm hj), mul_zero, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hterm : ∀ i : Fin n, ⟪(β i * (((q i) ^ 2 : ℝ) : ℂ)) • x i,
      U.offDiagonalPart Z (U.offDiagonalPart Z g)⟫_ℂ =
      ((‖β i‖ ^ 2 * q i ^ 4 : ℝ) : ℂ) := by
    intro i
    have hnz : ‖β i * (((q i) ^ 2 : ℝ) : ℂ)‖ ^ 2 = ‖β i‖ ^ 2 * q i ^ 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (q i))]
      ring
    rw [inner_smul_left, hxi i, conj_mul_eq_ofReal_norm_sq, hnz]
  have hinner : ⟪p, U.offDiagonalPart Z (U.offDiagonalPart Z g)⟫_ℂ =
      ((‖p‖ ^ 2 : ℝ) : ℂ) := by
    rw [hpnorm, hpdef, sum_inner, Finset.sum_congr rfl fun i _ => hterm i]
    push_cast
    ring
  have hple : ‖p‖ ≤ ‖U.offDiagonalPart Z (U.offDiagonalPart Z g)‖ := by
    have hre : ‖p‖ ^ 2 ≤
        ‖p‖ * ‖U.offDiagonalPart Z (U.offDiagonalPart Z g)‖ := by
      have h1 : ((‖p‖ ^ 2 : ℝ) : ℂ) =
          ⟪p, U.offDiagonalPart Z (U.offDiagonalPart Z g)⟫_ℂ := hinner.symm
      have h2 : ‖((‖p‖ ^ 2 : ℝ) : ℂ)‖ ≤
          ‖p‖ * ‖U.offDiagonalPart Z (U.offDiagonalPart Z g)‖ := by
        rw [h1]
        exact norm_inner_le_norm _ _
      rwa [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)] at h2
    rcases (norm_nonneg p).lt_or_eq with h | h
    · exact le_of_mul_le_mul_left (by linarith [hre]) h
    · rw [← h]
      exact norm_nonneg _
  have hSSglow : ∑ i, ‖β i‖ ^ 2 * q i ^ 4 ≤
      ‖U.offDiagonalPart Z (U.offDiagonalPart Z g)‖ ^ 2 := by
    rw [← hpnorm]
    have := mul_self_le_mul_self (norm_nonneg p) hple
    nlinarith [this]
  -- assemble
  have hpythg := norm_sq_diagonalPart_apply (U := U) hZsa hZ2
    (U.offDiagonalPart Z g)
  have hfinal : ∑ i, ‖β i‖ ^ 2 * q i ^ 2 - ∑ i, ‖β i‖ ^ 2 * q i ^ 4 =
      ∑ i, ‖α i‖ ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hinvnorm : ‖((((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ))⁻¹‖ =
        (q i * √(1 - (q i) ^ 2))⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hqcpos i)]
    have hnβ : ‖β i‖ = ‖α i‖ * (q i * √(1 - (q i) ^ 2))⁻¹ := by
      simp only [hβdef, norm_mul, hinvnorm]
    have hqc2 : (q i * √(1 - (q i) ^ 2)) ^ 2 = q i ^ 2 * (1 - (q i) ^ 2) := by
      rw [mul_pow, hcsq i]
    have hd : q i ^ 2 * (1 - (q i) ^ 2) ≠ 0 :=
      ne_of_gt (mul_pos (pow_pos (hq i) 2) (hc0 i))
    have hkey : ‖β i‖ ^ 2 * (q i ^ 2 * (1 - (q i) ^ 2)) = ‖α i‖ ^ 2 := by
      rw [hnβ, mul_pow, inv_pow, hqc2, mul_assoc, inv_mul_cancel₀ hd, mul_one]
    linear_combination hkey
  rw [hcomb, hpythg, hnormSg, one_pow, one_mul]
  linarith [hSSglow, hfinal]

omit [CompleteSpace H] in
/-- **The leakage condition is automatic on an `A`-invariant trial space.**

If `A xᵢ` lies in the span of the family — which is what it means for the trial
space to be `A`-invariant — then the leakage pairs with it to *exactly* zero,
because the leakage is orthogonal to every member of the family.  No norm of `A`
and no cutoff level enter.

This is the reason the compressed hypothesis is reachable: on a
finite-dimensional `A`-invariant subspace `W ⊆ 𝔛₀ ∩ D(A)`, the compression
`P_W S² P_W` is a self-adjoint operator on a finite-dimensional space, so it
*always* has an orthonormal eigenbasis, and this lemma supplies the second
condition for free.  Nothing about the point spectrum of `S²` is needed. -/
theorem re_inner_compressedResidual_eq_zero_of_apply_eq_sum
    {n : ℕ} (x : Fin n → A.domain)
    (hxon : Orthonormal ℂ fun i => ((x i : A.domain) : H))
    {q : Fin n → ℝ}
    (hgram : ∀ i j, ⟪((x j : A.domain) : H), U.offDiagonalPart Z
        (U.offDiagonalPart Z ((x i : A.domain) : H))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0))
    {i : Fin n} {γ : Fin n → ℂ}
    (hA : A (x i) = ∑ j, γ j • ((x j : A.domain) : H)) :
    RCLike.re ⟪A (x i), U.offDiagonalPart Z
        (U.offDiagonalPart Z ((x i : A.domain) : H)) -
          (((q i) ^ 2 : ℝ) : ℂ) • ((x i : A.domain) : H)⟫_ℂ = 0 := by
  classical
  have hz : ⟪A (x i), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((x i : A.domain) : H)) -
        (((q i) ^ 2 : ℝ) : ℂ) • ((x i : A.domain) : H)⟫_ℂ = 0 := by
    rw [hA, sum_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_left, inner_sub_right, inner_smul_right, hgram i j,
      (orthonormal_iff_ite.mp hxon) j i]
    ring
  rw [hz, map_zero]

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Ky Fan prefix, on a
compressed double-angle eigenfamily.**

Identical in hypotheses and conclusion to
`gap_mul_sum_tangent_le_kyFan_of_doubleAngleEigenfamily` except that the exact
eigenvector relation `S² xᵢ = qᵢ² xᵢ` is weakened to the two compression
conditions `hgram` and `hres`.  The conclusion, **including the sharp constant
`2`**, is unchanged.

The constant survives because the defect is one-sided.  Three of the four
auxiliary systems are still exactly orthonormal and contribute
`kyFanApproximationGauge n B` each, exactly as before; the fourth is a
contraction system with constant `1`, and
`sum_le_kyFanApproximationGauge_of_contraction` charges `1 * 1` for it.  Nothing
anywhere is multiplied by `1 + ε`. -/
theorem gap_mul_sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b)
    {n : ℕ} (x : Fin n → A.domain)
    (hxU : ∀ i, ((x i : A.domain) : H) ∈ U)
    (hxon : Orthonormal ℂ fun i => ((x i : A.domain) : H))
    {q : Fin n → ℝ} (hq : ∀ i, 0 < q i)
    (hgram : ∀ i j, ⟪((x j : A.domain) : H), U.offDiagonalPart Z
        (U.offDiagonalPart Z ((x i : A.domain) : H))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0))
    (hres : ∀ i, RCLike.re ⟪A (x i), U.offDiagonalPart Z
        (U.offDiagonalPart Z ((x i : A.domain) : H)) -
          (((q i) ^ 2 : ℝ) : ℂ) • ((x i : A.domain) : H)⟫_ℂ ≤ 0) :
    (b - a) * ∑ i, q i / √(1 - (q i) ^ 2) ≤
      2 * kyFanApproximationGauge n B := by
  classical
  have hx1 : ∀ i, ‖((x i : A.domain) : H)‖ = 1 := fun i => hxon.norm_eq_one i
  have hself : ∀ i, ⟪((x i : A.domain) : H), U.offDiagonalPart Z
      (U.offDiagonalPart Z ((x i : A.domain) : H))⟫_ℂ =
      (((q i) ^ 2 : ℝ) : ℂ) := fun i => by
    rw [hgram i i, if_pos rfl, mul_one]
  have hq1 : ∀ i, q i < 1 := fun i =>
    compressedDoubleAngleEigenvalue_lt_one hred hB hZsa hZ2 hZdom hZcomm hUa hUb
      hab (hxU i) (hx1 i) (hq i) (hself i) (hres i)
  have hc0 : ∀ i, 0 < 1 - (q i) ^ 2 := by
    intro i
    nlinarith [hq i, hq1 i]
  have hcpos : ∀ i, 0 < √(1 - (q i) ^ 2) := fun i => Real.sqrt_pos.mpr (hc0 i)
  have hgram2 := fun i j => inner_of_compressedDoubleAngleEigenfamily (U := U)
    hZsa hZ2 (fun i => ((x i : A.domain) : H)) hxon hgram i j
  -- the two exactly orthonormal auxiliary systems
  have hyon : Orthonormal ℂ fun i =>
      (((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z ((x i : A.domain) : H)) :=
    orthonormal_scaled_of_inner_eq hq fun i j => (hgram2 i j).1
  have huon : Orthonormal ℂ fun i =>
      (((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z ((x i : A.domain) : H)) :=
    orthonormal_scaled_of_inner_eq hcpos fun i j => by
      rw [Real.sq_sqrt (hc0 j).le]
      exact (hgram2 i j).2
  have hnegon : Orthonormal ℂ fun i =>
      -(((q i : ℝ) : ℂ)⁻¹ • U.offDiagonalPart Z ((x i : A.domain) : H)) := by
    have h := orthonormal_signFlip hyon (fun _ => false)
    simpa using h
  -- the one contraction system
  have hcontr := sq_norm_sum_smul_diagonalPart_offDiagonalPart_le_of_compressed
    (U := U) hZsa hZ2 (fun i => ((x i : A.domain) : H)) hxon hq hq1 hgram
  -- the per-index estimate, divided by `qᵢ cᵢ`
  have hstep : ∀ i, (b - a) * (q i / √(1 - (q i) ^ 2)) ≤
      RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((x i : A.domain) : H)⟫_ℂ +
      RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
          U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ := by
    intro i
    have hqc : 0 < q i * √(1 - (q i) ^ 2) := mul_pos (hq i) (hcpos i)
    have hmain := gap_mul_sq_le_paired_of_compressedDoubleAngleEigenvector hred
      hB hZsa hZdom hZcomm hUa hUb (hxU i) (hx1 i) (hself i) (hres i)
    have hterm1 : RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((x i : A.domain) : H)⟫_ℂ =
        (q i * √(1 - (q i) ^ 2))⁻¹ *
          RCLike.re ⟪B ((x i : A.domain) : H),
            U.diagonalPart Z (U.offDiagonalPart Z
              ((x i : A.domain) : H))⟫_ℂ := by
      rw [inner_smul_left, ← Complex.ofReal_inv, Complex.conj_ofReal,
        ← Complex.real_smul, RCLike.smul_re, inner_re_symm]
    have hterm2 : RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
        U.offDiagonalPart Z ((x i : A.domain) : H)),
        B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ =
        -((q i * √(1 - (q i) ^ 2))⁻¹ *
          RCLike.re ⟪B (U.diagonalPart Z ((x i : A.domain) : H)),
            U.offDiagonalPart Z ((x i : A.domain) : H)⟫_ℂ) := by
      rw [mul_inv]
      simp only [map_smul, inner_neg_left, inner_smul_left, inner_smul_right,
        ← Complex.ofReal_inv, Complex.conj_ofReal]
      rw [mul_neg, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.real_smul,
        map_neg, RCLike.smul_re, inner_re_symm]
      ring
    rw [hterm1, hterm2]
    have hdiv : (b - a) * (q i / √(1 - (q i) ^ 2)) =
        (q i * √(1 - (q i) ^ 2))⁻¹ * ((b - a) * (q i) ^ 2) := by
      field_simp
    rw [hdiv]
    have hpos : (0 : ℝ) ≤ (q i * √(1 - (q i) ^ 2))⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmain hpos]
  have hsum1 : ∑ i, RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
      U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
      B ((x i : A.domain) : H)⟫_ℂ ≤ kyFanApproximationGauge n B := by
    have h := sum_le_kyFanApproximationGauge_of_contraction B zero_le_one
      zero_le_one hcontr
      (fun α => sq_norm_sum_smul_le_of_orthonormal hxon (le_refl (1 : ℝ)) α)
      (fun _ => le_rfl)
    simpa using h
  have hsum2 : ∑ i, RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
      U.offDiagonalPart Z ((x i : A.domain) : H)),
      B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
        U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ ≤
      kyFanApproximationGauge n B :=
    sum_le_kyFanApproximationGauge_of_orthonormal B hnegon huon (fun _ => le_rfl)
  calc (b - a) * ∑ i, q i / √(1 - (q i) ^ 2)
      = ∑ i, (b - a) * (q i / √(1 - (q i) ^ 2)) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, (RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((x i : A.domain) : H)⟫_ℂ +
          RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
            U.offDiagonalPart Z ((x i : A.domain) : H)),
            B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
              U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (∑ i, RCLike.re ⟪(((q i * √(1 - (q i) ^ 2)) : ℝ) : ℂ)⁻¹ •
          U.diagonalPart Z (U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((x i : A.domain) : H)⟫_ℂ) +
        ∑ i, RCLike.re ⟪-(((q i : ℝ) : ℂ)⁻¹ •
          U.offDiagonalPart Z ((x i : A.domain) : H)),
          B ((((√(1 - (q i) ^ 2) : ℝ) : ℂ)⁻¹ •
            U.diagonalPart Z ((x i : A.domain) : H)))⟫_ℂ :=
        Finset.sum_add_distrib
    _ ≤ 2 * kyFanApproximationGauge n B := by linarith [hsum1, hsum2]

/-- A trial-subspace *compressed* eigenbasis for `sin² 2Θ` realising the Ky Fan
prefixes of a candidate tangent operator.

Exactly `IsDoubleAngleEigenbasis` with the global eigenvector relation replaced
by the two compression conditions: the leakage
`rᵢ = S² yᵢ - qᵢ² yᵢ` is orthogonal to the family, and pairs non-positively with
`A yᵢ`.  Both hold whenever `rᵢ = 0`, and both hold whenever the span of the
family is `A`-invariant and `qᵢ²` are the eigenvalues of the compression of `S²`
to it — which a finite-dimensional space always supplies. -/
def IsCompressedDoubleAngleEigenbasis (A : H →ₗ.[ℂ] H) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (Z T : H →L[ℂ] H) : Prop :=
  ∀ k : ℕ, ∃ (y : Fin k → A.domain) (q : Fin k → ℝ),
    (∀ i, ((y i : A.domain) : H) ∈ U) ∧
      (Orthonormal ℂ fun i => ((y i : A.domain) : H)) ∧
      (∀ i, 0 < q i) ∧
      (∀ i j, ⟪((y j : A.domain) : H), U.offDiagonalPart Z
          (U.offDiagonalPart Z ((y i : A.domain) : H))⟫_ℂ =
        (((q i) ^ 2 : ℝ) : ℂ) * (if j = i then (1 : ℂ) else 0)) ∧
      (∀ i, RCLike.re ⟪A (y i), U.offDiagonalPart Z
          (U.offDiagonalPart Z ((y i : A.domain) : H)) -
            (((q i) ^ 2 : ℝ) : ℂ) • ((y i : A.domain) : H)⟫_ℂ ≤ 0) ∧
      kyFanApproximationGauge k T ≤ ∑ i, q i / √(1 - (q i) ^ 2)

omit [CompleteSpace H] in
/-- **An exact eigenbasis is a compressed one.**  The leakage vanishes
identically, so both compression conditions are trivial.  This is what makes
every compressed endpoint below at least as strong as its exact counterpart. -/
theorem isCompressedDoubleAngleEigenbasis_of_isDoubleAngleEigenbasis
    {T : H →L[ℂ] H} (hT : IsDoubleAngleEigenbasis A U Z T) :
    IsCompressedDoubleAngleEigenbasis A U Z T := by
  classical
  intro k
  obtain ⟨y, q, hyU, hyon, hqpos, hyeig, hle⟩ := hT k
  refine ⟨y, q, hyU, hyon, hqpos, ?_, ?_, hle⟩
  · intro i j
    rw [hyeig i, inner_smul_right]
    congr 1
    exact (orthonormal_iff_ite.mp hyon) j i
  · intro i
    rw [hyeig i, sub_self, inner_zero_right]
    simp

/-- **The unbounded residual `tan 2Θ` theorem at every Ky Fan gauge, on a
compressed eigenbasis.**  `δ · kyFanApproximationGauge k T ≤
2 · kyFanApproximationGauge k B` for every prefix length `k`. -/
theorem gap_mul_kyFan_le_two_mul_kyFan_of_compressedDoubleAngleEigenbasis
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : IsCompressedDoubleAngleEigenbasis A U Z T) (k : ℕ) :
    (b - a) * kyFanApproximationGauge k T ≤
      2 * kyFanApproximationGauge k B := by
  obtain ⟨y, q, hyU, hyon, hqpos, hygram, hyres, hle⟩ := hT k
  have hmain := gap_mul_sum_tangent_le_kyFan_of_compressedDoubleAngleEigenfamily
    hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab y hyU hyon hqpos hygram hyres
  have hδ : (0 : ℝ) ≤ b - a := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hle hδ, hmain]

/-- **The exact-eigenbasis Ky Fan endpoint, re-derived from the compressed
one.**

The statement is *verbatim* that of
`gap_mul_kyFan_le_two_mul_kyFan_of_doubleAngleEigenbasis` — same hypotheses,
same conclusion, same constant `2` — and the proof uses nothing but the
compressed endpoint.  This is the machine-checked demonstration that removing
the exact eigenvector relation lost no strength. -/
theorem gap_mul_kyFan_le_two_mul_kyFan_of_doubleAngleEigenbasis_via_compressed
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : IsDoubleAngleEigenbasis A U Z T) (k : ℕ) :
    (b - a) * kyFanApproximationGauge k T ≤
      2 * kyFanApproximationGauge k B :=
  gap_mul_kyFan_le_two_mul_kyFan_of_compressedDoubleAngleEigenbasis hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab
    (isCompressedDoubleAngleEigenbasis_of_isDoubleAngleEigenbasis hT) k

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Fan-dominant
unitarily invariant ideal gauge, on a compressed eigenbasis.**

`δ N(tan 2Θ₀) ≤ 2 N(R)` in the repository's scaled form.  Ideal membership of
the scaled tangent is concluded, not assumed. -/
theorem mem_and_gauge_le_of_compressedDoubleAngleEigenbasis
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain, (x : H) ∈ U →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : H) ∈ Uᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hab : a < b) {T : H →L[ℂ] H}
    (hT : IsCompressedDoubleAngleEigenbasis A U Z T) (hBmem : N.Mem B) :
    N.Mem ((((b - a) / 2 : ℝ) : ℂ) • T) ∧
      N.gauge ((((b - a) / 2 : ℝ) : ℂ) • T) ≤ N.gauge B := by
  refine mem_and_gauge_le_of_all_kyFanApproximationGauge_le N hBmem fun k => ?_
  rw [kyFanApproximationGauge_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b - a) / 2)]
  have h := gap_mul_kyFan_le_two_mul_kyFan_of_compressedDoubleAngleEigenbasis
    hred hB hZsa hZ2 hZdom hZcomm hUa hUb hab hT k
  linarith

end

end DavisKahan1970
end TauCeti
