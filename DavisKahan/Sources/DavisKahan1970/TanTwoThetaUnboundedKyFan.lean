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
variable {A : H →ₗ.[ℂ] H} {B Z : H →L[ℂ] H} {a b : ℝ}

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

end

end DavisKahan1970
end TauCeti
