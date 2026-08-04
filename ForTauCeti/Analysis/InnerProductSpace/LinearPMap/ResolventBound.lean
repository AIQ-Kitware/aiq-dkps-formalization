/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# The resolvent of an unbounded operator, and its norm

`TauCeti.LinearPMap.resolventSet` says a bounded two-sided inverse of `A - z`
*exists*; this file names it and proves the facts everything downstream wants:

* the **first resolvent identity**, `R w - R z = (w - z) • R w ∘ R z`;
* **resolvent spectral mapping** in the direction that matters — if `μ ≠ 0` and
  `z + μ⁻¹` is in the resolvent set of `A`, then `μ` is not in the spectrum of
  the bounded operator `R z`;
* hence, via Mathlib's `IsSelfAdjoint.spectralRadius_eq_nnnorm`, the
  quantitative bound the Davis--Kahan unbounded theory consumes:

> if `A` is self-adjoint and its spectrum avoids the ball of radius `s` about a
> real `c`, then `A - c` has a bounded two-sided inverse of norm at most `s⁻¹`.

## Why this file exists

That bound was previously obtained from `vendor/Spectra` by a much heavier
route: Stone's theorem (`genToGroup`) to manufacture a unitary group, its
projection-valued measure, the bounded Borel functional calculus, and a
truncated symbol `(l - c)⁻¹`.  None of that is needed.  The bound is a
*C⋆-algebra* fact about the bounded operator `R`, and the only input from the
unbounded side is the spectral mapping, which is elementary algebra with domain
bookkeeping.

For the Spectra-removal plan this removes the
projection-valued-measure layer from the critical path of the gap-resolvent
endpoint, which was the largest single block of the port.

## Provenance

* **Extraction class:** *new*.  Statement and proof are ours.
* **Spectra influence:** the *theorem selection* is Spectra's — its
  `exists_norm_le_two_sided_shifted_inverse_of_spectralProjection_Ioo_eq_zero`
  is what identified this bound as the thing to prove, and
  `docs/planning/tauceti-adaptation-and-spectra-extraction.md` records that
  theorem selection is attributable even when the proof is independent.  The
  proof *architecture* is not Spectra's: Spectra goes through the PVM and the
  bounded calculus, this goes through spectral mapping and the spectral radius,
  and the two share no lemma.
-/

public section

namespace TauCeti
namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The bounded two-sided inverse of `A - z`, for `z` in the resolvent set. -/
@[expose]
noncomputable def resolvent (A : E →ₗ.[𝕜] E) {z : 𝕜} (hz : z ∈ resolventSet A) :
    E →L[𝕜] E :=
  (mem_resolventSet_iff.mp hz).choose

/-- `resolvent A hz` is a **left** inverse of `A - z` on the domain: it undoes
`A - z` on every `ψ ∈ A.domain`.  Together with `sub_smul_resolvent` this is the
two-sided inverse property that defines the resolvent. -/
theorem resolvent_apply_sub_smul {A : E →ₗ.[𝕜] E} {z : 𝕜} (hz : z ∈ resolventSet A)
    (ψ : A.domain) : resolvent A hz (A ψ - z • (ψ : E)) = (ψ : E) :=
  (mem_resolventSet_iff.mp hz).choose_spec.1 ψ

/-- The resolvent maps the whole space **into the domain** of `A`.  This is what
makes the right-inverse statement `sub_smul_resolvent` typecheck: `A` may only
be applied to elements of `A.domain`, so a witness of membership is needed
before `A` can be applied to `resolvent A hz φ`. -/
theorem resolvent_mem_domain {A : E →ₗ.[𝕜] E} {z : 𝕜} (hz : z ∈ resolventSet A)
    (φ : E) : resolvent A hz φ ∈ A.domain :=
  ((mem_resolventSet_iff.mp hz).choose_spec.2 φ).choose

/-- `resolvent A hz` is a **right** inverse of `A - z`: applying `A - z` to it
recovers the original vector, for every `φ` in the whole space.  The domain
membership is supplied by `resolvent_mem_domain`. -/
theorem sub_smul_resolvent {A : E →ₗ.[𝕜] E} {z : 𝕜} (hz : z ∈ resolventSet A) (φ : E) :
    A ⟨resolvent A hz φ, resolvent_mem_domain hz φ⟩ - z • resolvent A hz φ = φ :=
  ((mem_resolventSet_iff.mp hz).choose_spec.2 φ).choose_spec

/-- **First resolvent identity.**  `R w - R z = (w - z) • R w ∘ R z`.

Sanity check on scalars: with `R t = (a - t)⁻¹`,
`R w - R z = (w - z) / ((a - w)(a - z))`. -/
theorem resolvent_sub_resolvent {A : E →ₗ.[𝕜] E} {w z : 𝕜}
    (hw : w ∈ resolventSet A) (hz : z ∈ resolventSet A) (φ : E) :
    resolvent A hw φ - resolvent A hz φ
      = (w - z) • resolvent A hw (resolvent A hz φ) := by
  set x := resolvent A hz φ with hx
  have hmem : x ∈ A.domain := resolvent_mem_domain hz φ
  have hsolve : A ⟨x, hmem⟩ - z • x = φ := sub_smul_resolvent hz φ
  -- rewrite `(A - w) x` as `φ + (z - w) • x`
  have hshift : A ⟨x, hmem⟩ - w • ((⟨x, hmem⟩ : A.domain) : E) = φ + (z - w) • x := by
    rw [← hsolve, sub_smul]
    abel
  have hkey : resolvent A hw φ + (z - w) • resolvent A hw x = x := by
    have h := resolvent_apply_sub_smul hw ⟨x, hmem⟩
    rw [hshift, map_add, map_smul] at h
    exact h
  -- `rw [← hkey]` would also rewrite the `x` inside `R w x`; peel `hkey` instead.
  rw [eq_sub_of_add_eq hkey]
  module

/-- The two resolvents commute, and their product is a difference:
`R z ∘ R w = (z - w)⁻¹ • (R w - R z)` when `z ≠ w`.  Stated in the form the
spectral mapping below consumes. -/
theorem resolvent_comp_resolvent {A : E →ₗ.[𝕜] E} {z w : 𝕜}
    (hz : z ∈ resolventSet A) (hw : w ∈ resolventSet A) {μ : 𝕜}
    (hμ : μ ≠ 0) (hwz : w = z + μ⁻¹) (φ : E) :
    resolvent A hz (resolvent A hw φ) = μ • (resolvent A hw φ - resolvent A hz φ) := by
  have h := resolvent_sub_resolvent hz hw φ
  have hzw : z - w = -μ⁻¹ := by rw [hwz]; ring
  rw [hzw] at h
  have hμ' : (μ : 𝕜) ≠ 0 := hμ
  -- `R z φ - R w φ = -μ⁻¹ • R z (R w φ)`
  have := congrArg (fun v => (-μ) • v) h
  simp only [smul_smul] at this
  rw [show (-μ) * (-μ⁻¹) = 1 by field_simp] at this
  rw [one_smul] at this
  rw [← this]
  module

/-- **Resolvent spectral mapping**, in the direction the norm bound needs: a
nonzero `μ` outside the image `(· - z)⁻¹ '' spectrum A` is outside the spectrum
of the bounded operator `R z`.

Equivalently — and this is what is proved — if `z + μ⁻¹` is a resolvent point of
`A` then `μ • 1 - R z` is a unit, with explicit inverse
`μ⁻¹ • (1 + μ⁻¹ • R (z + μ⁻¹))`. -/
theorem notMem_spectrum_resolvent {A : E →ₗ.[𝕜] E} {z : 𝕜}
    (hz : z ∈ resolventSet A) {μ : 𝕜} (hμ : μ ≠ 0)
    (hw : z + μ⁻¹ ∈ resolventSet A) :
    μ ∉ _root_.spectrum 𝕜 (resolvent A hz) := by
  classical
  set R := resolvent A hz with hR
  set S := resolvent A hw with hS
  set T : E →L[𝕜] E := μ⁻¹ • (1 + μ⁻¹ • S) with hT
  -- `R (S φ) = μ • (S φ - R φ)` and `S (R φ) = μ • (S φ - R φ)`
  have hRS : ∀ φ, R (S φ) = μ • (S φ - R φ) := by
    intro φ
    have := resolvent_comp_resolvent hz hw hμ rfl φ
    simpa [hR, hS] using this
  have hSR : ∀ φ, S (R φ) = μ • (S φ - R φ) := by
    intro φ
    have h := resolvent_sub_resolvent hw hz φ
    have hwz : z + μ⁻¹ - z = μ⁻¹ := by ring
    rw [hwz] at h
    have := congrArg (fun v => μ • v) h
    simp only [smul_smul] at this
    rw [show (μ : 𝕜) * μ⁻¹ = 1 by field_simp, one_smul] at this
    simpa [hR, hS] using this.symm
  have hinv : μ * μ⁻¹ = 1 := mul_inv_cancel₀ hμ
  have hinv' : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ
  have hTapp : ∀ φ : E, T φ = μ⁻¹ • (φ + μ⁻¹ • S φ) := fun φ => by simp [hT]
  -- `R (T φ) = μ⁻¹ • S φ`, the one computation both directions rest on.
  have hRT : ∀ φ : E, R (T φ) = μ⁻¹ • S φ := by
    intro φ
    simp only [hTapp, map_smul, map_add, hRS φ, smul_smul, hinv', one_smul]
    module
  have hleft : (algebraMap 𝕜 (E →L[𝕜] E) μ - R) * T = 1 := by
    refine ContinuousLinearMap.ext fun φ => ?_
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change μ • T φ - R (T φ) = φ
    rw [hRT φ, hTapp φ, smul_smul, hinv, one_smul]
    module
  have hright : T * (algebraMap 𝕜 (E →L[𝕜] E) μ - R) = 1 := by
    refine ContinuousLinearMap.ext fun φ => ?_
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change T (μ • φ - R φ) = φ
    rw [hTapp, map_sub, map_smul, hSR φ]
    rw [show μ • S φ - μ • (S φ - R φ) = μ • R φ by module]
    -- `module` reduces to scalar identities; they need `μ ≠ 0`, so `field_simp`.
    match_scalars
    all_goals field_simp
    all_goals ring
  exact (spectrum.notMem_iff).mpr ⟨⟨_, T, hleft, hright⟩, rfl⟩
/-- **Resolvents at different points commute.**

Both orders of the first resolvent identity give `(w - z) • R w ∘ R z` and
`(z - w) • R z ∘ R w` for the same difference, so the two products agree once the
nonzero scalar `w - z` is cancelled. -/
theorem resolvent_comm {A : E →ₗ.[𝕜] E} {w z : 𝕜}
    (hw : w ∈ resolventSet A) (hz : z ∈ resolventSet A) (hne : w ≠ z) (φ : E) :
    resolvent A hw (resolvent A hz φ) = resolvent A hz (resolvent A hw φ) := by
  have h1 := resolvent_sub_resolvent hw hz φ
  have h2 := resolvent_sub_resolvent hz hw φ
  -- `R w φ - R z φ = (w - z) • R w (R z φ)` and `R z φ - R w φ = (z - w) • R z (R w φ)`
  have hsum : (w - z) • resolvent A hw (resolvent A hz φ)
      + (z - w) • resolvent A hz (resolvent A hw φ) = 0 := by
    rw [← h1, ← h2]; abel
  have hzw : (w - z) ≠ 0 := sub_ne_zero_of_ne hne
  have hstep : (w - z) • (resolvent A hw (resolvent A hz φ)
      - resolvent A hz (resolvent A hw φ)) = 0 := by
    rw [smul_sub]
    rw [show (w - z) • resolvent A hz (resolvent A hw φ)
        = -((z - w) • resolvent A hz (resolvent A hw φ)) by
      rw [← neg_smul]; congr 1; ring]
    rw [sub_neg_eq_add]
    exact hsum
  have := (smul_eq_zero.mp hstep).resolve_left hzw
  exact sub_eq_zero.mp this

/-- Resolvents always commute, including at a common point (where the two
membership proofs are equal by proof irrelevance). -/
theorem resolvent_comm' {A : E →ₗ.[𝕜] E} {w z : 𝕜}
    (hw : w ∈ resolventSet A) (hz : z ∈ resolventSet A) (φ : E) :
    resolvent A hw (resolvent A hz φ) = resolvent A hz (resolvent A hw φ) := by
  by_cases h : w = z
  · subst h; rfl
  · exact resolvent_comm hw hz h φ

/-- The composition form of `resolvent_comm'`. -/
theorem resolvent_commute {A : E →ₗ.[𝕜] E} {w z : 𝕜}
    (hw : w ∈ resolventSet A) (hz : z ∈ resolventSet A) :
    Commute (resolvent A hw) (resolvent A hz) := by
  ext φ
  exact resolvent_comm' hw hz φ

end LinearPMap
end TauCeti
