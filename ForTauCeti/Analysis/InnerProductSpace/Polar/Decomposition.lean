/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T02.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
a new `Mathlib/Analysis/InnerProductSpace/PolarDecomposition.lean`.

Sub-dev III of the operator polar decomposition project — COMPLETE
(proof-complete; reduction uses only:
`propext, Classical.choice, Quot.sound`). Tickets PD-08..PD-12.
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.PositiveSqrt
public import ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus
public import ForTauCeti.Analysis.InnerProductSpace.PartialIsometry
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder


/-! # Operator polar decomposition `A = U |A|` (Sub-dev III)

For an operator `A` on a finite-dimensional inner product space, `A = U |A|`, where
`|A| = (A⋆A)^{1/2}` is the modulus and `U` is a partial isometry with initial space `(ker A)ᗮ`
and `ker U = ker A`. When `A` is invertible, `U` is unitary and `U = A |A|⁻¹`.

* **RCLike route** (`E →ₗ[𝕜] E`, ℝ and ℂ): `|A|` built from the spectral square root
  (`TauCeti.IsPositive.sqrt`). Serves Davis's real-symmetric application directly.
* **CFC route / headline** (`E →L[ℂ] E`): `|A| = CFC.abs A` literally, transported across the
  definitional `LinearMap ↔ ContinuousLinearMap` adjoint bridge.

Sources: Horn & Johnson, *Matrix Analysis* 2nd ed., **Thm 7.3.1** (statement; `A = UQ`,
`Q = (A⋆A)^{1/2}`, `U` unitary, unique iff nonsingular). Conway, *A Course in Functional Analysis*
2nd ed., **VI.3.9** (the partial-isometry construction `A = U|A|`, `ker U = ker A` — the route
mathlib can follow, since HJ's SVD proof route is unavailable: mathlib has no SVD factorization).

## The three polar factors, and how they relate

Documented here because none of the three named the others, so a reviewer could
not tell a designed hierarchy from three independent
attempts. The separating hypotheses are the carrier, the field, and whether the
modulus is invertible:

* `TauCeti.polarFactor`, in `PolarDecomposition.lean` — square `E →ₗ[𝕜] E`,
  `RCLike`, finite dimension; a genuine **unitary** factor.
* `TauCeti.polarPartial`, in `PolarPartialIsometry.lean` — rectangular
  `E →L[ℂ] F` over `ℂ`, no invertibility assumed; a **partial isometry**.
* `TauCeti.polarIsometryOfIsUnitModulus`, in `PolarIsometry.lean` — rectangular
  `E →L[ℂ] F` over `ℂ` **and** the modulus a unit; then the factor is an
  **isometry**.

Read down the list: dropping finite dimension costs the unitary and leaves a
partial isometry; adding invertibility of the modulus buys it back as an
isometry. That is the whole hierarchy.
-/

public section

namespace TauCeti

open scoped InnerProductSpace
open LinearMap InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ### The modulus `|A|` (RCLike, LinearMap)

**There are two moduli in this library and they are not duplicates:**

* `TauCeti.operatorAbs`, below, is **square, `RCLike`-generic and finite-dimensional** —
  `(E →ₗ[𝕜] E) → (E →ₗ[𝕜] E)`, built from the spectral square root of `A⋆A`;
* `ContinuousLinearMap.modulus` in
  `ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean` is **rectangular
  and complex** — `(E →L[ℂ] F) → (E →L[ℂ] E)`, built from Mathlib's continuous
  functional calculus, which registers its C⋆-instances only over `ℂ`.

They agree exactly where both are defined, and the library proves it:
`operatorAbs_toContinuousLinearMap_eq_cfcAbs` below. Neither can be deleted in favour of
the other — one is more general in the field, the other in the shape.

The name is `operatorAbs`, not `operatorAbs`: a bare `operatorAbs` collides with the lattice
absolute value that `|·|` denotes in Lean, and `modulus` already names the
rectangular construction. This is the spelling the submitted roadmap states.
-/

/-- The **modulus** `|A| = (A⋆A)^{1/2}` of an operator, via the spectral square root of the
positive operator `A⋆A`. HJ 7.3.1 (`Q = (A⋆A)^{1/2}`). -/
@[expose]
noncomputable def operatorAbs (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  (LinearMap.isPositive_adjoint_comp_self A).sqrt

/-- The modulus is a positive operator, being a positive square root. -/
@[simp] theorem isPositive_operatorAbs (A : E →ₗ[𝕜] E) : (operatorAbs A).IsPositive :=
  (LinearMap.isPositive_adjoint_comp_self A).sqrt_isPositive

/-- `|A|² = A⋆A`. -/
theorem operatorAbs_mul_self (A : E →ₗ[𝕜] E) : operatorAbs A ∘ₗ operatorAbs A = A.adjoint ∘ₗ A :=
  (LinearMap.isPositive_adjoint_comp_self A).sqrt_mul_self

/-- **The polar norm identity** `‖|A| x‖ = ‖A x‖`. Not in HJ (SVD route); this is the seed of the
isometry route (Conway VI.3.9). -/
@[simp]
theorem norm_operatorAbs_apply (A : E →ₗ[𝕜] E) (x : E) : ‖operatorAbs A x‖ = ‖A x‖ := by
  have hsq : ‖operatorAbs A x‖ ^ 2 = ‖A x‖ ^ 2 :=
    ((LinearMap.isPositive_adjoint_comp_self A).sq_norm_sqrt_apply x).trans <| by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
  rw [← Real.sqrt_sq (norm_nonneg (operatorAbs A x)), ← Real.sqrt_sq (norm_nonneg (A x)), hsq]

/-- `ker |A| = ker A`. -/
theorem ker_operatorAbs (A : E →ₗ[𝕜] E) : ker (operatorAbs A) = ker A :=
  ((LinearMap.isPositive_adjoint_comp_self A).ker_sqrt).trans
    (LinearMap.ker_adjoint_comp_self A)

/-- `range |A| = (ker A)ᗮ` — the initial space of the polar factor. -/
theorem range_operatorAbs (A : E →ₗ[𝕜] E) : range (operatorAbs A) = (ker A)ᗮ := by
  rw [← ker_operatorAbs A, LinearMap.orthogonal_ker, (isPositive_operatorAbs A).adjoint_eq]

/-- Elementwise form of `range_operatorAbs`: every value of the modulus lies in the initial
space. -/
theorem operatorAbs_apply_mem_orthogonal_ker (A : E →ₗ[𝕜] E) (x : E) :
    operatorAbs A x ∈ (ker A)ᗮ := by
  rw [← range_operatorAbs A]
  exact LinearMap.mem_range_self (operatorAbs A) x

/-! ### The polar factor `U` and the decomposition -/

/-- The restriction of the modulus `|A|` to `(ker A)ᗮ = range |A|`, as a linear automorphism of
`(ker A)ᗮ` — the invertible core of `|A|`, which the polar factor inverts. -/
noncomputable def operatorAbsRestrict (A : E →ₗ[𝕜] E) : ↥((ker A)ᗮ) ≃ₗ[𝕜] ↥((ker A)ᗮ) :=
  LinearEquiv.ofBijective
      ((operatorAbs A).restrict fun x _ => operatorAbs_apply_mem_orthogonal_ker A x) <| by
    have hinj : Function.Injective
        ((operatorAbs A).restrict (p := (ker A)ᗮ)
          fun x _ => operatorAbs_apply_mem_orthogonal_ker A x) := by
      intro y z hyz
      have habs : operatorAbs A ↑y = operatorAbs A ↑z := congrArg Subtype.val hyz
      have hker : (↑y - ↑z : E) ∈ ker (operatorAbs A) := by
        rw [LinearMap.mem_ker, map_sub, habs, sub_self]
      rw [ker_operatorAbs A] at hker
      have hmem : (↑y - ↑z : E) ∈ (ker A)ᗮ := Submodule.sub_mem _ y.2 z.2
      exact Subtype.ext <| sub_eq_zero.mp <|
        Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint (ker A)) _ hker hmem
    exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The **polar factor** `U` of `A`: the partial isometry that is the isometry `|A| x ↦ A x` on
`range |A| = (ker A)ᗮ`, extended by `0` on `ker A`. Conway VI.3.9. -/
@[expose]
noncomputable def polarFactor (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  A ∘ₗ ((ker A)ᗮ).subtype ∘ₗ (operatorAbsRestrict A).symm.toLinearMap
    ∘ₗ (((ker A)ᗮ).orthogonalProjectionOnto : E →L[𝕜] ↥((ker A)ᗮ)).toLinearMap

/-- The defining property of the polar factor: `U (|A| x) = A x`. -/
@[simp]
theorem polarFactor_apply_operatorAbs_apply (A : E →ₗ[𝕜] E) (x : E) :
    polarFactor A (operatorAbs A x) = A x := by
  have habs : operatorAbs A x ∈ (ker A)ᗮ := operatorAbs_apply_mem_orthogonal_ker A x
  have hproj : ((ker A)ᗮ).orthogonalProjectionOnto (operatorAbs A x) = ⟨operatorAbs A x, habs⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨operatorAbs A x, habs⟩
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change A ↑((operatorAbsRestrict A).symm
    (((ker A)ᗮ).orthogonalProjectionOnto (operatorAbs A x))) = A x
  rw [hproj]
  have h1 : operatorAbs A ↑((operatorAbsRestrict A).symm ⟨operatorAbs A x, habs⟩)
      = operatorAbs A x :=
    congrArg Subtype.val ((operatorAbsRestrict A).apply_symm_apply ⟨operatorAbs A x, habs⟩)
  have hker : (↑((operatorAbsRestrict A).symm ⟨operatorAbs A x, habs⟩) - x : E)
      ∈ ker (operatorAbs A) := by
    rw [LinearMap.mem_ker, map_sub, h1, sub_self]
  rw [ker_operatorAbs A] at hker
  have h2 := LinearMap.mem_ker.mp hker
  rwa [map_sub, sub_eq_zero] at h2

/-- **Polar decomposition** `A = U |A|`. Conway VI.3.9; HJ 7.3.1. -/
theorem polar_decomposition (A : E →ₗ[𝕜] E) :
    A = polarFactor A ∘ₗ operatorAbs A := by
  ext x
  exact (polarFactor_apply_operatorAbs_apply A x).symm

/-- `ker U = ker A`. -/
theorem ker_polarFactor (A : E →ₗ[𝕜] E) : ker (polarFactor A) = ker A := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hUx
    have hyker : (↑((operatorAbsRestrict A).symm
        (((ker A)ᗮ).orthogonalProjectionOnto x)) : E) ∈ ker A :=
      LinearMap.mem_ker.mpr hUx
    have hy0 : ((operatorAbsRestrict A).symm (((ker A)ᗮ).orthogonalProjectionOnto x)) = 0 :=
      Subtype.ext <| Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint (ker A)) _
        hyker ((operatorAbsRestrict A).symm _).2
    have hproj : ((ker A)ᗮ).orthogonalProjectionOnto x = 0 := by
      have := congrArg (operatorAbsRestrict A) hy0
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal] at hproj
    exact LinearMap.mem_ker.mp hproj
  · intro hx
    have hproj : ((ker A)ᗮ).orthogonalProjectionOnto x = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
        (by rwa [Submodule.orthogonal_orthogonal])
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A ↑((operatorAbsRestrict A).symm (((ker A)ᗮ).orthogonalProjectionOnto x)) = 0
    rw [hproj, map_zero]
    simp

/-- `range U = range A` — the final space of the polar factor. -/
theorem range_polarFactor (A : E →ₗ[𝕜] E) : range (polarFactor A) = range A := by
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨x, rfl⟩ := hy
    exact ⟨_, rfl⟩
  · obtain ⟨x, rfl⟩ := hy
    exact ⟨operatorAbs A x, polarFactor_apply_operatorAbs_apply A x⟩

/-- `U` restricted to `range |A| = (ker A)ᗮ` is isometric. -/
theorem norm_polarFactor_apply_of_mem {A : E →ₗ[𝕜] E} {x : E} (hx : x ∈ (ker A)ᗮ) :
    ‖polarFactor A x‖ = ‖x‖ := by
  have hproj : ((ker A)ᗮ).orthogonalProjectionOnto x = ⟨x, hx⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩
  -- names the application so the norm bound applies to it directly.
  change ‖A ↑((operatorAbsRestrict A).symm (((ker A)ᗮ).orthogonalProjectionOnto x))‖ = ‖x‖
  rw [hproj, ← norm_operatorAbs_apply,
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    show operatorAbs A ↑((operatorAbsRestrict A).symm ⟨x, hx⟩) = x from
      congrArg Subtype.val ((operatorAbsRestrict A).apply_symm_apply ⟨x, hx⟩)]

/-- `U` is a partial isometry. -/
theorem isPartialIsometry_polarFactor (A : E →ₗ[𝕜] E) :
    IsPartialIsometry (polarFactor A) :=
  isPartialIsometry_of_isometryOn (K := (ker A)ᗮ)
    (by rw [ker_polarFactor, Submodule.orthogonal_orthogonal])
    (fun _ hx => norm_polarFactor_apply_of_mem hx)

/-! ### Invertible case: `U` is unitary -/

/-- When `A` is invertible, `|A|` is invertible and the polar factor is the unitary `U = A |A|⁻¹`,
packaged as a `LinearIsometryEquiv`. HJ 7.3.1(b) (`U` uniquely determined if `A` nonsingular). -/
@[expose]
noncomputable def polarUnitaryEquiv {A : E →ₗ[𝕜] E} (hA : IsUnit A) : E ≃ₗᵢ[𝕜] E :=
  have hinj : Function.Injective (polarFactor A) := by
    rw [← LinearMap.ker_eq_bot, ker_polarFactor]
    exact (LinearMap.isUnit_iff_ker_eq_bot A).mp hA
  { LinearEquiv.ofBijective (polarFactor A)
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩ with
    norm_map' := fun x => norm_polarFactor_apply_of_mem <| by
      rw [(LinearMap.isUnit_iff_ker_eq_bot A).mp hA, Submodule.bot_orthogonal_eq_top]
      exact Submodule.mem_top }

/-- The bundled polar unitary acts as the chosen one. -/
@[simp] theorem coe_polarUnitaryEquiv {A : E →ₗ[𝕜] E} (hA : IsUnit A) :
    ((polarUnitaryEquiv hA : E →ₗ[𝕜] E)) = polarFactor A :=
  rfl

/-- **Polar decomposition** for an operator with invertible modulus: `A = U |A|` with `U`
unitary. -/
theorem polar_decomposition_of_isUnit {A : E →ₗ[𝕜] E} (hA : IsUnit A) :
    A = (polarUnitaryEquiv hA : E →ₗ[𝕜] E) ∘ₗ operatorAbs A := by
  rw [coe_polarUnitaryEquiv]
  exact polar_decomposition A

/-! ### General square case: a kernel-completed unitary

Even for a singular `A`, the partial isometry `polarFactor A` extends to a
genuine unitary `E ≃ₗᵢ[𝕜] E` — map the initial space `(ker A)ᗮ` by
`polarFactor A` (isometrically onto `range A`) and complete `ker A`
isometrically onto `(range A)ᗮ` (equal dimensions by rank–nullity).  The
identity `A = U |A|` survives, and `U` is a true unitary; this is the factor the
orthogonal-Procrustes alignment argument needs (`polarUnitaryEquiv` above
requires invertibility).

**The completion is a choice, not a canonical construction.**  When `ker A ≠ ⊥`
*any* unitary from `ker A` onto `(range A)ᗮ` completes `polarFactor A`, and
`LinearIsometry.extend` merely selects one; only the restriction to `(ker A)ᗮ`
is determined by `A`.  Hence the name `choosePolarUnitary` rather than
`polarUnitary`: the invertible case, where the unitary factor really is unique,
is `polarUnitaryEquiv` above.

Users who need only *some* unitary factor should prefer
`exists_polar_decomposition_unitary`, which states the theorem without
committing to the selection. -/

/-- The polar factor restricted to `(ker A)ᗮ`, its initial space, where it is a
genuine linear isometry. -/
private noncomputable def polarIsometryOnOrthogonal (A : E →ₗ[𝕜] E) :
    ↥((ker A)ᗮ) →ₗᵢ[𝕜] E where
  toLinearMap := (polarFactor A) ∘ₗ ((ker A)ᗮ).subtype
  norm_map' x := norm_polarFactor_apply_of_mem x.2

/-- **A selected polar unitary (general square case).** A kernel-completed
unitary extending `polarFactor A`; unitary for every `A`, singular or not.

Not canonical when `A` is singular — see the section note above. -/
noncomputable def choosePolarUnitary (A : E →ₗ[𝕜] E) : E ≃ₗᵢ[𝕜] E :=
  LinearIsometryEquiv.ofSurjective (polarIsometryOnOrthogonal A).extend
    (LinearMap.injective_iff_surjective.mp (polarIsometryOnOrthogonal A).extend.injective)

/-- The chosen polar unitary satisfies the defining identity `U (|A| x) = A x`.  It is *a* choice --
see `choosePolarUnitary` -- but every choice satisfies this. -/
@[simp]
theorem choosePolarUnitary_apply_operatorAbs_apply (A : E →ₗ[𝕜] E) (x : E) :
    choosePolarUnitary A (operatorAbs A x) = A x := by
  have hmem : operatorAbs A x ∈ (ker A)ᗮ := operatorAbs_apply_mem_orthogonal_ker A x
  rw [choosePolarUnitary, LinearIsometryEquiv.coe_ofSurjective,
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    show operatorAbs A x = ((⟨operatorAbs A x, hmem⟩ : ↥((ker A)ᗮ)) : E) from rfl,
    LinearIsometry.extend_apply]
  exact polarFactor_apply_operatorAbs_apply A x

/-- **Polar decomposition with a unitary factor** (general square case),
`A = U |A|` at the selected witness `U = choosePolarUnitary A`.

For the statement that does not name a witness, use
`exists_polar_decomposition_unitary`. -/
theorem polar_decomposition_choosePolarUnitary (A : E →ₗ[𝕜] E) :
    A = (choosePolarUnitary A : E →ₗ[𝕜] E) ∘ₗ operatorAbs A := by
  ext x
  simp only [LinearMap.comp_apply]
  exact (choosePolarUnitary_apply_operatorAbs_apply A x).symm

/-- **Polar decomposition with a unitary factor**, existential form.

This is the honest general-case statement: every square operator on a
finite-dimensional space factors as a unitary times its modulus.  It says
nothing about *which* unitary, which is the point — for singular `A` the factor
is not unique.  `choosePolarUnitary` provides a witness when a concrete one is
needed. -/
theorem exists_polar_decomposition_unitary (A : E →ₗ[𝕜] E) :
    ∃ U : E ≃ₗᵢ[𝕜] E, A = (U : E →ₗ[𝕜] E) ∘ₗ operatorAbs A :=
  ⟨choosePolarUnitary A, polar_decomposition_choosePolarUnitary A⟩

/-- The modulus of a normal finite-dimensional operator commutes with the
operator.  This is the finite `RCLike` substitute for the corresponding CFC
commutation theorem. -/
theorem operatorAbs_comm_of_normal {A : E →ₗ[𝕜] E}
    (hnormal : A.adjoint ∘ₗ A = A ∘ₗ A.adjoint) :
    A ∘ₗ operatorAbs A = operatorAbs A ∘ₗ A := by
  have hcomm : A ∘ₗ (A.adjoint ∘ₗ A) =
      (A.adjoint ∘ₗ A) ∘ₗ A := by
    rw [← LinearMap.comp_assoc, ← hnormal]
  exact TauCeti.sqrt_comm
    (LinearMap.isPositive_adjoint_comp_self A) hcomm

/-- Uniqueness of the unitary factor in an invertible polar decomposition.
If `A = U H` with `U` unitary and `H` positive, then the canonical polar factor
of `A` is `U`. -/
theorem polarFactor_eq_of_isUnit_eq_comp_positive
    {A H : E →ₗ[𝕜] E} (hA : IsUnit A)
    (U : E ≃ₗᵢ[𝕜] E) (hH : H.IsPositive)
    (hdecomp : A = U.toLinearMap ∘ₗ H) :
    polarFactor A = U.toLinearMap := by
  have hgram : H ∘ₗ H = A.adjoint ∘ₗ A := by
    rw [hdecomp, LinearMap.adjoint_comp, U.adjoint_toLinearMap_eq_symm,
      hH.adjoint_eq]
    ext x
    simp [LinearMap.comp_apply]
  have hHabs : H = operatorAbs A := by
    exact (LinearMap.isPositive_adjoint_comp_self A).sqrt_unique hH hgram
  have habsinj : Function.Injective (operatorAbs A) := by
    rw [← LinearMap.ker_eq_bot, ker_operatorAbs,
      (LinearMap.isUnit_iff_ker_eq_bot _).mp hA]
  have habssurj : Function.Surjective (operatorAbs A) :=
    LinearMap.injective_iff_surjective.mp habsinj
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := habssurj x
  rw [polarFactor_apply_operatorAbs_apply]
  have hy := LinearMap.congr_fun hdecomp y
  simpa [LinearMap.comp_apply, hHabs] using hy

/-- For an invertible operator the polar factor of the adjoint is the adjoint
of the polar factor: from `A = U|A|` one gets `A⋆ = U⋆ ∘ (U|A|U⋆)` with the
conjugated modulus positive, and polar uniqueness identifies the factors. -/
theorem polarFactor_adjoint_of_isUnit {A : E →ₗ[𝕜] E} (hA : IsUnit A) :
    polarFactor (LinearMap.adjoint A) = LinearMap.adjoint (polarFactor A) := by
  have hA' : IsUnit (LinearMap.adjoint A) := by
    obtain ⟨B, hAB, hBA⟩ := isUnit_iff_exists.mp hA
    refine isUnit_iff_exists.mpr ⟨LinearMap.adjoint B, ?_, ?_⟩
    · rw [show LinearMap.adjoint A * LinearMap.adjoint B
          = LinearMap.adjoint (B ∘ₗ A) from (LinearMap.adjoint_comp B A).symm,
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        show B ∘ₗ A = (1 : E →ₗ[𝕜] E) from hBA]
      exact LinearMap.adjoint_id
    · rw [show LinearMap.adjoint B * LinearMap.adjoint A
          = LinearMap.adjoint (A ∘ₗ B) from (LinearMap.adjoint_comp A B).symm,
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        show A ∘ₗ B = (1 : E →ₗ[𝕜] E) from hAB]
      exact LinearMap.adjoint_id
  set R := polarUnitaryEquiv hA with hRdef
  have hpos : (R.toLinearMap ∘ₗ operatorAbs A ∘ₗ R.symm.toLinearMap).IsPositive := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv]
      calc ⟪R (operatorAbs A (R.symm x)), y⟫_𝕜
          = ⟪R (operatorAbs A (R.symm x)), R (R.symm y)⟫_𝕜 := by
            rw [R.apply_symm_apply]
        _ = ⟪operatorAbs A (R.symm x), R.symm y⟫_𝕜 := R.inner_map_map _ _
        _ = ⟪R.symm x, operatorAbs A (R.symm y)⟫_𝕜 :=
            (isPositive_operatorAbs A).isSymmetric _ _
        _ = ⟪R (R.symm x), R (operatorAbs A (R.symm y))⟫_𝕜 :=
            (R.inner_map_map _ _).symm
        _ = ⟪x, R (operatorAbs A (R.symm y))⟫_𝕜 := by rw [R.apply_symm_apply]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv]
      calc (0 : ℝ)
          ≤ RCLike.re ⟪operatorAbs A (R.symm x), R.symm x⟫_𝕜 :=
            (isPositive_operatorAbs A).re_inner_nonneg_left _
        _ = RCLike.re ⟪R (operatorAbs A (R.symm x)), R (R.symm x)⟫_𝕜 := by
            rw [R.inner_map_map]
        _ = RCLike.re ⟪R (operatorAbs A (R.symm x)), x⟫_𝕜 := by
            rw [R.apply_symm_apply]
  have hdecomp : LinearMap.adjoint A =
      R.symm.toLinearMap ∘ₗ (R.toLinearMap ∘ₗ operatorAbs A ∘ₗ R.symm.toLinearMap) := by
    conv_lhs => rw [polar_decomposition_of_isUnit hA]
    rw [LinearMap.adjoint_comp, (isPositive_operatorAbs A).adjoint_eq]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rw [show LinearMap.adjoint ((polarUnitaryEquiv hA : E →ₗ[𝕜] E)) x
        = R.symm x from LinearMap.congr_fun R.adjoint_toLinearMap_eq_symm x,
      R.symm_apply_apply]
  have hfac := polarFactor_eq_of_isUnit_eq_comp_positive hA' R.symm hpos hdecomp
  rw [hfac, ← R.adjoint_toLinearMap_eq_symm]
  exact congrArg LinearMap.adjoint (coe_polarUnitaryEquiv hA)

/-! ### CFC bridge — the ℂ / ContinuousLinearMap headline (`|A| = CFC.abs A`)

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.PolarDecomposition`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `3676b55`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

section CFCBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [CompleteSpace H]

/-- **Endomorphisms and bounded operators are the same algebra in finite dimension.**

Every linear endomorphism of a finite-dimensional normed space is continuous, so
`LinearMap.toContinuousLinearMap` is a linear equivalence; composition is the multiplication
on both sides, which makes it an algebra equivalence. Mathlib has the linear equivalence but
not this upgrade, and `AlgEquiv.spectrum_eq` across it is what carries eigenvalue facts about
a `Module.End` over to the `ContinuousLinearMap` the functional calculus is stated for. -/
noncomputable def endAlgEquivContinuousLinearMap : Module.End ℂ H ≃ₐ[ℂ] (H →L[ℂ] H) :=
  AlgEquiv.ofLinearEquiv LinearMap.toContinuousLinearMap (by ext x; rfl)
    (fun f g => by ext x; rfl)

omit [CompleteSpace H] in
/-- **Each eigenvalue lies in the real spectrum of the bounded operator.**

The containment the continuous functional calculus bridge needs: it lets a
`g : C(spectrum ℝ T.toContinuousLinearMap, ℝ)` be extended off the spectrum without changing
the finite calculus, and turns the Parseval bound of
`norm_selfAdjointFunctionalCalculus_apply_le` into `‖φ g‖ ≤ ‖g‖_∞`. -/
theorem eigenvalues_mem_spectrum_toContinuousLinearMap {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric)
    (i : Fin (Module.finrank ℂ H)) :
    (hT.eigenvalues rfl i : ℝ) ∈ spectrum ℝ T.toContinuousLinearMap := by
  have hvec : Module.End.HasEigenvector T ((hT.eigenvalues rfl i : ℝ) : ℂ)
      (hT.eigenvectorBasis rfl i) := by
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      exact hT.apply_eigenvectorBasis rfl i
    · simpa using (hT.eigenvectorBasis rfl).orthonormal.ne_zero i
  have hev := Module.End.hasEigenvalue_of_hasEigenvector hvec
  have hC : ((hT.eigenvalues rfl i : ℝ) : ℂ) ∈ spectrum ℂ T.toContinuousLinearMap := by
    have hsp := AlgEquiv.spectrum_eq endAlgEquivContinuousLinearMap T
    rw [show T.toContinuousLinearMap = endAlgEquivContinuousLinearMap T from rfl, hsp]
    exact hev.mem_spectrum
  rw [← spectrum.preimage_algebraMap (R := ℝ) ℂ]
  exact hC

open scoped Classical in
/-- **The finite calculus as a continuous star-algebra homomorphism.**

The bundle `cfcHom_eq_of_continuous_of_map_id` consumes. A symbol on the spectrum is extended
by zero; `selfAdjointFunctionalCalculus_indicator` together with the eigenvalue containment
makes that extension invisible, so each field is the corresponding algebraic lemma about the
calculus. -/
noncomputable def calculusStarAlgHom {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric) :
    C(spectrum ℝ T.toContinuousLinearMap, ℝ) →⋆ₐ[ℝ] (H →L[ℂ] H) where
  toFun g := (selfAdjointFunctionalCalculus hT (extendSymbol g)).toContinuousLinearMap
  map_one' := by
    rw [extendSymbol_one_eq_indicator,
      selfAdjointFunctionalCalculus_indicator hT
        (eigenvalues_mem_spectrum_toContinuousLinearMap hT),
      selfAdjointFunctionalCalculus_one hT]
    ext x; rfl
  map_mul' g₁ g₂ := by
    -- explicit arguments: the lambda pattern in `_comp` defeats higher-order unification
    rw [extendSymbol_mul,
      ← selfAdjointFunctionalCalculus_comp hT (extendSymbol g₁) (extendSymbol g₂)]
    ext x; rfl
  map_zero' := by
    rw [extendSymbol_zero, selfAdjointFunctionalCalculus_zero hT]
    ext x; rfl
  map_add' g₁ g₂ := by
    rw [extendSymbol_add, selfAdjointFunctionalCalculus_add hT]
    ext x; rfl
  commutes' r := by
    have hr : extendSymbol (algebraMap ℝ C(spectrum ℝ T.toContinuousLinearMap, ℝ) r)
        = (spectrum ℝ T.toContinuousLinearMap).indicator (fun _ => r) := by
      exact extendSymbol_eq_indicator _ _ fun _ _ => rfl
    rw [hr, selfAdjointFunctionalCalculus_indicator hT
        (eigenvalues_mem_spectrum_toContinuousLinearMap hT),
      show (fun _ : ℝ => r) = r • (fun _ : ℝ => (1 : ℝ)) from by funext _; simp,
      selfAdjointFunctionalCalculus_smul hT, selfAdjointFunctionalCalculus_one hT]
    ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' g := by
    have hstar : star g = g := rfl
    rw [hstar]
    refine (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_).symm
    intro x y
    exact selfAdjointFunctionalCalculus_isSymmetric hT (extendSymbol g) x y

/-- The bundle sends the identity symbol to the operator, one of the two hypotheses of
`cfcHom_eq_of_continuous_of_map_id`. -/
theorem calculusStarAlgHom_id {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric) :
    calculusStarAlgHom hT
        (ContinuousMap.restrict (spectrum ℝ T.toContinuousLinearMap) (ContinuousMap.id ℝ))
      = T.toContinuousLinearMap := by
  have hmem := eigenvalues_mem_spectrum_toContinuousLinearMap hT
  have hext : extendSymbol
      (ContinuousMap.restrict (spectrum ℝ T.toContinuousLinearMap) (ContinuousMap.id ℝ))
      = (spectrum ℝ T.toContinuousLinearMap).indicator (id : ℝ → ℝ) := by
    exact extendSymbol_eq_indicator _ _ fun _ _ => rfl
  have key : (selfAdjointFunctionalCalculus hT (extendSymbol
      (ContinuousMap.restrict (spectrum ℝ T.toContinuousLinearMap)
        (ContinuousMap.id ℝ)))).toContinuousLinearMap = T.toContinuousLinearMap := by
    rw [hext, selfAdjointFunctionalCalculus_indicator hT hmem,
      selfAdjointFunctionalCalculus_id hT]
  exact key

/-- The bundle is bounded by the sup norm of the symbol, hence continuous: the other
hypothesis of `cfcHom_eq_of_continuous_of_map_id`. -/
theorem norm_calculusStarAlgHom_le {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric)
    (g : C(spectrum ℝ T.toContinuousLinearMap, ℝ)) :
    ‖calculusStarAlgHom hT g‖ ≤ ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun x => ?_
  refine norm_selfAdjointFunctionalCalculus_apply_le hT _ (norm_nonneg g) (fun i => ?_) x
  have hmem := eigenvalues_mem_spectrum_toContinuousLinearMap hT i
  rw [extendSymbol_apply_of_mem _ hmem]
  simpa using g.norm_coe_le_norm ⟨_, hmem⟩

/-- **The two calculi agree**: the `RCLike` finite functional calculus, transported to bounded
operators, is Mathlib's continuous functional calculus.

Part A's milestone.  `calculusStarAlgHom` is continuous and sends the identity symbol to the
operator, so `cfcHom_eq_of_continuous_of_map_id` identifies it with `cfcHom`; the extension of
a symbol off the spectrum is invisible to the finite calculus, by
`selfAdjointFunctionalCalculus_indicator` and the eigenvalue containment. -/
theorem selfAdjointFunctionalCalculus_toContinuousLinearMap_eq_cfc {T : H →ₗ[ℂ] H}
    (hT : T.IsSymmetric) (f : ℝ → ℝ) (hf : Continuous f) :
    (selfAdjointFunctionalCalculus hT f).toContinuousLinearMap
      = cfc f T.toContinuousLinearMap := by
  have ha : IsSelfAdjoint T.toContinuousLinearMap :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT
  have hcont : Continuous (calculusStarAlgHom hT) :=
    AddMonoidHomClass.continuous_of_bound (calculusStarAlgHom hT) 1 fun g => by
      rw [one_mul]; exact norm_calculusStarAlgHom_le hT g
  have hhom : cfcHom ha = calculusStarAlgHom hT :=
    cfcHom_eq_of_continuous_of_map_id ha _ hcont (calculusStarAlgHom_id hT)
  rw [cfc_apply f T.toContinuousLinearMap ha hf.continuousOn, hhom]
  have key : (selfAdjointFunctionalCalculus hT
      (extendSymbol (⟨_, hf.continuousOn.restrict⟩ :
        C(spectrum ℝ T.toContinuousLinearMap, ℝ)))).toContinuousLinearMap
      = (selfAdjointFunctionalCalculus hT f).toContinuousLinearMap := by
    congr 1
    refine selfAdjointFunctionalCalculus_congr hT fun i => ?_
    rw [extendSymbol_apply_of_mem _ (eigenvalues_mem_spectrum_toContinuousLinearMap hT i)]
    rfl
  exact key.symm

/-- The spectral modulus agrees with the C⋆-algebra `CFC.abs` on `E →L[ℂ] E`, transported across
the definitional `LinearMap ↔ ContinuousLinearMap` adjoint bridge (`adjoint_toContinuousLinearMap`
is `rfl`). This is what makes the decomposition literally "via CFC". -/
theorem operatorAbs_toContinuousLinearMap_eq_cfcAbs (A : H →ₗ[ℂ] H) :
    (operatorAbs A).toContinuousLinearMap = CFC.abs A.toContinuousLinearMap := by
  refine (CFC.sqrt_unique ?_ ?_).symm
  · -- `|A|.toCLM * |A|.toCLM = star A.toCLM * A.toCLM`, transported from
    -- `operatorAbs_mul_self` across
    -- the definitional `LinearMap ↔ ContinuousLinearMap` adjoint bridge.
    ext x
    exact congrArg (fun f : H →ₗ[ℂ] H => f x) (operatorAbs_mul_self A)
  · exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      ((LinearMap.isPositive_toContinuousLinearMap_iff (operatorAbs A)).mpr
        (isPositive_operatorAbs A))

/-- **Headline (via CFC):** every `A : H →L[ℂ] H` factors as `A = U ∘L CFC.abs A` with `U` a
partial isometry. -/
theorem continuousLinearMap_polar_decomposition (A : H →L[ℂ] H) :
    ∃ U : H →L[ℂ] H, IsPartialIsometry U ∧ A = U ∘L CFC.abs A := by
  refine ⟨(polarFactor (A : H →ₗ[ℂ] H)).toContinuousLinearMap, ?_, ?_⟩
  · -- transport `IsPartialIsometry` across the (definitional) star-monoid bridge
    have h := isPartialIsometry_polarFactor (A : H →ₗ[ℂ] H)
    ext x
    exact congrArg (fun f : H →ₗ[ℂ] H => f x) h
  · rw [show CFC.abs A = CFC.abs ((A : H →ₗ[ℂ] H)).toContinuousLinearMap from rfl,
      ← operatorAbs_toContinuousLinearMap_eq_cfcAbs (A : H →ₗ[ℂ] H)]
    ext x
    exact congrArg (fun f : H →ₗ[ℂ] H => f x) (polar_decomposition (A : H →ₗ[ℂ] H))

end CFCBridge

end TauCeti
