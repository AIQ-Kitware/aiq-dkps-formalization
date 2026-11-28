/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: the normalised self-adjoint Krein/Julia column completion.
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Completeness
public import TauCeti.Analysis.InnerProductSpace.Positive.Basic
public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import ForTauCeti.Analysis.InnerProductSpace.Gram.Domination
public import ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.RealAlgebra
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# A contractive column has a self-adjoint contractive completion

Let `E` and `F` be complex Hilbert spaces, `A : E →L[ℂ] E` self-adjoint and
`B : E →L[ℂ] F` arbitrary, and suppose the column

```
[ A ]
[ B ]
```

is a contraction, in the operator-inequality form `A⋆A + B⋆B ≤ 1`.  Then that
column is the **first block column of a self-adjoint contraction on `E ⊕₂ F`**:

```
∃ K : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F),
  IsSelfAdjoint K ∧ ‖K‖ ≤ 1 ∧ K ∘L l2Inl = l2Column A B.
```

This is the normalised Krein extension: the caller supplies only `A`, `B` and
the Gram inequality — no defect operator, no `Γ`, no Julia operator, no
lower-right block and no completion certificate.  All of that is built here.

## The construction

With `A⋆ = A` the hypothesis reads `A² + B⋆B ≤ 1`, so the **defect**

```
G := 1 - A²
```

satisfies `B⋆B ≤ G` and in particular `0 ≤ G`.  Let `D := √G` be its positive
square root (`CFC.sqrt`; this is why the theorem is stated over `ℂ`, where
Mathlib registers the continuous functional calculus on `E →L[ℂ] E`).  Then

* `D⋆ = D` and `D² = G`, so `A² + D² = 1`;
* `A` commutes with `G`, hence with `D`, by `Commute.cfcₙ_nnreal`;
* `B⋆B ≤ D²`, so `ContinuousLinearMap.exists_contraction_of_gram_le` — the
  specialised Douglas factorisation proved in
  `ForTauCeti/Analysis/InnerProductSpace/Gram/Domination.lean` — produces
  a contraction `Γ : E →L[ℂ] F` with `Γ D = B`.

The **Julia operator** of `A` is the block operator on `E ⊕₂ E`

```
        [ A   D ]
J_A  =  [       ],
        [ D  -A ]
```

self-adjoint because `A` and `D` are, and an involution because `A² + D² = 1`
and `A` commutes with `D`.  A self-adjoint involution is unitary, so `‖J_A‖ ≤ 1`.
Damping the second coordinate by `Γ` through the block-diagonal contraction

```
        [ 1   0 ]
L    =  [       ] : E ⊕₂ E →L E ⊕₂ F
        [ 0   Γ ]
```

uses TauCeti’s `ContinuousLinearMap.withLpProdMap` and its norm law. The completion is

```
K := L J_A L⋆,
```

self-adjoint by `adjoint_comp`, contractive by submultiplicativity, and with
first block column `[A; ΓD] = [A; B]` because `L⋆` and `L` fix the first
coordinate.

## Main definitions and results

* `TauCeti.l2Column`: the column `x ↦ (a x, b x)` into an `L²` product;
* `TauCeti.l2Inl`: the first-coordinate inclusion `x ↦ (x, 0)`;
* `TauCeti.l2Block`: the `2 × 2` block operator between `L²` products, with its
  application, composition and adjoint laws for arbitrary blocks;
* `TauCeti.exists_selfAdjoint_contraction_extension_of_column_gram_le`: the
  capstone;
* `TauCeti.exists_selfAdjoint_norm_one_extension_of_column`: the normalised
  corollary, where a column of norm exactly `1` completes to a self-adjoint
  operator of norm exactly `1`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti`.
-/

public section

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower

namespace TauCeti

open scoped InnerProductSpace

universe u v w x y

/-! ### Columns and the first-coordinate inclusion -/

section Column

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- The **column** `[a; b] : x ↦ (a x, b x)` into the Hilbert `L²` product. -/
noncomputable def l2Column (a : E →L[𝕜] F) (b : E →L[𝕜] G) :
    E →L[𝕜] WithLp 2 (F × G) :=
  ((WithLp.prodContinuousLinearEquiv 2 𝕜 F G).symm :
      (F × G) →L[𝕜] WithLp 2 (F × G)) ∘L a.prod b

/-- The column, applied: both coordinates come from the same argument. -/
@[simp]
theorem l2Column_apply (a : E →L[𝕜] F) (b : E →L[𝕜] G) (z : E) :
    l2Column a b z = WithLp.toLp 2 (a z, b z) := (rfl)

end Column

/-! ### The Gram inequality of a contractive column -/

section ColumnGram

variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **A contractive column has a contractive Gram operator.**

`‖[a; b]‖ ≤ 1` gives `a⋆a + b⋆b ≤ 1` in the Loewner order, because both sides
have the same quadratic form: `⟪x, (a⋆a + b⋆b) x⟫ = ‖a x‖² + ‖b x‖²` is the
squared `L²` norm of the column value.  This is the form in which the
normalised Krein completion consumes a column bound. -/
theorem l2Column_gram_le_id_of_norm_le_one (a : E →L[ℂ] F) (b : E →L[ℂ] G)
    (h : ‖l2Column a b‖ ≤ 1) :
    ContinuousLinearMap.adjoint a ∘L a + ContinuousLinearMap.adjoint b ∘L b ≤
      ContinuousLinearMap.id ℂ E := by
  have hgram : (l2Column a b).adjoint ∘L l2Column a b =
      a.adjoint ∘L a + b.adjoint ∘L b := by
    ext x
    apply ext_inner_right ℂ
    intro y
    simp only [ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.adjoint_inner_left, l2Column_apply, WithLp.prod_inner_apply,
      inner_add_left]
  rw [← hgram]
  simpa only [ContinuousLinearMap.adjoint_adjoint, LinearIsometryEquiv.norm_map,
    ContinuousLinearMap.one_def] using
    (ContinuousLinearMap.self_comp_adjoint_le_one_iff (l2Column a b).adjoint).2
      ((LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (l2Column a b)).trans_le h)

end ColumnGram

section Inl

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The **first-coordinate inclusion** `x ↦ (x, 0)` into the Hilbert `L²`
product. It is the native product inclusion transported to `WithLp 2`. -/
noncomputable def l2Inl : E →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl 𝕜 E F

/-- `l2Inl` unfolded as a column; the defining equation, kept as a lemma so that
consumers rewrite rather than unfold. -/
theorem l2Inl_eq_l2Column :
    (l2Inl : E →L[𝕜] WithLp 2 (E × F))
      = l2Column (ContinuousLinearMap.id 𝕜 E) (0 : E →L[𝕜] F) := (rfl)

/-- The first-coordinate inclusion, applied. -/
@[simp]
theorem l2Inl_apply (z : E) :
    (l2Inl : E →L[𝕜] WithLp 2 (E × F)) z = WithLp.toLp 2 (z, (0 : F)) := (rfl)

end Inl

/-! ### The `2 × 2` block calculus on Hilbert `L²` products -/

section Block

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v} {G : Type w} {H : Type x}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

omit [NormedAddCommGroup E] [NormedAddCommGroup F] in
/-- Extensionality for the Hilbert `L²` product: two elements agreeing in both
coordinates are equal. -/
theorem l2_ext {z w : WithLp 2 (E × F)} (h₁ : z.fst = w.fst) (h₂ : z.snd = w.snd) :
    z = w :=
  (WithLp.ext_iff (p := 2)).mpr (Prod.ext_iff.mpr ⟨h₁, h₂⟩)

/-- The **block operator**

```
[ a  b ]
[ c  d ]
```

from `E ⊕₂ F` to `G ⊕₂ H`.  It is the column of its two block rows. -/
noncomputable def l2Block (a : E →L[𝕜] G) (b : F →L[𝕜] G)
    (c : E →L[𝕜] H) (d : F →L[𝕜] H) :
    WithLp 2 (E × F) →L[𝕜] WithLp 2 (G × H) :=
  l2Column (a ∘L WithLp.fstL 2 𝕜 E F + b ∘L WithLp.sndL 2 𝕜 E F)
    (c ∘L WithLp.fstL 2 𝕜 E F + d ∘L WithLp.sndL 2 𝕜 E F)

/-- The block operator, applied: each output coordinate is the corresponding
block row against the two input coordinates. -/
@[simp]
theorem l2Block_apply (a : E →L[𝕜] G) (b : F →L[𝕜] G)
    (c : E →L[𝕜] H) (d : F →L[𝕜] H) (z : WithLp 2 (E × F)) :
    l2Block a b c d z = WithLp.toLp 2 (a z.fst + b z.snd, c z.fst + d z.snd) := (rfl)

/-- A diagonal block operator is the orthogonal sum of its two diagonal maps. -/
private theorem l2Block_diagonal (a : E →L[𝕜] G) (d : F →L[𝕜] H) :
    l2Block a (0 : F →L[𝕜] G) (0 : E →L[𝕜] H) d = a.withLpProdMap 2 d := by
  ext z
  rw [l2Block_apply, ContinuousLinearMap.withLpProdMap_apply]
  simp

end Block

section BlockComp

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v} {G : Type w} {H : Type x} {X : Type y}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]

/-- A block operator applied to a column is the column of the two block-row
combinations.  This is the only composition rule the completion needs on the
right. -/
theorem l2Block_comp_l2Column (a : E →L[𝕜] G) (b : F →L[𝕜] G)
    (c : E →L[𝕜] H) (d : F →L[𝕜] H) (p : X →L[𝕜] E) (q : X →L[𝕜] F) :
    l2Block a b c d ∘L l2Column p q
      = l2Column (a ∘L p + b ∘L q) (c ∘L p + d ∘L q) := by
  ext z
  refine l2_ext ?_ ?_ <;> simp

end BlockComp

section BlockCompBlock

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v} {G : Type w} {H : Type x} {X Y : Type y}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]

/-- Block operators compose by the matrix product rule. -/
theorem l2Block_comp (a : E →L[𝕜] G) (b : F →L[𝕜] G)
    (c : E →L[𝕜] H) (d : F →L[𝕜] H)
    (p : X →L[𝕜] E) (q : Y →L[𝕜] E) (r : X →L[𝕜] F) (s : Y →L[𝕜] F) :
    l2Block a b c d ∘L l2Block p q r s
      = l2Block (a ∘L p + b ∘L r) (a ∘L q + b ∘L s)
          (c ∘L p + d ∘L r) (c ∘L q + d ∘L s) := by
  ext z
  refine l2_ext ?_ ?_ <;>
    · simp only [ContinuousLinearMap.comp_apply, l2Block_apply, WithLp.toLp_fst,
        WithLp.toLp_snd, add_apply, map_add]
      abel

end BlockCompBlock

section BlockAdjoint

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v} {G : Type w} {H : Type x}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **The adjoint of a block operator is its conjugate transpose.**

Proved from the defining inner-product characterisation of the adjoint: the
`L²` inner product splits over the two coordinates, and each of the four
resulting scalar terms is moved across by `adjoint_inner_left`. -/
theorem adjoint_l2Block (a : E →L[𝕜] G) (b : F →L[𝕜] G)
    (c : E →L[𝕜] H) (d : F →L[𝕜] H) :
    ContinuousLinearMap.adjoint (l2Block a b c d)
      = l2Block (ContinuousLinearMap.adjoint a) (ContinuousLinearMap.adjoint c)
          (ContinuousLinearMap.adjoint b) (ContinuousLinearMap.adjoint d) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z w
  simp only [l2Block_apply, WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left]
  ring

end BlockAdjoint

/-! ### The self-adjoint contractive completion -/

section Completion

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The normalised self-adjoint Krein/Julia column completion.**

If `A` is self-adjoint and the column `[A; B]` is a contraction in the
operator-inequality sense `A⋆A + B⋆B ≤ 1`, then `[A; B]` is the first block
column of a self-adjoint contraction `K` on the Hilbert `L²` sum `E ⊕₂ F`.

The completion is `K = L J_A L⋆` with `J_A` the Julia operator of `A` and `L`
the block-diagonal damping by the Douglas factor of `B` through the defect
`√(1 - A²)`; all of that is constructed inside the proof, so the caller supplies
nothing beyond `A`, `B` and the Gram inequality.  See the module docstring. -/
theorem exists_selfAdjoint_contraction_extension_of_column_gram_le
    (A : E →L[ℂ] E) (B : E →L[ℂ] F) (hA : IsSelfAdjoint A)
    (hgram : ContinuousLinearMap.adjoint A ∘L A + ContinuousLinearMap.adjoint B ∘L B
      ≤ ContinuousLinearMap.id ℂ E) :
    ∃ K : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F),
      IsSelfAdjoint K ∧ ‖K‖ ≤ 1 ∧ K ∘L l2Inl = l2Column A B := by
  have hAadj : ContinuousLinearMap.adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hA.star_eq
  -- Step 1: the defect `G = 1 - A²` dominates the Gram operator of `B`.
  have hgram' : A * A + ContinuousLinearMap.adjoint B ∘L B ≤ (1 : E →L[ℂ] E) := by
    have h := hgram
    rw [hAadj] at h
    rwa [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
  have hBG : ContinuousLinearMap.adjoint B ∘L B ≤ 1 - A * A := by
    rw [le_sub_iff_add_le]
    calc ContinuousLinearMap.adjoint B ∘L B + A * A
        = A * A + ContinuousLinearMap.adjoint B ∘L B := add_comm _ _
      _ ≤ 1 := hgram'
  have hBnn : (0 : E →L[ℂ] E) ≤ ContinuousLinearMap.adjoint B ∘L B :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr
      (ContinuousLinearMap.isPositive_adjoint_comp_self B)
  have hG : (0 : E →L[ℂ] E) ≤ 1 - A * A := hBnn.trans hBG
  -- Steps 2 and 3: the positive square root of the defect, and its commutation with `A`.
  obtain ⟨D, hDnn, hDsq, hDA⟩ :
      ∃ D : E →L[ℂ] E, 0 ≤ D ∧ D * D = 1 - A * A ∧ Commute D A := by
    refine ⟨CFC.sqrt (1 - A * A), CFC.sqrt_nonneg _, CFC.sqrt_mul_sqrt_self _ hG,
      Commute.cfcₙ_nnreal ?_ _⟩
    change (1 - A * A) * A = A * (1 - A * A)
    rw [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
  have hDself : IsSelfAdjoint D := IsSelfAdjoint.of_nonneg hDnn
  have hDadj : ContinuousLinearMap.adjoint D = D := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hDself.star_eq
  -- Step 4: the Douglas factor of `B` through the defect.
  obtain ⟨Γ, hΓnorm, hΓD⟩ : ∃ W : E →L[ℂ] F, ‖W‖ ≤ 1 ∧ W ∘L D = B := by
    refine ContinuousLinearMap.exists_contraction_of_gram_le ?_
    rw [hDadj]
    rw [← ContinuousLinearMap.mul_def, hDsq]
    exact hBG
  -- Steps 5 to 8: the Julia operator of `A`.
  set J : WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × E) := l2Block A D D (-A) with hJdef
  have hJadj : ContinuousLinearMap.adjoint J = J := by
    rw [hJdef, adjoint_l2Block, map_neg, hAadj, hDadj]
  have hJself : IsSelfAdjoint J := by
    change star J = J
    rw [ContinuousLinearMap.star_eq_adjoint]; exact hJadj
  have hJinvol : J ∘L J = ContinuousLinearMap.id ℂ (WithLp 2 (E × E)) := by
    have e₁ : A ∘L A + D ∘L D = ContinuousLinearMap.id ℂ E := by
      simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.one_def, hDsq]
      abel
    have e₂ : A ∘L D + D ∘L (-A) = 0 := by
      simp only [← ContinuousLinearMap.mul_def, mul_neg, hDA.eq]
      abel
    have e₃ : D ∘L A + (-A) ∘L D = 0 := by
      simp only [← ContinuousLinearMap.mul_def, neg_mul, hDA.eq]
      abel
    have e₄ : D ∘L D + (-A) ∘L (-A) = ContinuousLinearMap.id ℂ E := by
      simp only [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.one_def, neg_mul_neg, hDsq]
      abel
    rw [hJdef, l2Block_comp, e₁, e₂, e₃, e₄, l2Block_diagonal,
      ContinuousLinearMap.withLpProdMap_id]
  have hJnorm : ‖J‖ ≤ 1 := by
    have h := ContinuousLinearMap.norm_adjoint_comp_self J
    rw [hJadj, hJinvol] at h
    have hid : ‖ContinuousLinearMap.id ℂ (WithLp 2 (E × E))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    nlinarith [norm_nonneg J]
  -- Step 9: the block-diagonal damping.
  set L : WithLp 2 (E × E) →L[ℂ] WithLp 2 (E × F) :=
    (ContinuousLinearMap.id ℂ E).withLpProdMap 2 Γ with hLdef
  have hLnorm : ‖L‖ ≤ 1 := by
    rw [hLdef, ContinuousLinearMap.norm_withLpProdMap]
    exact max_le ContinuousLinearMap.norm_id_le hΓnorm
  have hLadjnorm : ‖ContinuousLinearMap.adjoint L‖ ≤ 1 :=
    (LinearIsometryEquiv.norm_map _ _).trans_le hLnorm
  -- Steps 10 to 13: the completion `K = L J L⋆`.
  refine ⟨L ∘L J ∘L ContinuousLinearMap.adjoint L, ?_, ?_, ?_⟩
  · exact hJself.conj_adjoint L
  · have h₁ : ‖J ∘L ContinuousLinearMap.adjoint L‖ ≤ 1 := by
      calc ‖J ∘L ContinuousLinearMap.adjoint L‖
          ≤ ‖J‖ * ‖ContinuousLinearMap.adjoint L‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * 1 := mul_le_mul hJnorm hLadjnorm (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    calc ‖L ∘L J ∘L ContinuousLinearMap.adjoint L‖
        ≤ ‖L‖ * ‖J ∘L ContinuousLinearMap.adjoint L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hLnorm h₁ (ContinuousLinearMap.opNorm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have hLI : ContinuousLinearMap.adjoint L ∘L (l2Inl : E →L[ℂ] WithLp 2 (E × F))
        = (l2Inl : E →L[ℂ] WithLp 2 (E × E)) := by
      ext x
      apply ext_inner_right ℂ
      intro y
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
      simp [l2Inl_apply, hLdef, ContinuousLinearMap.withLpProdMap_apply, WithLp.prod_inner_apply]
    have hJI : J ∘L (l2Inl : E →L[ℂ] WithLp 2 (E × E)) = l2Column A D := by
      rw [hJdef, l2Inl_eq_l2Column, l2Block_comp_l2Column]
      simp
    have hLC : L ∘L l2Column A D = l2Column A B := by
      ext x
      simp [hLdef, ContinuousLinearMap.withLpProdMap_apply, ← hΓD]
    calc (L ∘L J ∘L ContinuousLinearMap.adjoint L)
          ∘L (l2Inl : E →L[ℂ] WithLp 2 (E × F))
        = L ∘L (J ∘L (ContinuousLinearMap.adjoint L ∘L l2Inl)) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = L ∘L (J ∘L (l2Inl : E →L[ℂ] WithLp 2 (E × E))) := by rw [hLI]
      _ = L ∘L l2Column A D := by rw [hJI]
      _ = l2Column A B := hLC

/-- **The normalised case.**

A column of norm exactly `1` satisfying the Gram contraction inequality
completes to a self-adjoint operator of norm exactly `1`.  No new analysis: the
completion restricts to the column along the isometric inclusion `l2Inl`, so its
norm is at least `1`, and the contraction bound supplies the other half.

This is the form the later normalised Krein reduction consumes. -/
theorem exists_selfAdjoint_norm_one_extension_of_column
    (A : E →L[ℂ] E) (B : E →L[ℂ] F) (hA : IsSelfAdjoint A)
    (hgram : ContinuousLinearMap.adjoint A ∘L A + ContinuousLinearMap.adjoint B ∘L B
      ≤ ContinuousLinearMap.id ℂ E)
    (hcolumn : ‖l2Column A B‖ = 1) :
    ∃ K : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F),
      IsSelfAdjoint K ∧ ‖K‖ = 1 ∧ K ∘L l2Inl = l2Column A B := by
  obtain ⟨K, hKself, hKnorm, hKcol⟩ :=
    exists_selfAdjoint_contraction_extension_of_column_gram_le A B hA hgram
  refine ⟨K, hKself, le_antisymm hKnorm ?_, hKcol⟩
  calc (1 : ℝ) = ‖l2Column A B‖ := hcolumn.symm
    _ = ‖K ∘L (l2Inl : E →L[ℂ] WithLp 2 (E × F))‖ := by rw [hKcol]
    _ ≤ ‖K‖ * ‖(l2Inl : E →L[ℂ] WithLp 2 (E × F))‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖K‖ * 1 := mul_le_mul_of_nonneg_left
      (WithLp.norm_prodContinuousLinearEquiv_symm_comp_inl_le_one 2 ℂ E F) (norm_nonneg _)
    _ = ‖K‖ := mul_one _

/-! ## The ambient form

The normalised column completion above is stated on an `L²` direct sum.  The
form that a perturbation argument actually needs is ambient: a bounded
self-adjoint `T` on a Hilbert space `X` and an orthogonally complemented closed
subspace `P` admit a self-adjoint `T'` agreeing with `T` on `P` whose norm is
exactly the restriction norm `‖T P_P‖`.

The coordinate system is Mathlib's `Submodule.orthogonalDecomposition`,
`X ≃ₗᵢ[𝕜] WithLp 2 (P × Pᗮ)`.  Being a `LinearIsometryEquiv` it transports the
norm and the inner product for free.  The load-bearing scalar identity is
`‖l2Column A B‖ = ‖T P_P‖`, which is proved rather than assumed: the
decomposition is isometric, so the column norm is `‖T ∘L P.subtypeL‖`, and that
equals the ambient restriction norm by two inequalities -- `P.starProjection`
fixes `P`, and it is a contraction.
-/

section Ambient

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [CompleteSpace X]

/-- **The restriction norm does not care whether the source is the subspace or
the projection.**  `‖T ∘ ι_P‖ = ‖T P_P‖`: the projection fixes `P`, giving one
inequality, and it is a contraction, giving the other.

Stated over an arbitrary `RCLike` field, with its own binders: nothing in the
argument sees the scalars. -/
theorem norm_comp_subtypeL_eq_norm_comp_starProjection
    {𝕜 : Type*} [RCLike 𝕜] {Z : Type*} [NormedAddCommGroup Z]
    [InnerProductSpace 𝕜 Z]
    (T : Z →L[𝕜] Z) (P : Submodule 𝕜 Z) [P.HasOrthogonalProjection]
    [CompleteSpace P] :
    ‖T ∘L P.subtypeL‖ = ‖T ∘L P.starProjection‖ := by
  have hsubtype : (T ∘L P.starProjection) ∘L P.subtypeL = T ∘L P.subtypeL := by
    ext u
    exact congrArg (fun x => T x) (P.starProjection_eq_self_iff.mpr u.property)
  have hprojection : (T ∘L P.subtypeL) ∘L P.orthogonalProjectionOnto = T ∘L P.starProjection :=
    ContinuousLinearMap.comp_assoc _ _ _
  refine le_antisymm ?_ ?_
  · rw [← hsubtype]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) P.norm_subtypeL_le)
  · rw [← hprojection]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) P.orthogonalProjectionOnto_norm_le)

/-- **Krein's completion theorem, ambient form.**

A bounded self-adjoint `T` on a complex Hilbert space `X` and an orthogonally
complemented closed subspace `P` admit a self-adjoint `T'` that agrees with `T`
on `P` and whose norm is exactly the norm of the restriction `T P_P`.

The caller supplies `T`, its self-adjointness and `P`: no block matrices, no
Douglas factor `Γ`, no defect operator, no completion certificate, and no
nonvanishing hypothesis.  The zero-restriction case is handled internally by
`T' = 0`.

The proof reads the first block column of `T` in the orthogonal decomposition
`X ≃ₗᵢ[ℂ] WithLp 2 (P × Pᗮ)`, normalises it by the exact restriction norm --
which is why `‖l2Column A B‖ = ‖T P_P‖` has to be *proved* -- feeds the
normalised column to `exists_selfAdjoint_norm_one_extension_of_column`,
rescales, and transports back through the isometric equivalence. -/
theorem exists_selfAdjoint_completion_eq_norm_restriction
    (T : X →L[ℂ] X) (hT : IsSelfAdjoint T) (P : Submodule ℂ X)
    [P.HasOrthogonalProjection] :
    ∃ T' : X →L[ℂ] X, IsSelfAdjoint T' ∧
      T' ∘L P.starProjection = T ∘L P.starProjection ∧
      ‖T'‖ = ‖T ∘L P.starProjection‖ := by
  classical
  let : CompleteSpace P :=
    (P.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  let : CompleteSpace (Pᗮ : Submodule ℂ X) :=
    (Pᗮ.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  set r : ℝ := ‖T ∘L P.starProjection‖ with hrdef
  by_cases hr : r = 0
  · refine ⟨0, IsSelfAdjoint.zero _, ?_, ?_⟩
    · have hz : T ∘L P.starProjection = 0 := by
        rw [← norm_eq_zero, ← hrdef]; exact hr
      rw [hz, ContinuousLinearMap.zero_comp]
    · rw [norm_zero]; exact hr.symm
  have hrpos : 0 < r := lt_of_le_of_ne
    (by rw [hrdef]; exact ContinuousLinearMap.opNorm_nonneg _) (Ne.symm hr)
  have hrealsa : ∀ t : ℝ, IsSelfAdjoint ((t : ℂ)) := fun t => Complex.conj_ofReal t
  -- normalise the operator, not the column: the ambient endomorphism algebra is
  -- where scalar norms are available
  set T₀ : X →L[ℂ] X := ((r⁻¹ : ℝ) : ℂ) • T with hT₀def
  have hT₀sa : IsSelfAdjoint T₀ := by
    rw [hT₀def]; exact IsSelfAdjoint.smul (hrealsa _) hT
  have hT₀res : T₀ ∘L P.starProjection = ((r⁻¹ : ℝ) : ℂ) • (T ∘L P.starProjection) := by
    rw [hT₀def, ContinuousLinearMap.smul_comp]
  -- the first block column of the normalised operator
  set U : X ≃ₗᵢ[ℂ] WithLp 2 (P × Pᗮ) := P.orthogonalDecomposition with hUdef
  set Acol : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L T₀ ∘L P.subtypeL with hAdef
  set Bcol : (P : Submodule ℂ X) →L[ℂ] (Pᗮ : Submodule ℂ X) :=
    Pᗮ.orthogonalProjectionOnto ∘L T₀ ∘L P.subtypeL with hBdef
  have hAsa : IsSelfAdjoint Acol := by
    rw [hAdef, ← Submodule.adjoint_subtypeL]
    exact hT₀sa.adjoint_conj P.subtypeL
  set C : P →L[ℂ] WithLp 2 (P × Pᗮ) := l2Column Acol Bcol with hCdef
  have hCeq : C = (U : X →L[ℂ] WithLp 2 (P × Pᗮ)) ∘L T₀ ∘L P.subtypeL := by
    rw [hCdef, hUdef]
    ext u
    change l2Column Acol Bcol u = P.orthogonalDecomposition (T₀ (u : X))
    rw [l2Column_apply, Submodule.orthogonalDecomposition_apply]
    rfl
  have hCnorm : ‖C‖ = 1 := by
    rw [hCeq, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
      norm_comp_subtypeL_eq_norm_comp_starProjection, hT₀res, norm_smul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ r⁻¹), ← hrdef,
      inv_mul_cancel₀ hr]
  -- the normalised Krein completion, in coordinates
  obtain ⟨K0, hK0sa, hK0norm, hK0col⟩ :=
    exists_selfAdjoint_norm_one_extension_of_column Acol Bcol hAsa
      (l2Column_gram_le_id_of_norm_le_one Acol Bcol (le_of_eq hCnorm))
      hCnorm
  -- transport back to `X`
  set T₁ : X →L[ℂ] X := (U.symm : WithLp 2 (P × Pᗮ) →L[ℂ] X) ∘L K0 ∘L
    (U : X →L[ℂ] WithLp 2 (P × Pᗮ)) with hT₁def
  have hT₁sa : IsSelfAdjoint T₁ := by
    rw [hT₁def, ← U.adjoint_eq_symm]
    exact hK0sa.adjoint_conj (U : X →L[ℂ] WithLp 2 (P × Pᗮ))
  have hT₁norm : ‖T₁‖ = 1 := by
    rw [hT₁def, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
      ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, hK0norm]
  have hT₁res : T₁ ∘L P.starProjection = T₀ ∘L P.starProjection := by
    ext x
    change U.symm (K0 (U (P.starProjection x))) = T₀ (P.starProjection x)
    set px : X := P.starProjection x with hpxdef
    have hpx : px ∈ P := P.starProjection_apply_mem x
    set u : P := ⟨px, hpx⟩ with hudef
    have h1 : P.orthogonalProjectionOnto px = u := by
      apply Subtype.ext
      change P.starProjection px = px
      exact Submodule.starProjection_eq_self_iff.mpr hpx
    have h2 : Pᗮ.orthogonalProjectionOnto px = 0 := by
      apply Subtype.ext
      change Pᗮ.starProjection px = (0 : X)
      rw [Submodule.starProjection_orthogonal_val,
        Submodule.starProjection_eq_self_iff.mpr hpx, sub_self]
    have hUpx : U px = l2Inl (𝕜 := ℂ) (F := ((Pᗮ : Submodule ℂ X) : Type u)) u := by
      rw [hUdef, Submodule.orthogonalDecomposition_apply, h1, h2, l2Inl_apply]
    have hKu : K0 (l2Inl (𝕜 := ℂ) (F := ((Pᗮ : Submodule ℂ X) : Type u)) u) = C u :=
      congrArg (fun M : P →L[ℂ] WithLp 2 (P × Pᗮ) => M u) hK0col
    rw [hUpx, hKu, hCeq]
    change U.symm ((U : X →L[ℂ] WithLp 2 (P × Pᗮ)) (T₀ (u : X))) = T₀ px
    rw [hUdef]
    exact P.orthogonalDecomposition.symm_apply_apply _
  -- scale back
  refine ⟨((r : ℝ) : ℂ) • T₁, IsSelfAdjoint.smul (hrealsa _) hT₁sa, ?_, ?_⟩
  · rw [ContinuousLinearMap.smul_comp, hT₁res, hT₀res, smul_smul,
      show (((r : ℝ) : ℂ) * ((r⁻¹ : ℝ) : ℂ)) = 1 by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ hr, Complex.ofReal_one],
      one_smul]
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hrpos.le, hT₁norm, mul_one]

/-- **The pointwise form on `P`.**  A thin consequence of the capstone: the
completion agrees with `T` at every vector of `P`. -/
theorem exists_selfAdjoint_completion_eqOn_of_norm_restriction
    (T : X →L[ℂ] X) (hT : IsSelfAdjoint T) (P : Submodule ℂ X)
    [P.HasOrthogonalProjection] :
    ∃ T' : X →L[ℂ] X, IsSelfAdjoint T' ∧ (∀ x ∈ P, T' x = T x) ∧
      ‖T'‖ = ‖T ∘L P.starProjection‖ := by
  obtain ⟨T', hsa, hcol, hnorm⟩ :=
    exists_selfAdjoint_completion_eq_norm_restriction T hT P
  refine ⟨T', hsa, fun x hx => ?_, hnorm⟩
  have hfix : P.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
  have h := congrArg (fun M : X →L[ℂ] X => M x) hcol
  change T' x = T x
  simpa only [ContinuousLinearMap.comp_apply, hfix] using h

end Ambient

end Completion

end TauCeti

end
