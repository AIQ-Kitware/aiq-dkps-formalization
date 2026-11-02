/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T06.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`AlignedBasis.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

Groundwork for the Yu–Wang–Samworth aligned-basis (orthogonal-Procrustes) bound:
selected-unitary alignment identities on TauCeti's accepted coordinate
synthesis isometry and overlap operator.
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
public import ForTauCeti.Analysis.InnerProductSpace.Gram.Matrix
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Overlap


/-! # Selected-unitary orthonormal alignment

An orthonormal family `v : Fin d → E` gives a linear isometry
`hv.synthesisMapIsometry : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E`, `eⱼ ↦ vⱼ`, onto the
span of the family.  Its adjoint recovers the coordinates `y ↦ (⟪vⱼ, y⟫)ⱼ`, so
the composite `(hu.synthesisMapIsometry)⋆ ∘ (hv.synthesisMapIsometry)` is the overlap operator
with matrix `⟪uᵢ, vⱼ⟫` — the object whose singular values are the cosines of the
principal angles between `span u` and `span v`.

## Main results

* `Orthonormal.synthesisMapIsometry`: the accepted coordinate isometry.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.AlignedBasis`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `75fdc44`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none**. Coordinate synthesis and overlap come from TauCeti.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {d : ℕ}

/-- **An orthonormal family of the right size, lying in `V`, spans `V`.**

Containment gives one inequality and `finrank_span_eq_card` gives equality of
dimensions, which is all `Submodule.eq_of_le_of_finrank_eq` needs.  Written out
four times across `AngleGeometry` and the YWS application statistics layer, once per
subspace in each. -/
theorem span_range_eq_of_orthonormal_of_mem {V : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 V] {v : Fin d → E} (hv : Orthonormal 𝕜 v)
    (hmem : ∀ i, v i ∈ V) (hd : d = finrank 𝕜 V) :
    Submodule.span 𝕜 (Set.range v) = V := by
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact hmem i
  · rw [finrank_span_eq_card hv.linearIndependent, Fintype.card_fin, hd]

/-- The squared overlaps are bounded by the sum of principal cosines. -/
theorem sum_overlap_le_sum_singularValues {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2 ≤
      ∑ k : Fin d, (overlapOperator 𝕜 u v).singularValues (k : ℕ) := by
  have hsq := sum_range_sq_cosPrincipalAngles hu hv
  rw [Fintype.card_fin, ← Fin.sum_univ_eq_sum_range] at hsq
  rw [← hsq]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← cosPrincipalAngles_def hu hv]
  rw [sq]
  exact mul_le_of_le_one_left (cosPrincipalAngles_nonneg hu hv i)
    (cosPrincipalAngles_le_one hu hv i)

/-- **Cross-term identity** (Procrustes/polar).  With `O = choosePolarUnitary
(overlapOperator 𝕜 u v)`, the aligned rotation `wⱼ = (hv.synthesisMapIsometry)(O⁻¹ eⱼ)`
satisfies `⟪uⱼ, wⱼ⟫ = ⟪O⁻¹ eⱼ, |M|(O⁻¹ eⱼ)⟫`, where `M = overlapOperator 𝕜 u v`.
Moves `hu.synthesisMapIsometry` to its adjoint (giving `M`), then `M = O|M|` with `O`
unitary. -/
theorem inner_u_aligned_eq {u v : Fin d → E} (_hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (j : Fin d) :
    ⟪u j, hv.synthesisMapIsometry ((choosePolarUnitary (overlapOperator 𝕜 u v)).symm
          (EuclideanSpace.single j 1))⟫_𝕜
      = ⟪(choosePolarUnitary (overlapOperator 𝕜 u v)).symm (EuclideanSpace.single j 1),
          LinearMap.operatorAbs (overlapOperator 𝕜 u v)
            ((choosePolarUnitary (overlapOperator 𝕜 u v)).symm (EuclideanSpace.single j 1))⟫_𝕜 := by
  set M := overlapOperator 𝕜 u v with hM
  set O := choosePolarUnitary M with hO
  have hstep : ⟪u j, hv.synthesisMapIsometry (O.symm (EuclideanSpace.single j 1))⟫_𝕜
      = ⟪EuclideanSpace.single j 1, M (O.symm (EuclideanSpace.single j 1))⟫_𝕜 := by
    rw [hM, overlapOperator_def, LinearMap.comp_apply, EuclideanSpace.inner_single_left,
      map_one, one_mul, analysisMap_apply, Orthonormal.synthesisMapIsometry_apply,
      synthesisMap_apply]
  rw [hstep]
  -- `M = O ∘ |M|`, then `O` unitary moves across the inner product.
  have hpolar : M (O.symm (EuclideanSpace.single j 1))
      = O (M.operatorAbs (O.symm (EuclideanSpace.single j 1))) := by
    have h1 := LinearMap.congr_fun (polar_decomposition_choosePolarUnitary M)
      (O.symm (EuclideanSpace.single j 1))
    rw [LinearMap.comp_apply] at h1
    rw [h1, hO]
    rfl
  rw [hpolar, ← O.apply_symm_apply (EuclideanSpace.single j 1)]
  rw [O.inner_map_map, O.symm_apply_apply]

/-- **Cross-term sum = `∑ cos θ`.** Summing the Procrustes cross-term recovers the
trace of the modulus, `∑ⱼ re⟪uⱼ, wⱼ⟫ = ∑ⱼ σⱼ`, via `W0.1(c)` on the
`O⁻¹`-image orthonormal basis. -/
theorem sum_re_inner_u_aligned {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ∑ j, RCLike.re ⟪u j, hv.synthesisMapIsometry ((choosePolarUnitary (overlapOperator 𝕜 u v)).symm
          (EuclideanSpace.single j 1))⟫_𝕜
      = ∑ k : Fin d, (overlapOperator 𝕜 u v).singularValues (k : ℕ) := by
  rw [← sum_re_inner_abs_self_eq_sum_singularValues (overlapOperator 𝕜 u v)
    finrank_euclideanSpace_fin
    ((EuclideanSpace.basisFun (Fin d) 𝕜).map
      (choosePolarUnitary (overlapOperator 𝕜 u v)).symm)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_u_aligned_eq hu hv j, OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply,
    (LinearMap.isPositive_operatorAbs (overlapOperator 𝕜 u v)).isSymmetric
      ((choosePolarUnitary (overlapOperator 𝕜 u v)).symm (EuclideanSpace.single j 1))
      ((choosePolarUnitary (overlapOperator 𝕜 u v)).symm (EuclideanSpace.single j 1))]

/-- **Yu–Wang–Samworth aligned-basis bound.** For orthonormal families `u, v`
(bases of the two `d`-subspaces), the Procrustes-rotated basis
`wⱼ = (hv.synthesisMapIsometry)(O⁻¹ eⱼ)` (`O = choosePolarUnitary (overlapOperator 𝕜 u v)`) obeys
`∑ⱼ ‖wⱼ − uⱼ‖² ≤ 2 (d − ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²) = 2 ‖sinΘ‖²_F`.  From
`∑‖wⱼ−uⱼ‖² = 2d − 2∑ cos θ` and the analytic core `overlap ≤ ∑ cos θ`. -/
theorem sum_sq_norm_aligned_le {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ∑ j, ‖hv.synthesisMapIsometry ((choosePolarUnitary (overlapOperator 𝕜 u v)).symm
          (EuclideanSpace.single j 1)) - u j‖ ^ 2
      ≤ 2 * ((d : ℝ) - ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2) := by
  have hexp : ∀ j, ‖hv.synthesisMapIsometry ((choosePolarUnitary (overlapOperator 𝕜 u v)).symm
        (EuclideanSpace.single j 1)) - u j‖ ^ 2
      = 2 - 2 * RCLike.re ⟪u j, hv.synthesisMapIsometry
          ((choosePolarUnitary (overlapOperator 𝕜 u v)).symm (EuclideanSpace.single j 1))⟫_𝕜 := by
    intro j
    simp only [norm_sub_sq (𝕜 := 𝕜), (hv.synthesisMapIsometry).norm_map,
      (choosePolarUnitary (overlapOperator 𝕜 u v)).symm.norm_map, PiLp.norm_single 2, norm_one,
      hu.1 j, inner_re_symm]
    ring
  rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_re_inner_u_aligned hu hv]
  simp
  have hkey := sum_overlap_le_sum_singularValues hu hv
  linarith

end TauCeti
