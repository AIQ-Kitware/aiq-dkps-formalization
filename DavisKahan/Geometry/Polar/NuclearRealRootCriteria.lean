/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.NuclearRootSpectralFactors
public import ForTauCeti.Analysis.InnerProductSpace.RealSpectralSignExistence

/-!
# Real signed-root feasibility on compact Hilbert pairs

For compact projection difference and balanced crossed defects, a real
signed root exists if and only if every strictly acute positive sine
eigenspace has real dimension divisible by four. Its full dimension is
twice the source-side multiplicity, so the criterion is even source
multiplicity. Right-angle factors always exist; the zero sector has no
free root factor. The resulting actual orthogonal transporter attains
the projection nuclear lower bound, with finite cost in the trace-class
case.

The block construction uses classical orthogonal complex structures;
the application joins the local finite real matching parity with the
compact signed-root product. An equivalent predecessor for this exact
transport criterion has not been located in the sources examined; its
historical priority remains unresolved. See provenance row T8 in
`dev/spectral-transport-unification.md`. Necessity of this certificate
for every real lower-bound attainer is not proved here, nor is a
classification of real minimizers whose value exceeds that bound.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private theorem nuclear_sine_compact_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection)) :
    IsCompactOperator (K.sinAngleOperator L) := by
  apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
  have hsv : (K.sinAngleOperator L).singularValue =
      (K.starProjection - L.starProjection).singularValue := by
    funext n
    rw [K.sinAngleOperator_def L, ContinuousLinearMap.singularValue_modulus]
  rw [hsv]
  exact hcompact.tendsto_singularValue

private theorem nuclear_spectral_block_relations_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (s : ℝ) (hs : s ≠ 0)
    (hcomplete : CompleteSpace (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s)) :
    let S := K.sinAngleOperator L
    let V : E →L[ℝ] E := nuclearTransportDual K L D
    let C := Proposition35.section3CosAngleOperator K L
    let G := V * C
    let J : E →L[ℝ] E := K.reflection
    let hV := Proposition35.commute_sinAngleOperator_of_commute_section3CosAngleOperator
      K L V (nuclearTransportDual_comm_cosine K L D)
    let v := V.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S V hV s)
    let g := G.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S G
      (nuclear_spectral_symmetries_comm_sine K L D).1 s)
    let j := J.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J
      (nuclear_spectral_symmetries_comm_sine K L D).2 s)
    star v = -v ∧ v * v = -1 ∧ star g = -g ∧ IsSelfAdjoint j ∧ j * j = 1 ∧
      j * v + v * j = 0 ∧ j * g + g * j = 0 := by
  let := hcomplete
  dsimp only
  let S := K.sinAngleOperator L
  let V : E →L[ℝ] E := nuclearTransportDual K L D
  let C := Proposition35.section3CosAngleOperator K L
  let G := V * C
  let J : E →L[ℝ] E := K.reflection
  let B := nonacuteDirectRotation K L D - C
  let Q := B.ker.starProjection
  let N := Module.End.eigenspace S.toLinearMap s
  have hVS : Commute V S :=
    Proposition35.commute_sinAngleOperator_of_commute_section3CosAngleOperator
      K L V (nuclearTransportDual_comm_cosine K L D)
  have hGS := (nuclear_spectral_symmetries_comm_sine K L D).1
  have hJS := (nuclear_spectral_symmetries_comm_sine K L D).2
  let v := V.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S V hVS s)
  let g := G.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S G hGS s)
  let j := J.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J hJS s)
  change star v = -v ∧ v * v = -1 ∧ star g = -g ∧ IsSelfAdjoint j ∧ j * j = 1 ∧
    j * v + v * j = 0 ∧ j * g + g * j = 0
  have hSQ : S * Q = 0 := by
    ext x
    change S (Q x) = 0
    apply norm_eq_zero.mp
    rw [← show B.modulus = S from
      (Proposition35.modulus_nonacuteDirectRotation_sub_cosine K L D).trans
        (by rw [Proposition35.section3SinAngleOperator]; exact (K.sinAngleOperator_def L).symm),
      B.norm_modulus_apply]
    have hz : B (Q x) = 0 := B.ker.starProjection_apply_mem x
    rw [hz, norm_zero]
  have hQS : Q * S = 0 := by
    have h := congrArg star hSQ
    have hSs : star S = S := (K.isPositive_sinAngleOperator L).isSelfAdjoint.star_eq
    have hQs : star Q = Q := (isSelfAdjoint_starProjection B.ker).star_eq
    simpa only [star_mul, hSs, hQs, star_zero] using h
  have hQzero (x : N) : Q x = 0 := by
    have h := congrArg (fun T : E →L[ℝ] E => T x) hQS
    change Q (S x) = 0 at h
    have hx : S (x : E) = s • (x : E) := Module.End.mem_eigenspace_iff.mp x.property
    rw [hx, map_smul] at h
    exact (smul_eq_zero.mp h).resolve_left hs
  have hVstar (x : N) : star V x = -V x := by
    have h := congrArg (fun T : E →L[ℝ] E => T x) (nuclearTransportDual_add_star K L D)
    change V x + star V x = Q x + Q x at h
    rw [hQzero, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  have hVC := (nuclearTransportDual_comm_cosine K L D).eq
  have hJC := (Proposition35.commute_section3CosAngleOperator_of_commute_sinAngleOperator
    K L J hJS).eq
  have hGstar (x : N) : star G x = -G x := by
    have hCs := ((ContinuousLinearMap.nonneg_iff_isPositive).mp
      (Proposition35.section3CosAngleOperator_nonneg K L)).isSelfAdjoint.star_eq
    change (star (V * C)) x = -G x
    rw [star_mul, hCs]
    change C (star V x) = -V (C x)
    rw [hVstar, map_neg]
    exact congrArg Neg.neg (congrArg (fun T : E →L[ℝ] E => T x) hVC.symm)
  have hVodd (x : N) : J (V x) = -V (J x) := by
    have h := congrArg (fun T : E →L[ℝ] E => T (J x))
      (reflection_conj_nuclearTransportDual K L D)
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] at h
    change J (V (K.reflection.symm (J x))) = -V (J x) + Q (J x) + Q (J x) at h
    have hJJ (y : E) : K.reflection.symm (J y) = y := K.reflection.symm_apply_apply y
    rw [hJJ, show Q (J x) = 0 from hQzero (j x), add_zero, add_zero] at h
    exact h
  have hvs : star v = -v := by
    apply Eq.symm
    apply (ContinuousLinearMap.eq_adjoint_iff (-v) v).mpr
    intro x y
    change ⟪-V x, (y : E)⟫_ℝ = ⟪(x : E), V y⟫_ℝ
    rw [← hVstar]
    exact V.adjoint_inner_left (y : E) (x : E)
  have hvunit (x : E) : star V (V x) = x :=
    congrArg (fun T : E →L[ℝ] E => T x)
      (Unitary.star_mul_self_of_mem (Unitary.linearIsometryEquiv.symm (nuclearTransportDual K L D)).property)
  refine ⟨hvs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    have h := hvunit (x : E)
    rw [show star V (V x) = -V (V x) from hVstar (v x)] at h
    change V (V (x : E)) = -(x : E)
    exact neg_eq_iff_eq_neg.mp h
  · apply Eq.symm
    apply (ContinuousLinearMap.eq_adjoint_iff (-g) g).mpr
    intro x y
    change ⟪-G x, (y : E)⟫_ℝ = ⟪(x : E), G y⟫_ℝ
    rw [← hGstar]
    exact G.adjoint_inner_left (y : E) (x : E)
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    have hJsa : IsSelfAdjoint J := by
      change (K.reflection : E →L[ℝ] E).adjoint = _
      rw [K.reflection.adjoint_eq_symm, K.reflection_symm]
    exact hJsa.isSymmetric.restrict_invariant
      (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J hJS s)
  · ext x
    exact K.reflection_reflection (x : E)
  · ext x
    change J (V (x : E)) + V (J x) = 0
    rw [hVodd, neg_add_cancel]
  · ext x
    change J (V (C (x : E))) + V (C (J x)) = 0
    have hCS : Commute C S :=
      Proposition35.commute_sinAngleOperator_of_commute_section3CosAngleOperator K L C (Commute.refl C)
    let cx : N := ⟨C x, ContinuousLinearMap.mapsTo_eigenspace_of_commute S C hCS s x x.property⟩
    rw [show J (V (C (x : E))) = -V (J (C x)) from hVodd cx,
      show J (C (x : E)) = C (J x) from congrArg (fun T : E →L[ℝ] E => T x) hJC,
      neg_add_cancel]

/-- The full sine eigenspace consists of two equal-dimensional principal
sides. Thus its fourfold real parity is exactly even multiplicity on
the source side. This includes the balanced right-angle block. -/
theorem finrank_sine_eigenspace_eq_two_mul_source_side_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection))
    (s : ℝ) (hs : s ≠ 0) :
    let N := Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s
    Module.finrank ℝ N = 2 * Module.finrank ℝ (K.comap N.subtype) := by
  let S := K.sinAngleOperator L
  let V : E →L[ℝ] E := nuclearTransportDual K L D
  let J : E →L[ℝ] E := K.reflection
  let N := Module.End.eigenspace S.toLinearMap s
  let : FiniteDimensional ℝ N := ContinuousLinearMap.finite_dimensional_eigenspace
    (nuclear_sine_compact_real K L hcompact) s hs
  let : CompleteSpace N := FiniteDimensional.complete ℝ N
  have hVS := Proposition35.commute_sinAngleOperator_of_commute_section3CosAngleOperator
    K L V (nuclearTransportDual_comm_cosine K L D)
  let v := V.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S V hVS s)
  let j := J.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J
    (nuclear_spectral_symmetries_comm_sine K L D).2 s)
  obtain ⟨_, hvsq, _, _, hjsq, hjv, _⟩ :=
    nuclear_spectral_block_relations_real K L D s hs inferInstance
  have hdim := finrank_eq_two_mul_positive_eigenspace_real v j hvsq hjsq hjv
  have hside : Module.End.eigenspace j.toLinearMap 1 = K.comap N.subtype := by
    ext x
    rw [Module.End.mem_eigenspace_iff]
    change j x = (1 : ℝ) • x ↔ (x : E) ∈ K
    rw [one_smul]
    constructor
    · intro h
      exact (K.reflection_eq_self_iff (x : E)).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((K.reflection_eq_self_iff (x : E)).mpr h)
  rw [hside] at hdim
  exact hdim

/-- **Infinite-rank real spectral obstruction.** Every nonzero strictly
acute sine eigenspace must have real dimension divisible by four if a
real signed root exists. Compactness makes each such eigenspace finite;
the ambient pair may have infinite rank and arbitrary fixed directions. -/
theorem nuclearSignedSineParameters_four_dvd_sine_eigenspace_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection))
    (hroot : (nuclearSignedSineParameters K L D).Nonempty)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    4 ∣ Module.finrank ℝ (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s) := by
  let S := K.sinAngleOperator L
  let G := (nuclearTransportDual K L D : E →L[ℝ] E) *
    Proposition35.section3CosAngleOperator K L
  let J : E →L[ℝ] E := K.reflection
  let N := Module.End.eigenspace S.toLinearMap s
  have hSc : IsCompactOperator S := by
    apply ContinuousLinearMap.isCompactOperator_iff_tendsto_singularValue.mpr
    have hsv : S.singularValue = (K.starProjection - L.starProjection).singularValue := by
      funext n
      rw [show S = (K.starProjection - L.starProjection).modulus from K.sinAngleOperator_def L,
        ContinuousLinearMap.singularValue_modulus]
    rw [hsv]
    exact hcompact.tendsto_singularValue
  let : FiniteDimensional ℝ N :=
    ContinuousLinearMap.finite_dimensional_eigenspace hSc s hs0.ne'
  let g : N →L[ℝ] N := G.restrict
    (ContinuousLinearMap.mapsTo_eigenspace_of_commute S G
      (nuclear_spectral_symmetries_comm_sine K L D).1 s)
  let j : N →L[ℝ] N := J.restrict
    (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J
      (nuclear_spectral_symmetries_comm_sine K L D).2 s)
  obtain ⟨P, hP⟩ :=
    (nuclearSignedSineParameters_nonempty_iff_spectral_factors K L D hcompact).mp hroot ⟨s, hs0.ne'⟩
  change IsStarProjection P ∧ Commute P g ∧ P * j + j * P = j at hP
  let c := Real.sqrt (1 - s * s)
  have hsmall : 0 < 1 - s * s := by nlinarith
  have hc : c ≠ 0 := (Real.sqrt_pos.mpr hsmall).ne'
  have hcsq : c * c = 1 - s * s := Real.mul_self_sqrt hsmall.le
  have hgsq : g * g = -(c * c) • 1 := by
    ext x
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    change S (x : E) = s • (x : E) at hx
    have h := nuclear_spectral_phase_square K L D s hs0.ne' (x : E) hx
    change G (G (x : E)) = (s * s - 1) • (x : E) at h
    change G (G (x : E)) = -(c * c) • (x : E)
    rw [h, hcsq]
    module
  have hjsq : j * j = 1 := by
    ext x
    exact K.reflection_reflection (x : E)
  exact four_dvd_finrank_of_spectral_sign_projection_real g j P c hc hgsq hjsq
    hP.1 hP.2.1 hP.2.2

/-- A single compact strictly acute sine block of dimension not divisible
by four rules out every real signed root, regardless of the other blocks. -/
theorem not_nonempty_nuclearSignedSineParameters_of_sine_dimension_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection))
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hdim : ¬4 ∣ Module.finrank ℝ
      (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s)) :
    ¬(nuclearSignedSineParameters K L D).Nonempty := by
  intro hroot
  exact hdim (nuclearSignedSineParameters_four_dvd_sine_eigenspace_real
    K L D hcompact hroot s hs0 hs1)

/-- On each strictly acute sine eigenspace, the local real signed-root
factor is nonempty exactly in dimensions divisible by four. -/
theorem nuclearSignedSineSpectralFactors_nonempty_iff_four_dvd_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection))
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    (nuclearSignedSineSpectralFactors K L D ⟨s, hs0.ne'⟩).Nonempty ↔
      4 ∣ Module.finrank ℝ (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s) := by
  let S := K.sinAngleOperator L
  let G := (nuclearTransportDual K L D : E →L[ℝ] E) *
    Proposition35.section3CosAngleOperator K L
  let J : E →L[ℝ] E := K.reflection
  let N := Module.End.eigenspace S.toLinearMap s
  have hSc : IsCompactOperator S := nuclear_sine_compact_real K L hcompact
  let : FiniteDimensional ℝ N := ContinuousLinearMap.finite_dimensional_eigenspace hSc s hs0.ne'
  let g := G.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S G
    (nuclear_spectral_symmetries_comm_sine K L D).1 s)
  let j := J.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J
    (nuclear_spectral_symmetries_comm_sine K L D).2 s)
  obtain ⟨_, _, hgs, hjs, hjsq, _, hjg⟩ :=
    nuclear_spectral_block_relations_real K L D s hs0.ne' inferInstance
  let c := Real.sqrt (1 - s * s)
  have hcpos : 0 < 1 - s * s := by nlinarith
  have hcsq : c * c = 1 - s * s := Real.mul_self_sqrt hcpos.le
  have hgsq : g * g = -(c * c) • 1 := by
    ext x
    have hx : S (x : E) = s • (x : E) := Module.End.mem_eigenspace_iff.mp x.property
    have h := nuclear_spectral_phase_square K L D s hs0.ne' (x : E) hx
    change G (G (x : E)) = (s * s - 1) • (x : E) at h
    change G (G (x : E)) = -(c * c) • (x : E)
    rw [h, hcsq]
    module
  exact exists_spectral_sign_projection_iff_four_dvd_finrank_real g j c
    (Real.sqrt_pos.mpr hcpos).ne' hgs hgsq hjs hjsq hjg

/-- Right-angle sine blocks always admit a real signed-root factor.
The balanced crossed-defect equivalence supplies the quarter-turn; no
fourfold multiplicity condition is imposed. -/
theorem nuclearSignedSineSpectralFactors_nonempty_one_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection)) :
    (nuclearSignedSineSpectralFactors K L D ⟨1, one_ne_zero⟩).Nonempty := by
  let S := K.sinAngleOperator L
  let V : E →L[ℝ] E := nuclearTransportDual K L D
  let C := Proposition35.section3CosAngleOperator K L
  let G := V * C
  let J : E →L[ℝ] E := K.reflection
  let N := Module.End.eigenspace S.toLinearMap 1
  have hSc : IsCompactOperator S := nuclear_sine_compact_real K L hcompact
  let : FiniteDimensional ℝ N := ContinuousLinearMap.finite_dimensional_eigenspace hSc 1 one_ne_zero
  let : CompleteSpace N := FiniteDimensional.complete ℝ N
  have hVS := Proposition35.commute_sinAngleOperator_of_commute_section3CosAngleOperator
    K L V (nuclearTransportDual_comm_cosine K L D)
  let v := V.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S V hVS 1)
  let g := G.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S G
    (nuclear_spectral_symmetries_comm_sine K L D).1 1)
  let j := J.restrict (ContinuousLinearMap.mapsTo_eigenspace_of_commute S J
    (nuclear_spectral_symmetries_comm_sine K L D).2 1)
  obtain ⟨hvs, hvsq, hgs, hjs, hjsq, hjv, _⟩ :=
    nuclear_spectral_block_relations_real K L D 1 one_ne_zero inferInstance
  change star v = -v at hvs
  change v * v = -1 at hvsq
  change star g = -g at hgs
  change IsSelfAdjoint j at hjs
  change j * j = 1 at hjsq
  change j * v + v * j = 0 at hjv
  have hgsq : g * g = 0 := by
    ext x
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    change S (x : E) = (1 : ℝ) • (x : E) at hx
    have h := nuclear_spectral_phase_square K L D 1 one_ne_zero (x : E) hx
    change G (G (x : E)) = (1 * 1 - 1 : ℝ) • (x : E) at h
    change G (G (x : E)) = 0
    simpa only [one_mul, sub_self, zero_smul] using h
  have hg : g = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    have hz : g (g x) = 0 := congrArg (fun T : N →L[ℝ] N => T x) hgsq
    have hstar : g.adjoint (g x) = 0 := by
      change star g (g x) = 0
      rw [hgs]
      change -g (g x) = 0
      rw [hz, neg_zero]
    have h := g.adjoint_inner_left x (g x)
    rw [hstar, inner_zero_left] at h
    exact inner_self_eq_zero.mp h.symm
  let A : N →L[ℝ] N := v * j
  have hAs : star A = A := by
    change star (v * j) = v * j
    calc
      _ = star j * star v := star_mul v j
      _ = -(j * v) := by
        rw [hjs.star_eq, hvs]
        apply ContinuousLinearMap.ext
        intro x
        change j (-(v x)) = -(j (v x))
        rw [map_neg]
      _ = v * j := by
        have h : j * v = -(v * j) := eq_neg_of_add_eq_zero_left hjv
        rw [h, neg_neg]
  have hAsq : A * A = 1 := by
    have h : j * v = -(v * j) := eq_neg_of_add_eq_zero_left hjv
    calc
      _ = v * (j * v) * j := by change (v * j) * (v * j) = _; noncomm_ring
      _ = -(v * v) * (j * j) := by
        rw [h]
        apply ContinuousLinearMap.ext
        intro x
        change v (-(v (j (j x)))) = -(v (v (j (j x))))
        rw [map_neg]
      _ = 1 := by rw [hvsq, hjsq]; simp
  have hAJ : A * j + j * A = 0 := by
    dsimp only [A]
    linear_combination (norm := noncomm_ring) hjv * j
  let P : N →L[ℝ] N := (1 / 2 : ℝ) • (1 + A)
  change ∃ P, IsStarProjection P ∧ Commute P g ∧ P * j + j * P = j
  obtain ⟨hP, hPJ⟩ := half_one_add_projection_of_odd_involution_real A j hAs hAsq hAJ
  refine ⟨P, hP, ?_, hPJ⟩
  rw [hg]
  exact Commute.zero_right P

/-- **Exact real nuclear root existence in arbitrary Hilbert dimension.**
For a compact projection difference and balanced crossed defects, a real
signed root exists iff every strictly acute positive sine eigenspace
has real dimension divisible by four. The kernel has no free factor;
right angles impose no extra parity condition. -/
theorem nuclearSignedSineParameters_nonempty_iff_four_dvd_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection)) :
    (nuclearSignedSineParameters K L D).Nonempty ↔
      ∀ s : ℝ, 0 < s → s < 1 →
        4 ∣ Module.finrank ℝ (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s) := by
  constructor
  · intro h s hs0 hs1
    exact nuclearSignedSineParameters_four_dvd_sine_eigenspace_real K L D hcompact h s hs0 hs1
  · intro hparity
    apply (nuclearSignedSineParameters_nonempty_iff_spectral_factors K L D hcompact).mpr
    intro μ
    let S := K.sinAngleOperator L
    let N := Module.End.eigenspace S.toLinearMap μ.val
    let : FiniteDimensional ℝ N := ContinuousLinearMap.finite_dimensional_eigenspace
      (nuclear_sine_compact_real K L hcompact) μ.val μ.property
    let : CompleteSpace N := FiniteDimensional.complete ℝ N
    by_cases hN : Subsingleton N
    · let := hN
      change ∃ P : N →L[ℝ] N, IsStarProjection P ∧ Commute P _ ∧ _ = _
      refine ⟨0, ⟨?_, ?_⟩, ?_, ?_⟩
      · change (0 : N →L[ℝ] N) * 0 = 0
        rfl
      · change (0 : N →L[ℝ] N).adjoint = 0
        exact map_zero ContinuousLinearMap.adjoint
      · apply ContinuousLinearMap.ext
        intro x
        exact Subsingleton.elim _ _
      · apply ContinuousLinearMap.ext
        intro x
        exact Subsingleton.elim _ _
    · let : Nontrivial N := not_subsingleton_iff_nontrivial.mp hN
      obtain ⟨x, hx⟩ := exists_ne (0 : N)
      have hxE : (x : E) ≠ 0 := by
        intro h
        exact hx (Subtype.ext h)
      have hn : 0 < ‖(x : E)‖ := norm_pos_iff.mpr hxE
      have hxeq := Module.End.mem_eigenspace_iff.mp x.property
      change S (x : E) = μ.val • (x : E) at hxeq
      have hnorm : ‖S (x : E)‖ ≤ ‖(x : E)‖ := by
        calc
          _ ≤ ‖S‖ * ‖(x : E)‖ := S.le_opNorm x
          _ ≤ 1 * ‖(x : E)‖ := mul_le_mul_of_nonneg_right
            (K.norm_sinAngleOperator_le_one L) (norm_nonneg _)
          _ = _ := one_mul _
      rw [hxeq, norm_smul, Real.norm_eq_abs] at hnorm
      have habs : |μ.val| ≤ 1 := by nlinarith
      have hpos := (K.isPositive_sinAngleOperator L).re_inner_nonneg_left (x : E)
      change 0 ≤ ⟪S (x : E), (x : E)⟫_ℝ at hpos
      rw [hxeq, real_inner_smul_left, real_inner_self_eq_norm_sq] at hpos
      have hnonneg : 0 ≤ μ.val := by nlinarith [sq_pos_of_pos hn]
      have hs0 : 0 < μ.val := lt_of_le_of_ne hnonneg (Ne.symm μ.property)
      have hs1 : μ.val ≤ 1 := (le_abs_self μ.val).trans habs
      by_cases hone : μ.val = 1
      · have hμ : μ = ⟨1, one_ne_zero⟩ := Subtype.ext hone
        rw [hμ]
        exact nuclearSignedSineSpectralFactors_nonempty_one_real K L D hcompact
      · exact (nuclearSignedSineSpectralFactors_nonempty_iff_four_dvd_real K L D hcompact
          μ.val hs0 (lt_of_le_of_ne hs1 hone)).mpr
            (hparity μ.val hs0 (lt_of_le_of_ne hs1 hone))

/-- The numerical root criterion in principal-side multiplicities:
each strictly acute positive sine level has even source multiplicity.
This is the Hilbert-space form of the finite real matching parity. -/
theorem nuclearSignedSineParameters_nonempty_iff_even_source_multiplicity_real
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection)) :
    (nuclearSignedSineParameters K L D).Nonempty ↔
      ∀ s : ℝ, 0 < s → s < 1 →
        Even (Module.finrank ℝ (K.comap
          (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s).subtype)) := by
  rw [nuclearSignedSineParameters_nonempty_iff_four_dvd_real K L D hcompact]
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs0
  apply forall_congr'
  intro _
  rw [finrank_sine_eigenspace_eq_two_mul_source_side_real K L D hcompact s hs0.ne']
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by omega⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by omega⟩

/-- Numerical parity constructs an actual real orthogonal transporter
attaining the projection nuclear lower bound. With trace-class
projection difference this is a finite-cost global minimum. The
statement also retains the extended-valued equality when the trace is
infinite. -/
theorem exists_real_nuclear_transport_of_sine_parity
    (K L : Submodule ℝ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (D : halmosSourceDefect K L ≃ₗᵢ[ℝ] halmosTargetDefect K L)
    (hcompact : IsCompactOperator (K.starProjection - L.starProjection))
    (hparity : ∀ s : ℝ, 0 < s → s < 1 →
      4 ∣ Module.finrank ℝ (Module.End.eigenspace (K.sinAngleOperator L).toLinearMap s)) :
    ∃ T : E ≃ₗᵢ[ℝ] E, K.map T.toLinearMap = L ∧
      (1 - (T : E →L[ℝ] E)).nuclearENorm = (K.starProjection - L.starProjection).nuclearENorm ∧
      ∀ W : E ≃ₗᵢ[ℝ] E, K.map W.toLinearMap = L →
        (1 - (T : E →L[ℝ] E)).nuclearENorm ≤ (1 - (W : E →L[ℝ] E)).nuclearENorm := by
  obtain ⟨A, hA⟩ :=
    (nuclearSignedSineParameters_nonempty_iff_four_dvd_real K L D hcompact).mpr hparity
  obtain ⟨hself, hmod, hcomm, hodd⟩ := (mem_nuclearSignedSineParameters K L D A).mp hA
  refine ⟨nuclearSignedSineTransport K L D A hself hmod hcomm,
    nuclearSignedSineTransport_map K L D A hself hmod hcomm hodd,
    nuclearSignedSineTransport_nuclearENorm K L D A hself hmod hcomm hodd, ?_⟩
  exact fun W hW => nuclearSignedSineTransport_isMin K L D A hself hmod hcomm hodd W hW

end TauCeti.DavisKahan
