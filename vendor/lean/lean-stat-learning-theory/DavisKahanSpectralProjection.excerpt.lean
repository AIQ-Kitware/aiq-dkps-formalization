/-
VENDORED SOURCE EXCERPT -- NOT PART OF THE PROJECT BUILD.

Original work:
  Yuanhe Zhang, Jason D. Lee, Fanghui Liu
  `SLT/MatrixInfra/Perturb.lean`
  https://github.com/YuanheZ/lean-stat-learning-theory
  commit 216e578c9576bab6b0abc3ba6c65762536768e96
  blob 1de3e2023f6051fe75f2fb4ecb6ec437fb6cf118
  source lines 540-649
  Apache License 2.0

Local change: this provenance wrapper was added. The source excerpt below is
otherwise copied verbatim. It depends on definitions and lemmas earlier in the
original file, including `spectralSubspace`, `spectralProjection`, and the
centered spectral-subspace coercivity estimates.
-/

/--
HDP Lemma 4.1.16 in the centered form used in the proof.

If the selected eigenvalues of `A` lie within distance `r` of `c`, while the selected
eigenvalues of `B` are at least distance `r + δ` from `c`, then the product of the corresponding
spectral projections satisfies `‖QP‖ ≤ ‖A - B‖ / δ`.
-/
theorem davisKahan_spectralProjection_centered {n : ℕ}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hn : finrank 𝕜 E = n)
    {I J : Set ℝ} {c r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hI : ∀ i : Fin n, hA.eigenvalues hn i ∈ I →
      |hA.eigenvalues hn i - c| ≤ r)
    (hJ : ∀ j : Fin n, hB.eigenvalues hn j ∈ J →
      r + δ ≤ |hB.eigenvalues hn j - c|) :
    ‖(hB.spectralProjection hn J).toContinuousLinearMap.comp
        (hA.spectralProjection hn I).toContinuousLinearMap‖ ≤
      ‖(A - B).toContinuousLinearMap‖ / δ := by
  let P : E →L[𝕜] E := (hA.spectralProjection hn I).toContinuousLinearMap
  let Q : E →L[𝕜] E := (hB.spectralProjection hn J).toContinuousLinearMap
  let S : E →L[𝕜] E := Q.comp P
  let TA : E →L[𝕜] E :=
    (A - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E)).toContinuousLinearMap
  let TB : E →L[𝕜] E :=
    (B - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E)).toContinuousLinearMap
  let H : E →L[𝕜] E := (B - A).toContinuousLinearMap
  have hgap_nonneg : 0 ≤ r + δ := add_nonneg hr hδ.le
  have hSrange : ∀ x : E, S x ∈ hB.spectralSubspace hn J := by
    intro x
    exact hB.spectralProjection_apply_mem hn J (P x)
  have hlower :
      (r + δ) * ‖S‖ ≤ ‖TB.comp S‖ := by
    simpa [TB] using
      hB.mul_norm_le_norm_shifted_comp_of_forall_mem_spectralSubspace
        hn hgap_nonneg hJ S hSrange
  have hHnorm : ‖H‖ = ‖(A - B).toContinuousLinearMap‖ := by
    simpa [H] using norm_toContinuousLinearMap_sub_rev A B
  have hHterm :
      ‖Q.comp (H.comp P)‖ ≤ ‖(A - B).toContinuousLinearMap‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro x
    have hQle : ‖Q ((H.comp P) x)‖ ≤ ‖(H.comp P) x‖ := by
      simpa [Q] using hB.norm_spectralProjection_apply_le hn J ((H.comp P) x)
    have hHle : ‖(H.comp P) x‖ ≤ ‖H‖ * ‖P x‖ := H.le_opNorm (P x)
    have hPle : ‖P x‖ ≤ ‖x‖ := by
      simpa [P] using hA.norm_spectralProjection_apply_le hn I x
    calc
      ‖(Q.comp (H.comp P)) x‖ = ‖Q ((H.comp P) x)‖ := rfl
      _ ≤ ‖(H.comp P) x‖ := hQle
      _ ≤ ‖H‖ * ‖P x‖ := hHle
      _ ≤ ‖H‖ * ‖x‖ := mul_le_mul_of_nonneg_left hPle (norm_nonneg H)
      _ = ‖(A - B).toContinuousLinearMap‖ * ‖x‖ := by rw [hHnorm]
  have hTAfactor : Q.comp (TA.comp P) = S.comp (TA.comp P) := by
    ext x
    have hxP : P x ∈ hA.spectralSubspace hn I := by
      simpa [P] using hA.spectralProjection_apply_mem hn I x
    have hTAmem :
        (A - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E)) (P x) ∈
          hA.spectralSubspace hn I :=
      hA.shifted_apply_mem_spectralSubspace hn I c hxP
    have hfix :
        hA.spectralProjection hn I
            ((A - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E)) (P x)) =
          (A - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E)) (P x) :=
      (hA.spectralProjection_eq_self_iff hn I).mpr hTAmem
    change
      Q ((A - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E)) (P x)) =
        Q (hA.spectralProjection hn I
          ((A - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E)) (P x)))
    exact congrArg Q hfix.symm
  have hTAop : ‖TA.comp P‖ ≤ r := by
    simpa [TA, P] using hA.norm_shifted_comp_spectralProjection_le hn hr hI
  have hTAterm :
      ‖Q.comp (TA.comp P)‖ ≤ r * ‖S‖ := by
    rw [hTAfactor]
    calc
      ‖S.comp (TA.comp P)‖ ≤ ‖S‖ * ‖TA.comp P‖ :=
        ContinuousLinearMap.opNorm_comp_le S (TA.comp P)
      _ ≤ ‖S‖ * r := mul_le_mul_of_nonneg_left hTAop (norm_nonneg S)
      _ = r * ‖S‖ := by ring
  have hdecomp :
      TB.comp S = Q.comp (H.comp P) + Q.comp (TA.comp P) := by
    ext x
    have hcommB := LinearMap.congr_fun
      (hB.shifted_comp_spectralProjection_eq_spectralProjection_comp_shifted hn J c)
      (P x)
    change
      (B - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E))
          (hB.spectralProjection hn J (P x)) =
        hB.spectralProjection hn J
            ((B - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E)) (P x)) at hcommB
    change
      (B - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E))
          (hB.spectralProjection hn J (P x)) =
        hB.spectralProjection hn J ((B - A) (P x)) +
          hB.spectralProjection hn J
            ((A - ((c : 𝕜) • LinearMap.id : E →ₗ[𝕜] E)) (P x))
    rw [hcommB, ← map_add]
    congr 1
    simp [sub_eq_add_neg, add_assoc]
  have hupper :
      ‖TB.comp S‖ ≤ ‖(A - B).toContinuousLinearMap‖ + r * ‖S‖ := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans (add_le_add hHterm hTAterm)
  have hdeltaS : δ * ‖S‖ ≤ ‖(A - B).toContinuousLinearMap‖ := by
    nlinarith
  have htarget : ‖S‖ * δ ≤ ‖(A - B).toContinuousLinearMap‖ := by
    nlinarith
  have hmain := (le_div_iff₀ hδ).mpr htarget
  simpa [S, P, Q] using hmain
