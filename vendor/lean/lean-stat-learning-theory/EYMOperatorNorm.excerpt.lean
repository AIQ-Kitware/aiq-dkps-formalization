/-
VENDORED SOURCE EXCERPT -- NOT PART OF THE PROJECT BUILD.

Original work:
  Yuanhe Zhang, Jason D. Lee, Fanghui Liu
  `SLT/MatrixInfra/EYM.lean`
  https://github.com/YuanheZ/lean-stat-learning-theory
  commit 216e578c9576bab6b0abc3ba6c65762536768e96
  blob ef6e16a2942555987e9bfc4d944f96838d72627f
  source lines 227-347
  Apache License 2.0

Local change: this provenance wrapper was added. The source excerpt below is
otherwise copied verbatim. It depends on declarations earlier in the original file.
-/

/--
The lower-bound half of the operator-norm Eckart-Young-Mirsky theorem.

With zero-based singular values, if `B` has rank at most `k`, then the operator-norm error
`‖T - B‖` is at least `T.singularValues k`, the first singular value not captured by a rank-`k`
truncation. This is the min-max obstruction in HDP Theorem 4.1.13.
-/
theorem eckartYoungMirsky_opNorm_lower_bound
    (T B : E →ₗ[𝕜] F) {n k : ℕ} (hn : finrank 𝕜 E = n) (hk : k < n)
    (hB : finrank 𝕜 B.range ≤ k) :
    T.singularValues k ≤ ‖(T - B).toContinuousLinearMap‖ := by
  let i : Fin n := ⟨k, hk⟩
  let L : Submodule 𝕜 E :=
    T.isSymmetric_adjoint_comp_self.leadingEigenSubspace hn (Nat.succ_le_of_lt i.2)
  have hLdim : finrank 𝕜 L = k + 1 := by
    simpa [L, i] using
      T.isSymmetric_adjoint_comp_self.finrank_leadingEigenSubspace hn
        (Nat.succ_le_of_lt i.2)
  have hkerdim : finrank 𝕜 B.ker = n - finrank 𝕜 B.range := by
    have h := B.finrank_range_add_finrank_ker
    rw [hn] at h
    omega
  have hinter :
      finrank 𝕜 E < finrank 𝕜 L + finrank 𝕜 B.ker := by
    rw [hn, hLdim, hkerdim]
    omega
  obtain ⟨x, hxL, hxker, hx0⟩ :=
    Submodule.exists_ne_zero_mem_inf_of_finrank_lt_add_finrank L B.ker hinter
  have hsing_le : T.singularValues k ≤ singularQuotient T x := by
    simpa [i] using
      singularValues_le_singularQuotient_of_mem_gram_leadingEigenSubspace T hn i
        (by simpa [L] using hxL) hx0
  have hquot_le : singularQuotient T x ≤ ‖(T - B).toContinuousLinearMap‖ := by
    unfold singularQuotient
    have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hTx : T x = (T - B) x := by
      simp [LinearMap.sub_apply, LinearMap.mem_ker.mp hxker]
    rw [hTx]
    exact (div_le_iff₀ hxnorm).mpr ((T - B).toContinuousLinearMap.le_opNorm x)
  exact hsing_le.trans hquot_le

/-- Exact-rank approximants satisfy the same Eckart-Young-Mirsky lower bound. -/
theorem eckartYoungMirsky_opNorm_lower_bound_of_finrank_range_eq
    (T B : E →ₗ[𝕜] F) {n k : ℕ} (hn : finrank 𝕜 E = n) (hk : k < n)
    (hB : finrank 𝕜 B.range = k) :
    T.singularValues k ≤ ‖(T - B).toContinuousLinearMap‖ :=
  eckartYoungMirsky_opNorm_lower_bound T B hn hk hB.le

/--
The canonical rank-`k` truncation has operator-norm error at most the next singular value.
-/
theorem eckartYoungMirskyApproximant_opNorm_error_le
    (T : E →ₗ[𝕜] F) {n k : ℕ} (hn : finrank 𝕜 E = n) (hk : k < n) :
    ‖(T - T.eckartYoungMirskyApproximant hn (Nat.le_of_lt hk)).toContinuousLinearMap‖ ≤
      T.singularValues k := by
  let i : Fin n := ⟨k, hk⟩
  let L : Submodule 𝕜 E :=
    T.isSymmetric_adjoint_comp_self.leadingEigenSubspace hn (Nat.le_of_lt hk)
  haveI : CompleteSpace L := FiniteDimensional.complete 𝕜 L
  let B : E →ₗ[𝕜] F := T.eckartYoungMirskyApproximant hn (Nat.le_of_lt hk)
  refine ((T - B).toContinuousLinearMap).opNorm_le_bound (T.singularValues_nonneg k) ?_
  intro x
  change ‖(T - B) x‖ ≤ T.singularValues k * ‖x‖
  let y : E := x - L.starProjection x
  have h_apply : (T - B) x = T y := by
    simp [B, eckartYoungMirskyApproximant, L, y, LinearMap.sub_apply, map_sub]
  rw [h_apply]
  by_cases hy0 : y = 0
  · rw [hy0, map_zero, norm_zero]
    exact mul_nonneg (T.singularValues_nonneg k) (norm_nonneg x)
  have hyOrth : y ∈ Lᗮ := by
    simp [y]
  have hyTrailing :
      y ∈ T.isSymmetric_adjoint_comp_self.trailingEigenSubspace hn i := by
    simpa [L, i] using
      T.isSymmetric_adjoint_comp_self.leadingEigenSubspace_orthogonal_le_trailingEigenSubspace
        hn i hyOrth
  have hquot : singularQuotient T y ≤ T.singularValues k := by
    simpa [i] using
      singularQuotient_le_singularValues_of_mem_gram_trailingEigenSubspace T hn i hyTrailing hy0
  have hTy : ‖T y‖ ≤ T.singularValues k * ‖y‖ := by
    unfold singularQuotient at hquot
    exact (div_le_iff₀ (norm_pos_iff.mpr hy0)).mp hquot
  have hnorm_y : ‖y‖ ≤ ‖x‖ := by
    have hproj : Lᗮ.starProjection x = y := by
      simp [y]
    calc
      ‖y‖ = ‖Lᗮ.starProjection x‖ := by rw [← hproj]
      _ ≤ ‖x‖ := Submodule.norm_starProjection_apply_le (K := Lᗮ) x
  exact hTy.trans (mul_le_mul_of_nonneg_left hnorm_y (T.singularValues_nonneg k))

/--
The canonical rank-`k` truncation attains the operator-norm Eckart-Young-Mirsky value.
-/
theorem eckartYoungMirskyApproximant_opNorm_error_eq
    (T : E →ₗ[𝕜] F) {n k : ℕ} (hn : finrank 𝕜 E = n) (hk : k < n) :
    ‖(T - T.eckartYoungMirskyApproximant hn (Nat.le_of_lt hk)).toContinuousLinearMap‖ =
      T.singularValues k := by
  apply le_antisymm
  · exact eckartYoungMirskyApproximant_opNorm_error_le T hn hk
  · exact eckartYoungMirsky_opNorm_lower_bound T
      (T.eckartYoungMirskyApproximant hn (Nat.le_of_lt hk)) hn hk
      (finrank_range_eckartYoungMirskyApproximant_le T hn (Nat.le_of_lt hk))

/--
Operator-norm Eckart-Young-Mirsky theorem in zero-based singular-value indexing: among all maps
with rank at most `k`, the optimal error is `T.singularValues k`, and it is attained by the
projection truncation onto the leading Gram eigenspace.
-/
theorem eckartYoungMirsky_opNorm_rank_le_attained
    (T : E →ₗ[𝕜] F) {n k : ℕ} (hn : finrank 𝕜 E = n) (hk : k < n) :
    ∃ B : E →ₗ[𝕜] F,
      finrank 𝕜 B.range ≤ k ∧
        ‖(T - B).toContinuousLinearMap‖ = T.singularValues k ∧
          ∀ C : E →ₗ[𝕜] F, finrank 𝕜 C.range ≤ k →
            T.singularValues k ≤ ‖(T - C).toContinuousLinearMap‖ := by
  refine ⟨T.eckartYoungMirskyApproximant hn (Nat.le_of_lt hk), ?_, ?_, ?_⟩
  · exact finrank_range_eckartYoungMirskyApproximant_le T hn (Nat.le_of_lt hk)
  · exact eckartYoungMirskyApproximant_opNorm_error_eq T hn hk
  · intro C hC
    exact eckartYoungMirsky_opNorm_lower_bound T C hn hk hC
