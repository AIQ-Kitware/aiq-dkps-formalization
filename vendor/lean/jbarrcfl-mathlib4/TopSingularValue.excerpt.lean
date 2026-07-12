/-
VENDORED SOURCE EXCERPT -- NOT PART OF THE PROJECT BUILD.

Original work:
  Jacob Barr, `Mathlib/Analysis/InnerProductSpace/SingularValuesNorm.lean`
  https://github.com/jbarrcfl/mathlib4
  commit f99fc7704e93eb402469ab24cd6970601aad1141
  blob d0df4abf5a71e8f80e03640f31155fe19b83c5f7
  source lines 124-153
  Apache License 2.0

Local change: this provenance wrapper was added. The source excerpt below is
otherwise copied verbatim. It depends on declarations earlier in the original file.
-/

variable [CompleteSpace E] [CompleteSpace F]

/-- **The operator norm equals the top singular value.**
For a continuous linear map `T` between nontrivial finite-dimensional inner product spaces,
`‖T‖ = σ₀(T)`, the largest singular value. -/
theorem norm_eq_singularValues_zero [Nontrivial E] (T : E →L[𝕜] F) {n : ℕ}
    (hn : finrank 𝕜 E = n) (hn0 : 0 < n) :
    ‖T‖ = (T : E →ₗ[𝕜] F).singularValues 0 := by
  set S : E →L[𝕜] E := ContinuousLinearMap.adjoint T ∘L T with hS
  have hpos : S.IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self T
  have hC : ‖T‖ ^ 2 = ‖S‖ := by
    rw [hS, sq]; exact (norm_adjoint_comp_self T).symm
  have hrank0 := norm_eq_eigenvalues_zero_of_isPositive S hpos hn hn0
  set TL : E →ₗ[𝕜] F := (T : E →ₗ[𝕜] F) with hTL
  have hsig : TL.singularValues 0 ^ 2
      = TL.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨0, hn0⟩ :=
    TL.sq_singularValues_of_lt hn hn0
  have heig : hpos.isSymmetric.eigenvalues hn ⟨0, hn0⟩
      = TL.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨0, hn0⟩ := by
    congr 1
  have hsq : ‖T‖ ^ 2 = TL.singularValues 0 ^ 2 := by
    rw [hC, hrank0, heig, ← hsig]
  have hT0 : (0 : ℝ) ≤ ‖T‖ := norm_nonneg T
  have hσ0 : (0 : ℝ) ≤ TL.singularValues 0 := TL.singularValues_nonneg 0
  nlinarith [hsq, hT0, hσ0, sq_nonneg (‖T‖ - TL.singularValues 0),
    sq_nonneg (‖T‖ + TL.singularValues 0)]

end ContinuousLinearMap
