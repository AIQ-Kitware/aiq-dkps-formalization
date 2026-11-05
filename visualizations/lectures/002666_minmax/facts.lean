/- Applications of the accepted Courant--Fischer and Weyl APIs. -/
import TauCeti.Analysis.InnerProductSpace.CourantFischer

noncomputable section
-- slide-begin
open Module
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} (T S : E →L[ℝ] E)
  (hT : LinearMap.IsSymmetric (T : E →ₗ[ℝ] E))
  (hS : LinearMap.IsSymmetric (S : E →ₗ[ℝ] E))
  (hn : finrank ℝ E = n) (k : Fin n)

example : hT.eigenvalues hn k =
    ⨆ V : {V : Submodule ℝ E //
        finrank ℝ V = (k : ℕ) + 1},
      ⨅ x : {x : E //
          x ∈ (V : Submodule ℝ E) ∧ ‖x‖ = 1},
        RCLike.re ⟪T (x : E), (x : E)⟫_ℝ :=
  hT.eigenvalues_eq_iSup_iInf_re_inner hn k

example :
    |hT.eigenvalues hn k -
      hS.eigenvalues hn k| ≤ ‖T - S‖ :=
  hT.abs_eigenvalue_sub_eigenvalue_le_norm hS hn k
-- slide-end
