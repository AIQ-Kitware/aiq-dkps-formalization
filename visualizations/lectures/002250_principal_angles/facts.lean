import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
noncomputable section
-- slide-begin
variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (U V : Submodule ℝ E)

example (i : ℕ) :
    0 ≤ U.principalCosines V i ∧
      U.principalCosines V i ≤ 1 :=
  ⟨U.principalCosines_nonneg V i,
    U.principalCosines_le_one V i⟩

example :
    U.principalCosines V = V.principalCosines U :=
  U.principalCosines_comm V
-- slide-end
