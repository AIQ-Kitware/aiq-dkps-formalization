/-
# Rank-controlled PSD Gram realization (pending: only the rank-control is novel) -- solution / dependency audit
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues
public import ForTauCeti.LinearAlgebra.Matrix.PosDef

public section

#print axioms Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le
#print axioms TauCeti.Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
