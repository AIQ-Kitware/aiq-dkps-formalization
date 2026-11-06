/- Applications of accepted Tau Ceti compression and Ritz-residual APIs.
   Q on the slides is X here; X maps trial coordinates into the ambient space. -/
import TauCeti.Analysis.InnerProductSpace.RayleighRitz

noncomputable section
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (A : E →L[ℝ] E) (X : F →L[ℝ] E) (hX : Isometry X)
-- slide-begin
example : A.compression X =
    ContinuousLinearMap.adjoint X ∘L A ∘L X :=
  A.compression_def X

example : ContinuousLinearMap.adjoint X ∘L
    A.sylvester (A.compression X) X = 0 :=
  A.adjoint_comp_sylvester_compression hX

example (M : F →L[ℝ] F) :
    A.sylvester M X =
      A.sylvester (A.compression X) X +
        X ∘L (A.compression X - M) :=
  A.sylvester_eq_sylvester_compression_add X M
-- slide-end
