/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

module

public import DavisKahan.Sources.DavisKahan1970.Section6AppendixLeakage

public section

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Lemma 6.3 over a real Hilbert space

Standing assumption 1 of the transcription puts the paper on a separable
Hilbert space that may be **real or complex**, with finite dimensionality only
a special case.  `Section6AppendixLeakage.lean` proves Lemma 6.3 over `ℂ`; this
module supplies the real form, at arbitrary dimension.

The proof uses the scalar-generic leakage estimate with the orthogonal
splitting of square energy supplied by TauCeti's Hilbert–Schmidt API.
-/

open scoped InnerProductSpace BigOperators ENNReal
open Finset

namespace TauCeti
namespace DavisKahan1970
namespace Section6Appendix

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **Davis--Kahan 1970, Lemma 6.3, over a real Hilbert space of arbitrary
dimension.**

Word for word the statement of `lemma6_3_approximationNumber_leakage_complex` with
`InnerProductSpace ℂ` replaced by `InnerProductSpace ℝ`: the source-faithful
block hypothesis `K ∘ P = Q ∘ K ∘ P`, a rank bound on the selected target
block, and near-saturation of the first-`n` square energy force the off-block
operator norm below `η`.  The rank bound on `P` is retained for source symmetry;
only the bound on `Q` is used. -/
theorem lemma6_3_approximationNumber_leakage_real
    (K : E →L[ℝ] F)
    (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℝ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (_hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear : approximationEnergy (K ∘L P.starProjection) n >
      approximationEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  exact lemma6_3_approximationNumber_leakage K P Q n hn η hη hKP hrankQ hnear

/-- Finite-dimensional real singular-value specialization of Lemma 6.3. -/
theorem lemma6_3_singularValue_leakage_real
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : E →L[ℝ] F)
    (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℝ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear :
      ∑ i ∈ Finset.range n,
          ((LinearMap.singularValues
            (K ∘L P.starProjection).toLinearMap i : ℝ) ^ 2) >
        ∑ i ∈ Finset.range n,
          ((LinearMap.singularValues K.toLinearMap i : ℝ) ^ 2) - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  apply lemma6_3_approximationNumber_leakage_real
    K P Q n hn η hη hKP hrankP hrankQ
  simpa only [approximationEnergy_eq_singularValues] using hnear

end Section6Appendix
end DavisKahan1970
end TauCeti
