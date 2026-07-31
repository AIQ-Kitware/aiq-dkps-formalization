/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Matrix spectra, concentration, and the toolkit of spectral statistics: suggested signatures

The roadmap prose is authoritative.  This file records representative target
shapes using names already present in the staged `ForTauCeti` implementation;
it is not exhaustive, and discharging everything here finishes neither a Part
nor the roadmap.
-/

namespace TauCetiRoadmap.MatrixStatistics

open MeasureTheory InnerProductSpace
open scoped ENNReal Matrix

/-! ## Part A -- rank factorization and positive-semidefinite Gram factorization (T21) -/

section RankFactorization

variable {𝕜 : Type*} [Field 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Rank at most `r` is exactly factorization through `Fin r`. -/
theorem rank_le_iff_exists_eq_mul (M : Matrix m n 𝕜) (r : ℕ) :
    M.rank ≤ r ↔ ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := sorry

/-- **The multidimensional-scaling embedding step**, as an iff: a matrix is
positive semidefinite of rank at most `d` exactly when it is the Gram matrix of
`n` points in `d`-dimensional space. -/
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {𝕜 : Type*} [RCLike 𝕜] [PartialOrder 𝕜] [StarOrderedRing 𝕜]
    {n d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := sorry

end RankFactorization

/-! ## Part B -- Berge's maximum theorem over a fixed compact feasible set (T22) -/

section Berge

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
variable {K : Set X} {g : P → X → ℝ}

/-- Compactness form of approximate-minimizer stability: an approximate minimizing
sequence on a compact feasible set has a subsequence converging to a true minimizer.
This one is proved, and it is the statement the Berge argument below consumes. -/
theorem exists_subseq_tendsto_isMinOn_of_approxMinOn [FirstCountableTopology X]
    (hK : IsCompact K) {F : X → ℝ} (hF : Continuous F)
    {z : ℕ → X} (hz : ∀ k, z k ∈ K)
    {ε : X → ℕ → ℝ} (hε : ∀ x ∈ K, Filter.Tendsto (ε x) Filter.atTop (nhds 0))
    (happrox : ∀ x ∈ K, ∀ k, F (z k) ≤ F x + ε x k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ψ ∈ K, IsMinOn F K ψ ∧
      Filter.Tendsto (fun t => z (φ t)) Filter.atTop (nhds ψ) := sorry

/-! **The quantitative stability statement is deliberately unnamed.**  A
`approxMinimizer_stability_target` placeholder stood here, and it named nothing: the
prose behind it -- "an approximate minimizer at a nearby parameter is close to the
argmin set" -- is three different theorems depending on the quantifier order, and the
one worth proving has a shape like

```text
∀ ε > 0, ∃ δ > 0, ∃ η > 0, dist p p₀ < δ → x ∈ K → IsApproxMinOn (g p) K η x →
  ∃ x₀ ∈ K, IsMinOn (g p₀) K x₀ ∧ dist x x₀ < ε
```

Once that signature is fixed, `exists_isMinOn_dist_lt_of_approxMinOn` names it from its
conclusion.  Guessing the name before the quantifiers are settled is what produced the
placeholder. -/

/-- **Berge, argmin half**: the argmin correspondence over a fixed compact
feasible set is upper hemicontinuous, through Mathlib's own predicate.

The clean name belongs to this statement.  The staged proof additionally assumes
`[FirstCountableTopology X]`, which is a proof artifact -- it goes through the
sequential characterization -- so if both versions coexist it is the *restricted* one
that should be qualified (`..._of_firstCountable`) or kept private, not this one.

`IsMinOn` rather than an invented argmin-set API: the predicate is Mathlib's. -/
theorem upperHemicontinuousAt_isMinOn [T2Space X]
    (hK : IsCompact K) (hg : Continuous (Function.uncurry g))
    (p₀ : P) [(nhds p₀).IsCountablyGenerated] :
    UpperHemicontinuousAt (fun p => {x ∈ K | IsMinOn (g p) K x}) p₀ := sorry

/-- **Berge, value half**: the value function is continuous.

Stated without `[FirstCountableTopology P]`.  The staged proof carries that hypothesis
and this is the intended endpoint, so the general theorem should own the clean name and
the sequential one be qualified if it has to survive. -/
theorem continuous_iInf_of_isCompact
    (hK : IsCompact K) (hKne : K.Nonempty) (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ⨅ x : ↥K, g p ↑x) := sorry

end Berge

/-! ## Part C -- matrix spectra and spectral measurability (T19) -/

section MatrixSpectra

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- `Matrix` is a type-level `def`, so the pi `MeasurableSpace` instance does not fire
through it.  The staged library names this instance for the same reason; without it the
measurability statement below does not elaborate. -/
instance instMeasurableSpaceMatrix : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin n → ℝ))

/-- Sorted eigenvalues of a Hermitian matrix, the ordering every perturbation
statement below is stated against. -/
noncomputable def sortedEigenvalues {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : Fin n → ℝ := sorry

/-- **Weyl composed with the entrywise bridge**: an entrywise `ε`-perturbation
moves each sorted eigenvalue by at most `n·ε`.  The entrywise-to-operator-norm
comparison is one of the two Mathlib gaps this Part states precisely. -/
theorem abs_sortedEigenvalues_sub_le_of_entry_le {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hAhat : Ahat.IsHermitian)
    {ε : ℝ} (hentry : ∀ i j, |Ahat i j - A i j| ≤ ε) (k : Fin n) :
    |sortedEigenvalues hAhat k - sortedEigenvalues hA k| ≤ (n : ℝ) * ε := sorry

/-- The spectral `h`-transform of a Hermitian matrix. -/
noncomputable def specTransform (h : ℝ → ℝ) {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : Matrix (Fin n) (Fin n) ℝ := sorry

/-- **Spectral measurability**: the `h`-transform of a measurable Hermitian
random matrix is measurable — without which no probability statement about a
sample eigenspace is well-posed. -/
theorem measurable_specTransform (h : ℝ → ℝ) (hh : Continuous h)
    {Bm : Ω → Matrix (Fin n) (Fin n) ℝ} (hBmeas : Measurable Bm)
    (hsym : ∀ ω, (Bm ω).IsHermitian) :
    Measurable fun ω => specTransform h (hsym ω) := sorry

end MatrixSpectra

/-! ## Part D -- sample moments and matrix concentration (T20)

Chebyshev plus a union bound over `n²` entries, converted to a spectral bound
by Part C.  The elementary route is dimension-suboptimal by design: matrix
Bernstein would give `log n` in place of `n`, at the cost of Laplace-transform
machinery Mathlib does not have. -/

section Concentration

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- **Eigenvalue concentration of a sample matrix**: second moments of the
entries give, by Chebyshev and a union bound, simultaneous control of every
sorted eigenvalue with probability `1 − n²v/η²`. -/
theorem measure_forall_abs_sortedEigenvalues_sub_le_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hSherm : ∀ ω, (Shat ω).IsHermitian) (hAherm : A.IsHermitian)
    (hmeas : ∀ k l, Measurable fun ω => Shat ω k l)
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k, |sortedEigenvalues (hSherm ω) k - sortedEigenvalues hAherm k|
        ≤ (n : ℝ) * η} ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := sorry

/-- The empirical mean of a finite family. -/
noncomputable def finiteMean (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {n : ℕ} (z : Fin n → E) : E :=
  ((n : 𝕜)⁻¹) • ∑ i, z i

/-- The unnormalized centered scatter operator `∑ᵢ (zᵢ − mean z) ⊗ (zᵢ − mean z)`. -/
noncomputable def centeredScatter (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {n : ℕ} (z : Fin n → E) : E →L[𝕜] E :=
  ∑ i, rankOne 𝕜 (z i - finiteMean 𝕜 z) (z i - finiteMean 𝕜 z)

/-- **The exact add-one update for the centered scatter operator**, the streaming
identity of the sample-moment layer.

Named for the operation rather than as a target: this is an exact identity, and the
staged library proves it under this name.  `_snoc` would be marginally more literal --
the implementation appends with `Fin.snoc` -- but `append` names the mathematics. -/
theorem centeredScatter_append (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {n : ℕ} (z : Fin n → E) (y : E) :
    centeredScatter 𝕜 (Fin.snoc z y) = centeredScatter 𝕜 z +
      ((n : 𝕜) / ((n : 𝕜) + 1)) •
        rankOne 𝕜 (y - finiteMean 𝕜 z) (y - finiteMean 𝕜 z) := sorry

end Concentration

end TauCetiRoadmap.MatrixStatistics
