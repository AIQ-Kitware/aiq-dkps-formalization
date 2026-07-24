import Mathlib

/-!
# Approximation numbers and symmetric operator ideals: target signatures

**This file is not the roadmap and is not exhaustive.** The definitive document
is `README.md`. The statements here suggest Lean forms for particular milestones,
so that contributors and reviewers converge on names and signatures; discharging
all of them finishes neither a layer nor the roadmap.

The narrative roadmap, the generality bar, the layers (A–C), and the pinned
conventions are in `README.md`. Mathlib already carries the prerequisite static
stack — `ContinuousLinearMap` and the operator (semi)norm, `LinearMap.rank`, the
`ℝ≥0`/`ℝ` continuous functional calculus and `CFC.sqrt`, finite-dimensional
self-adjoint spectral theory and Courant–Fischer, `ContinuousLinearMap.adjoint`,
and the `NNReal`/`ENNReal`/`tsum` order and summability API. This roadmap builds
the approximation-number (`s`-number) layer and the symmetric-ideal theory on
top.

`sorry` is used honestly for milestone statements whose full form is settled but
not proved here; where a milestone needs a notion whose API does not yet exist,
the condition is omitted rather than named as an empty `Prop`.
-/

namespace TauCetiRoadmap.ApproximationNumbers

open scoped NNReal

/-! ## Layer A — the approximation number and its ideal theory (field-generic)

Over a `NontriviallyNormedField`, seminormed source and target, independent
universes. No inner product. -/

section LayerA

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A.1 — Zero-based approximation number: operator-norm distance to maps of
rank at most `n`, valued in `ℝ≥0`. (Extends the Mathlib `ContinuousLinearMap`
namespace for dot notation; a global-namespace commitment, see README.) -/
noncomputable def approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖₊

@[simp]
theorem approximationNumber_zero_eq_nnnorm (T : E →L[𝕜] F) :
    approximationNumber T 0 = ‖T‖₊ := sorry

/-- A.1 — antitone in the allowed rank. -/
theorem antitone_approximationNumber (T : E →L[𝕜] F) :
    Antitone (approximationNumber T) := sorry

/-- A.2 — the additive ideal inequality. -/
theorem approximationNumber_add_le_add (S T : E →L[𝕜] F) (m n : ℕ) :
    approximationNumber (S + T) (m + n) ≤
      approximationNumber S m + approximationNumber T n := sorry

/-- A.2 — Lipschitz in the operator norm. -/
theorem dist_approximationNumber_le (S T : E →L[𝕜] F) (n : ℕ) :
    dist (approximationNumber S n) (approximationNumber T n) ≤ ‖S - T‖₊ := sorry

/-- A.3 — two-sided ideal (multiplicativity), right factor. -/
theorem approximationNumber_comp_right_le
    (T : F →L[𝕜] G) (B : E →L[𝕜] F) (n : ℕ) :
    approximationNumber (T ∘L B) n ≤ approximationNumber T n * ‖B‖₊ := sorry

/-- A.3 — two-sided ideal (multiplicativity), left factor. -/
theorem approximationNumber_comp_left_le
    (A : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber (A ∘L T) n ≤ ‖A‖₊ * approximationNumber T n := sorry

/-- A.3 — absolute homogeneity. -/
theorem approximationNumber_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber (c • T) n = ‖c‖₊ * approximationNumber T n := sorry

end LayerA

/-! ## Layer B — Hilbert-space identification (adjoint, singular values)

Inner-product source and target over `[RCLike 𝕜]`; real and complex are the two
instances of a single `RCLike` statement. -/

section LayerB

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- B.1 — adjoint invariance. -/
theorem approximationNumber_adjoint (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber (ContinuousLinearMap.adjoint T) n
      = approximationNumber T n := sorry

/-- B.2 — the rectangular operator modulus `|T| = (T⋆T)^{1/2}`, a positive
self-adjoint operator on the source with `‖ |T| x‖ = ‖T x‖`. -/
noncomputable def operatorModulus (T : E →L[𝕜] F) : E →L[𝕜] E := sorry

theorem norm_operatorModulus_apply (T : E →L[𝕜] F) (x : E) :
    ‖operatorModulus T x‖ = ‖T x‖ := sorry

/-- B.2 — approximation numbers are computed from the modulus. -/
theorem approximationNumber_operatorModulus (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber (operatorModulus T) n = approximationNumber T n := sorry

end LayerB

section LayerBFiniteDim

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- B.3 — `n`th zero-based singular value: sorted eigenvalues of `|T|`. Reuses
the finite-dimensional eigenvalue enumeration; no private singular-value
predicate. -/
noncomputable def singularValue (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 := sorry

/-- B.3 — Eckart–Young: approximation numbers are the singular values. -/
theorem approximationNumber_eq_singularValue (T : E →L[𝕜] F) (n : ℕ) :
    approximationNumber T n = singularValue T n := sorry

/-- B.4 — Courant–Fischer min–max for `s`-numbers (finite-dimensional form). -/
theorem approximationNumber_eq_minmax (T : E →L[𝕜] F) (n : ℕ) :
    True := sorry  -- statement pending the subspace-quantifier API; see README B.4

end LayerBFiniteDim

/-! ## Layer C — symmetric operator ideals

Symmetric gauge on finitely supported `ℝ≥0` sequences is the primitive; Ky Fan
`k`-norms and Schatten `p`-norms are instances. Signatures below are deliberately
schematic — the gauge structure is a Layer-C design target, not yet pinned to a
Mathlib class. -/

section LayerC

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- C.2 — Ky Fan `k`-norm: the sum of the first `k` approximation numbers. -/
noncomputable def kyFanNorm (T : E →L[𝕜] F) (k : ℕ) : ℝ≥0 :=
  ∑ n ∈ Finset.range k, approximationNumber T n

/-- C.2 — Ky Fan dominance implies domination by every symmetric gauge. Stated
here only for the Ky Fan norms themselves; the general symmetric-gauge statement
is the Layer-C target (README C.1–C.2). -/
theorem kyFanNorm_mono_of_forall_le {S T : E →L[𝕜] F}
    (h : ∀ k, kyFanNorm S k ≤ kyFanNorm T k) (k : ℕ) :
    kyFanNorm S k ≤ kyFanNorm T k := h k

/-- C.3 — Hilbert–Schmidt via the `ℓ²` gauge on the approximation-number
sequence; the basis-column identity `∑ ‖T eᵢ‖²` is an equivalence theorem for
this one object (README C.3). -/
noncomputable def hilbertSchmidtNorm (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ∑' n : ℕ, ((approximationNumber T n : ℝ≥0∞)) ^ 2

end LayerC

end TauCetiRoadmap.ApproximationNumbers
