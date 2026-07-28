/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.Sequence.WeakSubmajorization
import ForTauCeti.Analysis.OperatorIdeal.Family.Basic
import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint

/-!
# Standard symmetric ideals and Fan dominance

This file gives an honest infinite-dimensional formulation of Fan dominance.
The dominance principle is not included as an axiom of a broadly named ideal
family.  Instead, a standard symmetric ideal is represented by a coherent
symmetric norming function on finite vectors and one of its two classical
completions:

* the **maximal/Fatou ideal**, whose extended gauge is finite exactly when the
  supremum of the finite prefix gauges is finite;
* the **minimal ideal**, the closure of finite-rank operators, characterized by
  vanishing norming-function tails.

The minimal branch is essential.  For the `ell-infinity` norming function it
is the compact-operator ideal with operator norm, while the maximal branch is
all bounded operators.  Thus the theory does not obtain “every standard
ideal” by silently excluding the compact ideal.
-/

namespace TauCeti
namespace FinishTanTwoTheta

open scoped BigOperators ENNReal Topology
open Filter

universe u v

/-- A coherent symmetric norming function, presented by its restrictions to
all finite-dimensional coordinate spaces. -/
structure SymmetricNormingFunction where
  finiteGauge : (n : ℕ) → FiniteSymmetricGauge n
  zeroPad : ∀ (n m : ℕ) (x : Fin n → ℝ),
    finiteGauge (n + m) (FiniteVector.zeroPadRight (m := m) x) =
      finiteGauge n x
  normalized : finiteGauge 1 (fun _ => 1) = 1

namespace SymmetricNormingFunction

/-- The gauge of the first `n` coordinates of a sequence. -/
noncomputable def prefixGauge (Φ : SymmetricNormingFunction)
    (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  Φ.finiteGauge n (sequencePrefixVector n x)

/-- The maximal/Fatou extended gauge of a sequence. -/
noncomputable def sequenceGauge (Φ : SymmetricNormingFunction)
    (x : ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (Φ.prefixGauge n x)

/-- Tail beginning at coordinate `n`. -/
def sequenceTail (n : ℕ) (x : ℕ → ℝ) : ℕ → ℝ :=
  fun j => x (n + j)

/-- Membership in the minimal sequence ideal associated to `Φ`: finite tails
converge to zero in the maximal gauge.  This is equivalent to belonging to the
closure of `c00` in the `Φ` norm. -/
def IsMinimalSequence (Φ : SymmetricNormingFunction) (x : ℕ → ℝ) : Prop :=
  Tendsto (fun n => Φ.sequenceGauge (sequenceTail n x)) atTop (𝓝 0)

/-- Finite prefix gauges are monotone under weak submajorization. -/
theorem prefixGauge_mono_of_weaklySubmajorized
    (Φ : SymmetricNormingFunction) {x y : ℕ → ℝ}
    (hxy : WeaklySubmajorized x y) (n : ℕ) :
    Φ.prefixGauge n x ≤ Φ.prefixGauge n y := by
  exact (Φ.finiteGauge n).mono_weaklyMajorized
    (finite_weaklyMajorized_of_weaklySubmajorized hxy n)

/-- Infinite Fan dominance for the maximal sequence gauge. -/
theorem sequenceGauge_mono_of_weaklySubmajorized
    (Φ : SymmetricNormingFunction) {x y : ℕ → ℝ}
    (hxy : WeaklySubmajorized x y) :
    Φ.sequenceGauge x ≤ Φ.sequenceGauge y := by
  apply iSup_le
  intro n
  refine le_trans ?_ (le_iSup (fun m : ℕ =>
    ENNReal.ofReal (Φ.prefixGauge m y)) n)
  exact ENNReal.ofReal_le_ofReal
    (Φ.prefixGauge_mono_of_weaklySubmajorized hxy n)

/-- **Full symmetry of the minimal completion.**  If `x` is weakly
submajorized by `y` and `y` lies in the finite-sequence closure, then `x` also
lies in that closure.

This is the nontrivial ideal-theory theorem needed to include compact-operator
and other minimal ideals, not just maximal Fatou ideals. -/
theorem isMinimalSequence_of_weaklySubmajorized
    (Φ : SymmetricNormingFunction) {x y : ℕ → ℝ}
    (hxy : WeaklySubmajorized x y) (hy : Φ.IsMinimalSequence y) :
    Φ.IsMinimalSequence x := by
  -- This is the classical Calderon--Mityagin full-symmetry theorem for the
  -- closure of `c00` under a coherent symmetric norming function.  The
  -- compiler lane should match this call to the final sequence-space API.
  exact FullySymmetricSequenceSpace.minimalClosure_mem_of_weakSubmajorized
    (finiteGauge := Φ.finiteGauge) (zeroPad := Φ.zeroPad) hxy hy

/-- The two standard completions associated with a symmetric norming
function. -/
inductive SymmetricIdealCompletion where
  | maximal
  | minimal
  deriving DecidableEq

/-- Extended sequence gauge for either classical completion.  The minimal
completion has the same norm on its carrier and value `∞` off the carrier. -/
noncomputable def standardSequenceGauge
    (Φ : SymmetricNormingFunction) (mode : SymmetricIdealCompletion)
    (x : ℕ → ℝ) : ℝ≥0∞ :=
  match mode with
  | .maximal => Φ.sequenceGauge x
  | .minimal => if Φ.IsMinimalSequence x then Φ.sequenceGauge x else ∞

/-- Fan dominance for both maximal and minimal standard completions. -/
theorem standardSequenceGauge_mono_of_weaklySubmajorized
    (Φ : SymmetricNormingFunction) (mode : SymmetricIdealCompletion)
    {x y : ℕ → ℝ} (hxy : WeaklySubmajorized x y) :
    Φ.standardSequenceGauge mode x ≤ Φ.standardSequenceGauge mode y := by
  cases mode with
  | maximal =>
      exact Φ.sequenceGauge_mono_of_weaklySubmajorized hxy
  | minimal =>
      by_cases hy : Φ.IsMinimalSequence y
      · have hx := Φ.isMinimalSequence_of_weaklySubmajorized hxy hy
        simp [standardSequenceGauge, hx, hy,
          Φ.sequenceGauge_mono_of_weaklySubmajorized hxy]
      · simp [standardSequenceGauge, hy]

end SymmetricNormingFunction

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Approximation numbers as a decreasing nonnegative sequence. -/
def approximationNumberSequence (A : E →L[𝕜] F) : ℕ → ℝ :=
  fun n => A.approximationNumber n

/-- Zero-based Ky Fan prefix built directly from canonical approximation
numbers. -/
def approximationNumberPrefix (k : ℕ) (A : E →L[𝕜] F) : ℝ :=
  sequencePrefixSum k (approximationNumberSequence A)

/-- Approximation-number sequences are decreasing and nonnegative. -/
theorem approximationNumberSequence_antitone_nonneg (A : E →L[𝕜] F) :
    Antitone (approximationNumberSequence A) ∧
      ∀ n, 0 ≤ approximationNumberSequence A n := by
  constructor
  · intro i j hij
    exact A.approximationNumber_antitone hij
  · intro n
    exact A.approximationNumber_nonneg n

/-- All Ky Fan prefix inequalities are exactly weak submajorization of the two
approximation-number sequences. -/
theorem weaklySubmajorized_approximationNumberSequence_iff
    (A B : E →L[𝕜] F) :
    WeaklySubmajorized (approximationNumberSequence A)
        (approximationNumberSequence B) ↔
      ∀ k, approximationNumberPrefix k A ≤ approximationNumberPrefix k B := by
  constructor
  · intro h k
    exact h.prefix_le k
  · intro h
    obtain ⟨hAa, hAn⟩ := approximationNumberSequence_antitone_nonneg A
    obtain ⟨hBa, hBn⟩ := approximationNumberSequence_antitone_nonneg B
    exact ⟨hAa, hBa, hAn, hBn, h⟩

/-- Fan dominance as a capability separate from the definition of a symmetric
operator ideal. -/
class HasFanDominance (N : SymmetricOperatorIdealFamily.{u, v} 𝕜) : Prop where
  gauge_le_of_prefix_le : ∀ {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A B : E →L[𝕜] F),
    (∀ k, approximationNumberPrefix k A ≤ approximationNumberPrefix k B) →
    N.toOperatorIdealFamily.gauge A ≤ N.toOperatorIdealFamily.gauge B

namespace HasFanDominance

/-- Membership descends under Fan dominance because membership is finiteness
of the extended gauge. -/
theorem mem_of_prefix_le
    (N : SymmetricOperatorIdealFamily.{u, v} 𝕜) [HasFanDominance N]
    (A B : E →L[𝕜] F)
    (hB : B ∈ N.toOperatorIdealFamily.carrier)
    (h : ∀ k, approximationNumberPrefix k A ≤ approximationNumberPrefix k B) :
    A ∈ N.toOperatorIdealFamily.carrier := by
  rw [OperatorIdealFamily.mem_carrier_iff] at hB ⊢
  exact ne_top_of_le_ne_top hB
    (HasFanDominance.gauge_le_of_prefix_le A B h)

end HasFanDominance

/-- A standard symmetric ideal is a symmetric operator ideal represented by a
coherent symmetric norming function and either its maximal or minimal
completion. -/
structure StandardSymmetricIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  toSymmetricOperatorIdealFamily : SymmetricOperatorIdealFamily.{u, v} 𝕜
  normingFunction : SymmetricNormingFunction
  completion : SymmetricIdealCompletion
  gauge_eq_standardSequenceGauge : ∀ {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F),
    toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge A =
      normingFunction.standardSequenceGauge completion
        (approximationNumberSequence A)

namespace StandardSymmetricIdealFamily

variable (N : StandardSymmetricIdealFamily.{u, v} 𝕜)

/-- Every standard symmetric ideal, maximal or minimal, satisfies infinite Fan
dominance. -/
instance : HasFanDominance N.toSymmetricOperatorIdealFamily where
  gauge_le_of_prefix_le := by
    intro E F _ _ _ _ _ _ A B hprefix
    rw [N.gauge_eq_standardSequenceGauge A,
      N.gauge_eq_standardSequenceGauge B]
    apply N.normingFunction.standardSequenceGauge_mono_of_weaklySubmajorized
    exact (weaklySubmajorized_approximationNumberSequence_iff A B).2 hprefix

/-- Full membership-and-gauge Fan dominance for every standard symmetric
ideal. -/
theorem fanDominance
    (A B : E →L[𝕜] F)
    (hB : B ∈ N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.carrier)
    (hprefix : ∀ k,
      approximationNumberPrefix k A ≤ approximationNumberPrefix k B) :
    A ∈ N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.carrier ∧
      N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge A ≤
        N.toSymmetricOperatorIdealFamily.toOperatorIdealFamily.gauge B := by
  constructor
  · exact HasFanDominance.mem_of_prefix_le
      N.toSymmetricOperatorIdealFamily A B hB hprefix
  · exact HasFanDominance.gauge_le_of_prefix_le A B hprefix

end StandardSymmetricIdealFamily

end FinishTanTwoTheta
end TauCeti
