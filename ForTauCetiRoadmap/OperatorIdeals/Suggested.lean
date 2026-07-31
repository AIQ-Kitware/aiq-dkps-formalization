/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Operator ideals: suggested signatures

The roadmap prose is authoritative.  This file records representative target
shapes using names already present in the staged `ForTauCeti` implementation;
it is not exhaustive, and discharging everything here finishes neither a Part
nor the roadmap.
-/

namespace TauCetiRoadmap.OperatorIdeals

open Module (finrank)
open scoped InnerProductSpace ENNReal
open Filter Topology

universe u v w x y

/-! ## Part A -- approximation numbers (T09)

Field-generic on normed spaces; the Hilbert identifications come later in the
Part.  Zero-based indexing: `a₀(T) = ‖T‖`. -/

section ApproximationNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H : Type y} [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The `n`-th approximation number: the distance from `T` to the operators of
rank at most `n`. -/
noncomputable def approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ :=
  ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖

@[simp] theorem approximationNumber_index_zero (T : E →L[𝕜] F) :
    approximationNumber T 0 = ‖T‖ := sorry

theorem approximationNumber_antitone (T : E →L[𝕜] F) :
    Antitone (approximationNumber T) := sorry

/-- Additivity across indices: the mixed subadditivity law of `s`-number theory. -/
theorem approximationNumber_add_le (S T : E →L[𝕜] F) (m n : ℕ) :
    approximationNumber (S + T) (m + n)
      ≤ approximationNumber S m + approximationNumber T n := sorry

/-- Composition multiplicativity across indices.

**The name carries `add` deliberately.**  `approximationNumber_comp_comp_le` is
already taken, by the *two-sided ideal* bound
`aₙ(L ∘ T ∘ R) ≤ ‖L‖ · aₙ(T) · ‖R‖`, which is a different theorem at a fixed
index; this one splits the index.  Naming the index addition also keeps it
legible beside `approximationNumber_add_le` and distinguishes it from the
fixed-index bounds `approximationNumber_comp_le_mul_norm` and
`approximationNumber_comp_le_norm_mul`. -/
theorem approximationNumber_comp_add_le_mul (S : F →L[𝕜] G) (T : E →L[𝕜] F) (m n : ℕ) :
    approximationNumber (S ∘L T) (m + n)
      ≤ approximationNumber S m * approximationNumber T n := sorry

/-- The two-sided ideal inequality, at a fixed index.  Recorded here because it
owns the name `approximationNumber_comp_comp_le`; the theorem above is the
index-splitting statement and must not reuse it. -/
theorem approximationNumber_comp_comp_le {G' H' : Type*}
    [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']
    [SeminormedAddCommGroup H'] [NormedSpace 𝕜 H']
    (L : F →L[𝕜] G') (T : E →L[𝕜] F) (R : H' →L[𝕜] E) (n : ℕ) :
    approximationNumber (L ∘L T ∘L R) n ≤ ‖L‖ * approximationNumber T n * ‖R‖ := sorry

end ApproximationNumbers

section HilbertIdentifications

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Adjoint invariance, the Hilbert-space symmetry the Banach theory lacks. -/
@[simp] theorem approximationNumber_adjoint (T : E →L[ℂ] F) (n : ℕ) :
    approximationNumber (ContinuousLinearMap.adjoint T) n
      = approximationNumber T n := sorry

/-- On finite-dimensional inner-product spaces, the approximation numbers are the
singular values: Eckart--Young. -/
theorem approximationNumber_eq_singularValues
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (T : E →L[ℂ] F) (n : ℕ) :
    approximationNumber T n = (T : E →ₗ[ℂ] F).singularValues n := sorry

/-- The min--max principle in the form the perturbation theory consumes: a subspace of
rank greater than `n` on which `T` is `c`-coercive forces `aₙ(T) ≥ c`.

Deliberately not called `approximationNumber_minmax`: this is one direction, and a name
claiming the equality would overstate what the declaration says. -/
theorem le_approximationNumber_of_lt_rank (T : E →L[ℂ] F) (n : ℕ) (V : Submodule ℂ E)
    {c : ℝ} (hVrank : (n : Cardinal) < Module.rank ℂ V)
    (hV : ∀ x : V, c * ‖(x : E)‖ ≤ ‖T (x : E)‖) :
    c ≤ approximationNumber T n := sorry

end HilbertIdentifications

/-! ## Part B -- symmetric operator ideals and Schatten norms (T10)

One interface, gauge-valued in `ℝ≥0∞`, quantified over all Hilbert pairs; the
concrete norms are instances rather than parallel developments. -/

section IdealFamilies

/-- An operator ideal family over `𝕜`: a gauge on every Hilbert pair, with
subadditivity, absolute homogeneity, domination of the operator norm, and the
two-sided ideal law. -/
structure OperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → ℝ≥0∞
  gauge_add_le : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A B : E →L[𝕜] F), gauge (A + B) ≤ gauge A + gauge B
  gauge_smul : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) (A : E →L[𝕜] F), gauge (c • A) = ‖c‖ₑ * gauge A
  enorm_le_gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), ‖A‖ₑ ≤ gauge A

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {ι : Type x}

/-- The Hilbert--Schmidt energy in `ℝ≥0∞`: no summability side conditions
anywhere, and basis independence is a theorem rather than a hypothesis. -/
noncomputable def hilbertSchmidtEnergy (T : F →L[𝕜] E) (b : HilbertBasis ι 𝕜 F) : ℝ≥0∞ :=
  ∑' i, ‖T (b i)‖ₑ ^ 2

/-- Basis independence of the energy, by Parseval and unconditional Fubini. -/
theorem hilbertSchmidtEnergy_indep {ι' : Type y} (T : F →L[𝕜] E)
    (b : HilbertBasis ι 𝕜 F) (c : HilbertBasis ι' 𝕜 F) :
    hilbertSchmidtEnergy T b = hilbertSchmidtEnergy T c := sorry

/-- The nuclear gauge: the series of approximation numbers.  Its triangle
inequality is the Ky Fan inequality in the limit. -/
noncomputable def nuclearENorm (T : E →L[𝕜] F) : ℝ≥0∞ := sorry

/-- **Milestone B2, the Ky Fan dominance principle.**  Dominance is a *property of a
family*, not a theorem about every family: it is false for an arbitrary
`OperatorIdealFamily`, and stating it as one would compete with the consumer-facing
field the staged library already has,
`IsKyFanDominant.gauge_le_of_forall_kyFanGauge_le`.

What is genuinely open is the **construction**: a family built from a symmetric
gauge is Ky Fan dominant.  Its name should follow the constructor's, so it is left
unnamed here rather than guessed -- `isKyFanDominant_symmetricGaugeFamily` if the
constructor lands as `symmetricGaugeFamily`. -/
class IsKyFanDominant (Φ : OperatorIdealFamily ℂ) : Prop where
  gauge_le_of_forall_kyFanGauge_le : True

/-- **Milestone B3**: finite-dimensional Schatten `p`-norms for real `p ≥ 1` on
the singular-value vector, with the endpoint identifications `S₁` nuclear,
`S₂` Frobenius, `S∞` operator norm. -/
noncomputable def schattenNorm (p : ℝ)
    {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : E →ₗ[ℂ] F) : ℝ := sorry

end IdealFamilies

/-! ## Part C -- Hilbert-Schmidt operators as `ℓ²` of columns (T11)

`lp (fun _ : ι => E) 2` is the Hilbert--Schmidt space; it arrives with Mathlib's
inner product and completeness already proved, which the tensor-product model
would have to re-derive. -/

section HilbertSchmidt

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {ι : Type x}

/-- The columns of an operator in a Hilbert basis. -/
noncomputable def columns (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) : ι → E :=
  fun i => T (b i)

/-- Membership in `ℓ²` of the columns is exactly finiteness of the energy —
the bridge from the model to the ideal theory of Part B. -/
theorem memLp_columns_iff (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) :
    Memℓp (columns b T) 2 ↔ hilbertSchmidtEnergy T b ≠ ⊤ := sorry

/-- The representation map: an `ℓ²` family of columns determines a bounded
operator through the absolutely convergent expansion against the basis. -/
noncomputable def ofLp (b : HilbertBasis ι 𝕜 F) (f : lp (fun _ : ι => E) 2) :
    F →L[𝕜] E := sorry

/-- Round trip: the columns of the represented operator are the family. -/
theorem columns_ofLp (b : HilbertBasis ι 𝕜 F) (f : lp (fun _ : ι => E) 2) :
    columns b (ofLp b f) = f := sorry

/-- The `ℓ²` norm is the Hilbert--Schmidt norm. -/
theorem norm_sq_eq_tsum_norm_column_sq (b : HilbertBasis ι 𝕜 F)
    (f : lp (fun _ : ι => E) 2) :
    ‖f‖ ^ 2 = ∑' i, ‖ofLp b f (b i)‖ ^ 2 := sorry

/-- **Milestone C1, isometric conjugation**: composition with a norm-preserving
map on the left and a map with norm-preserving adjoint on the right preserves
the energy — what makes the Sylvester flow a unitary group on this space. -/
theorem hilbertSchmidtEnergy_isometry_comp (b : HilbertBasis ι 𝕜 F)
    (U : E →L[𝕜] E) (hU : ∀ x, ‖U x‖ = ‖x‖) (T : F →L[𝕜] E) :
    hilbertSchmidtEnergy (U ∘L T) b = hilbertSchmidtEnergy T b := sorry

/-- **Milestone C2, Pythagoras along an orthogonal family**: a family splitting
every vector's norm splits the energy, with no countability or summability
side conditions. -/
theorem tsum_energy_isometryFamily_comp {κ : Type y} (b : HilbertBasis ι 𝕜 F)
    (P : κ → (E →L[𝕜] E)) (hP : ∀ v : E, ∑' k, ‖P k v‖ₑ ^ 2 = ‖v‖ₑ ^ 2)
    (T : F →L[𝕜] E) :
    ∑' k, hilbertSchmidtEnergy ((P k) ∘L T) b = hilbertSchmidtEnergy T b := sorry

end HilbertSchmidt

end TauCetiRoadmap.OperatorIdeals
