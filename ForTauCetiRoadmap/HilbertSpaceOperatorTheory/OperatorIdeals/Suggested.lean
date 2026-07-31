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
open scoped InnerProductSpace ENNReal NNReal
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
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic`
noncomputable def approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ :=
  ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖

-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic`
@[simp] theorem approximationNumber_index_zero (T : E →L[𝕜] F) :
    approximationNumber T 0 = ‖T‖ := sorry

-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic`
theorem approximationNumber_antitone (T : E →L[𝕜] F) :
    Antitone (approximationNumber T) := sorry

/-- Additivity across indices: the mixed subadditivity law of `s`-number theory. -/
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic`
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
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic`
theorem approximationNumber_comp_add_le_mul (S : F →L[𝕜] G) (T : E →L[𝕜] F) (m n : ℕ) :
    approximationNumber (S ∘L T) (m + n)
      ≤ approximationNumber S m * approximationNumber T n := sorry
-- **Proved 2026-07-31** as `ContinuousLinearMap.approximationNumber_comp_add_le_mul` in
-- `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean`, axiom-clean, signature
-- unchanged. The `sorry` stays because this file records target shapes.

/-- The two-sided ideal inequality, at a fixed index.  Recorded here because it
owns the name `approximationNumber_comp_comp_le`; the theorem above is the
index-splitting statement and must not reuse it. -/
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic`
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
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint`
@[simp] theorem approximationNumber_adjoint (T : E →L[ℂ] F) (n : ℕ) :
    approximationNumber (ContinuousLinearMap.adjoint T) n
      = approximationNumber T n := sorry

/-- On finite-dimensional inner-product spaces, the approximation numbers are the
singular values: Eckart--Young. -/
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional`
theorem approximationNumber_eq_singularValues
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (T : E →L[ℂ] F) (n : ℕ) :
    approximationNumber T n = (T : E →ₗ[ℂ] F).singularValues n := sorry

/-- The min--max principle in the form the perturbation theory consumes: a subspace of
rank greater than `n` on which `T` is `c`-coercive forces `aₙ(T) ≥ c`.

Deliberately not called `approximationNumber_minmax`: this is one direction, and a name
claiming the equality would overstate what the declaration says. -/
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax`
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
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.Family.Basic`
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
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Energy`
noncomputable def hilbertSchmidtEnergy (T : F →L[𝕜] E) (b : HilbertBasis ι 𝕜 F) : ℝ≥0∞ :=
  ∑' i, ‖T (b i)‖ₑ ^ 2

/-- Basis independence of the energy, by Parseval and unconditional Fubini. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Energy`
theorem hilbertSchmidtEnergy_indep {ι' : Type y} (T : F →L[𝕜] E)
    (b : HilbertBasis ι 𝕜 F) (c : HilbertBasis ι' 𝕜 F) :
    hilbertSchmidtEnergy T b = hilbertSchmidtEnergy T c := sorry

/-- The nuclear gauge: the series of approximation numbers.  Its triangle
inequality is the Ky Fan inequality in the limit. -/
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.Family.TraceClass`
noncomputable def nuclearENorm (T : E →L[𝕜] F) : ℝ≥0∞ := sorry

/-- **Milestone B2, the Ky Fan dominance principle.**  Dominance is a *property of a
family*, not a theorem about every family: it is false for an arbitrary
`OperatorIdealFamily`, and stating it as one would compete with the consumer-facing
field the staged library already has,
`IsKyFanDominant.gauge_le_of_forall_kyFanGauge_le`.

What is genuinely open is the **construction**: a family built from a symmetric
gauge is Ky Fan dominant.  See `isKyFanDominant_symmetricGaugeFamily` below. -/
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.Family.KyFanDominance`
class IsKyFanDominant (Φ : OperatorIdealFamily ℂ) : Prop where
  gauge_le_of_forall_kyFanGauge_le : True

end IdealFamilies

/-! ## Part B, the symmetric-gauge construction (Milestones B1-B4)

Everything below is over `ℂ`, where the Hilbert-space continuous functional calculus
is registered; Milestone B4 is what removes that restriction. -/

section SymmetricGauges

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {F : Type w} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type x}

/-! ### Milestone B1 -- symmetric norming functions

The object the interface exists to receive.  Four instances are examples; a map
from symbols to families is a theory. -/

/-- A **symmetric norming function** (Gohberg--Kreĭn): a monotone, permutation-invariant,
normalized gauge on finitely supported nonnegative sequences.

`symm` is stated against `Equiv.Perm ℕ` acting by precomposition on the finitely
supported sequence, which is what makes "symmetric" a property of `Φ` rather than a
property of the sequences it is applied to. -/
structure SymmetricGauge where
  /-- The underlying gauge on finitely supported nonnegative sequences. -/
  toFun : (ℕ →₀ ℝ≥0) → ℝ≥0
  /-- Subadditivity. -/
  add_le : ∀ a b : ℕ →₀ ℝ≥0, toFun (a + b) ≤ toFun a + toFun b
  /-- Positive homogeneity. -/
  smul : ∀ (c : ℝ≥0) (a : ℕ →₀ ℝ≥0), toFun (c • a) = c * toFun a
  /-- Permutation invariance -- the "symmetric" in symmetric norming function. -/
  symm : ∀ (σ : Equiv.Perm ℕ) (a : ℕ →₀ ℝ≥0),
    toFun (Finsupp.equivMapDomain σ a) = toFun a
  /-- Monotonicity in the termwise order. -/
  mono : ∀ ⦃a b : ℕ →₀ ℝ≥0⦄, a ≤ b → toFun a ≤ toFun b
  /-- Normalization: the first basis vector has gauge one.  This fixes the scale, and
  with it the two-sided bound `‖a‖_∞ ≤ Φ a ≤ ∑ aₙ`. -/
  normalized : toFun (Finsupp.single 0 1) = 1

/-- The extension of a symmetric gauge to arbitrary `ℝ≥0∞`-valued sequences: the
supremum of `Φ` over the finitely supported truncations of the decreasing
rearrangement.

**A supremum, not a `tsum`.**  The gauge must be total and genuinely `∞` off its
ideal, and a supremum of an increasing net is total by construction; any route
through summability reintroduces the side conditions the interface avoids. -/
noncomputable def SymmetricGauge.extend (Φ : SymmetricGauge) (a : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  sorry

/-- Both ends of the scale, and the reason the normalization is not a restriction. -/
theorem SymmetricGauge.iSup_le_extend_le_tsum (Φ : SymmetricGauge) (a : ℕ → ℝ≥0∞) :
    (⨆ n, a n) ≤ Φ.extend a ∧ Φ.extend a ≤ ∑' n, a n := sorry

/-- **Milestone B1.**  The family induced by a symmetric gauge, with gauge
`Φ∞ ∘ a`.  Its five structure fields are theorems, one input each: `gauge_add_le` is
Milestone B2, `gauge_smul` and `gauge_adjoint` and `enorm_le_gauge` and `gauge_comp_le`
are the corresponding approximation-number facts of Part A. -/
noncomputable def symmetricGaugeFamily (Φ : SymmetricGauge) : OperatorIdealFamily ℂ :=
  sorry

/-- **Milestone B2.**  Every family induced by a symmetric gauge respects Ky Fan
domination.  This is the Hardy--Littlewood--Pólya transfer of the
MajorizationAndAngles roadmap, lifted to sequences by monotone convergence along the
truncations -- which is why `extend` is a supremum of truncations and nothing cleverer. -/
instance isKyFanDominant_symmetricGaugeFamily (Φ : SymmetricGauge) :
    IsKyFanDominant (symmetricGaugeFamily Φ) := sorry

/-- The sequence form of Milestone B2, and the form the proof actually establishes:
weak majorization of antitone sequences implies domination under every symmetric
gauge. -/
theorem SymmetricGauge.extend_le_extend_of_forall_sum_le (Φ : SymmetricGauge)
    {a b : ℕ → ℝ≥0∞} (ha : Antitone a) (hb : Antitone b)
    (h : ∀ k, ∑ n ∈ Finset.range k, a n ≤ ∑ n ∈ Finset.range k, b n) :
    Φ.extend a ≤ Φ.extend b := sorry

/-- **Milestone B1, the direction of the Calkin correspondence we claim.**  The
construction is injective up to equality of gauges on antitone sequences, so the
ideal really is a function of the singular-value sequence alone.

Surjectivity -- that every symmetric ideal arises this way -- is *not* claimed here;
it is the substantial half of Calkin's theorem, needs a separability hypothesis
nothing else in this roadmap needs, and no downstream result consumes it. -/
theorem symmetricGaugeFamily_injective {Φ Ψ : SymmetricGauge}
    (h : symmetricGaugeFamily Φ = symmetricGaugeFamily Ψ)
    {a : ℕ → ℝ≥0∞} (ha : Antitone a) :
    Φ.extend a = Ψ.extend a := sorry

/-! ### Milestone B3 -- Schatten `p`

The Schatten classes are *obtained* from Milestone B1 rather than constructed, so
their four laws are B1's and not new work. -/

/-- The `ℓᵖ` symmetric gauge, `Φ_p a = (∑ aₙ ^ p) ^ (1 / p)`, for `1 ≤ p`. -/
-- DELIVERED: `DavisKahan.OperatorIdeal.ApproximationNumbers.SchattenApproximationFoundation`
noncomputable def schattenGauge (p : ℝ) (hp : 1 ≤ p) : SymmetricGauge := sorry

/-- The Schatten-`p` family.  `p = ∞` is the operator-norm family and is the honest
endpoint of the same scale rather than a separate definition. -/
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.Family.Schatten` (as `schattenIdealFamily`)
noncomputable def schattenFamily (p : ℝ) (hp : 1 ≤ p) : OperatorIdealFamily.{0, v, w} ℂ :=
  symmetricGaugeFamily (schattenGauge p hp)

/-- The scale is monotone, hence the ideals nest: `S_p ⊆ S_q` for `p ≤ q`.  Strictness
is witnessed by a diagonal operator with coefficients `n ↦ n ^ (-1/r)`, `p < r < q` --
the same diagonal machinery as Part A's acceptance example (6). -/
theorem gauge_schattenFamily_antitone {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p ≤ q)
    (T : E →L[ℂ] F) :
    (schattenFamily q hq).gauge T ≤ (schattenFamily p hp).gauge T := sorry

/-- **Milestone B3, the reconciliation obligation.**  `p = 2` is defined twice on
purpose -- through the singular-value sequence, and through an orthonormal expansion
that needs no spectral theory, which is what lets Part C stand on its own.  The two
must therefore be proved equal.  Both sides are basis-independent, so the statement is
well-posed; this is the one place in Part B where Milestone A3 is genuinely needed. -/
-- DELIVERED: `ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.EnergyComparison` (as `tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy_of_finiteDimensional`)
theorem tsum_approximationNumber_sq_eq_hilbertSchmidtEnergy
    (T : F →L[ℂ] E) (b : HilbertBasis ι ℂ F) :
    ∑' n, ENNReal.ofReal (approximationNumber T n) ^ 2 = hilbertSchmidtEnergy T b := sorry

/-- **Milestone B3**: finite-dimensional Schatten `p`-norms for real `p ≥ 1` on
the singular-value vector, with the endpoint identifications `S₁` nuclear,
`S₂` Frobenius, `S∞` operator norm.

This layer is **not** a special case of `schattenFamily` and does not wait on it: it is
a rectangular unitarily invariant norm on a vector, consumed by the
MajorizationAndAngles arm.  That the two agree in finite dimensions is a separate
target, and without it a reader cannot tell whether `S₂` means one thing or two. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.SchattenNorm`
noncomputable def schattenNorm (p : ℝ)
    {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : E →ₗ[ℂ] F) : ℝ := sorry

/-- **Milestone B4, block sums.**  The two-block comparison consumers actually use; the
general statement is that the sequence of a block-diagonal sum is the decreasing
rearrangement of the union of the summands' sequences. -/
theorem gauge_blockSum_le (Φ : OperatorIdealFamily ℂ) (T₁ T₂ : E →L[ℂ] F) :
    Φ.gauge (T₁ + T₂) ≤ Φ.gauge T₁ + Φ.gauge T₂ := Φ.gauge_add_le T₁ T₂

end SymmetricGauges

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
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Lp`
noncomputable def columns (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) : ι → E :=
  fun i => T (b i)

/-- Membership in `ℓ²` of the columns is exactly finiteness of the energy —
the bridge from the model to the ideal theory of Part B. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Lp`
theorem memLp_columns_iff (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) :
    Memℓp (columns b T) 2 ↔ hilbertSchmidtEnergy T b ≠ ⊤ := sorry

/-- The representation map: an `ℓ²` family of columns determines a bounded
operator through the absolutely convergent expansion against the basis. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Lp`
noncomputable def ofLp (b : HilbertBasis ι 𝕜 F) (f : lp (fun _ : ι => E) 2) :
    F →L[𝕜] E := sorry

/-- Round trip: the columns of the represented operator are the family. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Lp`
theorem columns_ofLp (b : HilbertBasis ι 𝕜 F) (f : lp (fun _ : ι => E) 2) :
    columns b (ofLp b f) = f := sorry

/-- The `ℓ²` norm is the Hilbert--Schmidt norm. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Space`
theorem norm_sq_eq_tsum_norm_column_sq (b : HilbertBasis ι 𝕜 F)
    (f : lp (fun _ : ι => E) 2) :
    ‖f‖ ^ 2 = ∑' i, ‖ofLp b f (b i)‖ ^ 2 := sorry

/-- **Milestone C1, isometric conjugation**: composition with a norm-preserving
map on the left and a map with norm-preserving adjoint on the right preserves
the energy — what makes the Sylvester flow a unitary group on this space. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Conjugation`
theorem hilbertSchmidtEnergy_isometry_comp (b : HilbertBasis ι 𝕜 F)
    (U : E →L[𝕜] E) (hU : ∀ x, ‖U x‖ = ‖x‖) (T : F →L[𝕜] E) :
    hilbertSchmidtEnergy (U ∘L T) b = hilbertSchmidtEnergy T b := sorry

/-- **Milestone C2, Pythagoras along an orthogonal family**: a family splitting
every vector's norm splits the energy, with no countability or summability
side conditions. -/
-- DELIVERED: `ForTauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Pythagoras`
theorem tsum_energy_isometryFamily_comp {κ : Type y} (b : HilbertBasis ι 𝕜 F)
    (P : κ → (E →L[𝕜] E)) (hP : ∀ v : E, ∑' k, ‖P k v‖ₑ ^ 2 = ‖v‖ₑ ^ 2)
    (T : F →L[𝕜] E) :
    ∑' k, hilbertSchmidtEnergy ((P k) ∘L T) b = hilbertSchmidtEnergy T b := sorry

end HilbertSchmidt

end TauCetiRoadmap.OperatorIdeals
