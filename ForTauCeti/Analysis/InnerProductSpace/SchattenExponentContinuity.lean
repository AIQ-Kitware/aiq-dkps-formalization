/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6.1 Sol
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.SchattenContinuity
public import Mathlib.Topology.Order.Compact

/-!
# Continuity in the finite Schatten exponent

The finite singular-value power sum is jointly continuous in the operator
and every positive real exponent, including when singular values vanish.
On a fixed compact operator set its minimum is consequently continuous
in the exponent. At finite exponents at least one these are the accepted
Schatten powers, rather than a second norm definition.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The literal finite singular-value power sum. Positive exponents below
one are allowed; no norm structure is asserted there. -/
@[expose] def singularValuePowerSum [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (q : ℝ) (A : E →L[𝕜] F) : ℝ :=
  ∑ i : Fin (Module.finrank 𝕜 E), (A.singularValue i : ℝ) ^ q

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- The positive-exponent spectral power sum is jointly continuous,
including rank changes and zero singular values. -/
theorem continuous_singularValuePowerSum_positive :
    Continuous (fun x : {q : ℝ // 0 < q} × (E →L[𝕜] F) =>
      singularValuePowerSum x.1.val x.2) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (Real.continuousAt_rpow_of_pos
    ((x.2.singularValue i : ℝ), x.1.val) x.1.property).comp₂
    ((NNReal.continuous_coe.comp (ContinuousLinearMap.continuous_singularValue i)).comp
      continuous_snd).continuousAt
    (continuous_subtype_val.comp continuous_fst).continuousAt

/-- Identification with the accepted finite Schatten power. -/
theorem singularValuePowerSum_eq_schatten_rpow
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (A : E →L[𝕜] F) :
    singularValuePowerSum p.toReal A =
      UnitarilyInvariantSeminorm.schatten 𝕜 E F p A.toLinearMap ^ p.toReal :=
  (schatten_rpow_eq_sum_singularValue p hp A).symm

/-- The spectral-power minimum on a fixed operator set. Compactness is
an explicit hypothesis of its continuity and attainment theorems. -/
@[expose] def singularValuePowerMinimum (q : ℝ) (S : Set (E →L[𝕜] F)) : ℝ :=
  sInf (singularValuePowerSum q '' S)

/-- Minima of finite spectral power sums on a fixed compact operator set
vary continuously with every positive exponent. The empty set is allowed
for continuity; attainment below explicitly requires nonemptiness. -/
theorem continuousOn_singularValuePowerMinimum
    {S : Set (E →L[𝕜] F)} (hS : IsCompact S) :
    ContinuousOn (fun q => singularValuePowerMinimum q S) (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact hS.continuous_sInf continuous_singularValuePowerSum_positive

/-- A global minimum on the compact carrier computes the power infimum. -/
theorem singularValuePowerMinimum_eq_of_isMinOn
    (q : ℝ) {S : Set (E →L[𝕜] F)} {A : E →L[𝕜] F} (hA : A ∈ S)
    (hmin : IsMinOn (singularValuePowerSum q) S A) :
    singularValuePowerMinimum q S = singularValuePowerSum q A := by
  apply IsLeast.csInf_eq
  refine ⟨Set.mem_image_of_mem _ hA, ?_⟩
  rintro _ ⟨B, hB, rfl⟩
  exact hmin hB

/-- Every positive-exponent minimum on a nonempty compact operator set
is attained. This includes the nuclear exponent and nonconvex powers. -/
theorem exists_attains_singularValuePowerMinimum
    (q : ℝ) (hq : 0 < q) {S : Set (E →L[𝕜] F)}
    (hS : IsCompact S) (hne : S.Nonempty) :
    ∃ A ∈ S, singularValuePowerMinimum q S = singularValuePowerSum q A ∧
      IsMinOn (singularValuePowerSum q) S A := by
  have hcont : Continuous (singularValuePowerSum q : (E →L[𝕜] F) → ℝ) :=
    continuous_singularValuePowerSum_positive.comp
      ((continuous_const (y := (⟨q, hq⟩ : {q : ℝ // 0 < q}))).prodMk continuous_id)
  obtain ⟨A, hA, hmin⟩ := hS.exists_isMinOn hne hcont.continuousOn
  exact ⟨A, hA, singularValuePowerMinimum_eq_of_isMinOn q hA hmin, hmin⟩

/-- The graph of global spectral-power minimizers over any fixed closed
operator set is closed. Compactness is not needed: every comparison with
a fixed feasible operator passes to the limit by joint continuity. -/
theorem isClosed_singularValuePower_minimizers
    {S : Set (E →L[𝕜] F)} (hS : IsClosed S) :
    IsClosed {x : {q : ℝ // 0 < q} × (E →L[𝕜] F) |
      x.2 ∈ S ∧ IsMinOn (singularValuePowerSum x.1.val) S x.2} := by
  have hcmp (B : E →L[𝕜] F) :
      IsClosed {x : {q : ℝ // 0 < q} × (E →L[𝕜] F) |
        singularValuePowerSum x.1.val x.2 ≤ singularValuePowerSum x.1.val B} :=
    isClosed_le continuous_singularValuePowerSum_positive
      (continuous_singularValuePowerSum_positive.comp
        (continuous_fst.prodMk continuous_const))
  have heq : {x : {q : ℝ // 0 < q} × (E →L[𝕜] F) |
      x.2 ∈ S ∧ IsMinOn (singularValuePowerSum x.1.val) S x.2} =
      (Prod.snd ⁻¹' S) ∩ ⋂ B ∈ S,
        {x | singularValuePowerSum x.1.val x.2 ≤ singularValuePowerSum x.1.val B} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_iInter, isMinOn_iff]
  rw [heq]
  exact (hS.preimage continuous_snd).inter
    (isClosed_iInter fun B => isClosed_iInter fun _ => hcmp B)

/-- A convergent family of positive-exponent global minimizers has a
feasible globally minimizing limit on a fixed closed operator set.
This includes convergence to exponent one and vanishing singular values. -/
theorem isMinOn_singularValuePowerSum_of_tendsto
    {α : Type*} {l : Filter α} [l.NeBot] {S : Set (E →L[𝕜] F)} (hS : IsClosed S)
    (q : α → {q : ℝ // 0 < q}) (A : α → E →L[𝕜] F)
    {q₀ : {q : ℝ // 0 < q}} {A₀ : E →L[𝕜] F}
    (hq : Filter.Tendsto q l (nhds q₀)) (hA : Filter.Tendsto A l (nhds A₀))
    (hmin : ∀ᶠ i in l, A i ∈ S ∧ IsMinOn (singularValuePowerSum (q i).val) S (A i)) :
    A₀ ∈ S ∧ IsMinOn (singularValuePowerSum q₀.val) S A₀ :=
  (isClosed_singularValuePower_minimizers hS).mem_of_tendsto
    (hq.prodMk_nhds hA) hmin

end TauCeti
