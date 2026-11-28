/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

module

public import ForTauCeti.Analysis.InnerProductSpace.Complexification.Basic

/-! # Operators preserving the real copy of a complexification

Restricting such an operator to real vectors and taking real coordinates
recovers the real operator. Preservation of the real copy is closed under
operator-norm convergence.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open Filter Topology
open TauCeti.RealComplexification

noncomputable section

universe v

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

local notation "Eℂ" => RealComplexification E
local notation "Fℂ" => RealComplexification F

/-- A complex operator maps the distinguished real copy into the real copy. -/
def MapsRealCopy (T : Eℂ →L[ℂ] Fℂ) : Prop :=
  ∀ x : E, im (T (ofReal x)) = 0

omit [CompleteSpace E] [CompleteSpace F] in
/-- Every coordinatewise complexification maps real vectors to real vectors. -/
theorem mapsRealCopy_complexify (T : E →L[ℝ] F) :
    MapsRealCopy (complexify T) := by
  intro x
  simp

omit [CompleteSpace F] in
/-- A vector with zero imaginary coordinate is its real-coordinate embedding. -/
theorem eq_ofReal_re_of_im_eq_zero
    (z : Fℂ) (hz : im z = 0) : ofReal (re z) = z := by
  apply RealComplexification.ext
  · simp
  · simp [hz]

omit [CompleteSpace E] [CompleteSpace F] in
/-- A complex-linear operator that preserves the real copy is exactly the
complexification of its real restriction. -/
theorem complexify_realPartOperator_eq
    (T : Eℂ →L[ℂ] Fℂ) (hT : MapsRealCopy T) :
    complexify (realPartOperator T) = T := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = ofReal (re z) + Complex.I • ofReal (im z) := by
    apply RealComplexification.ext <;> simp
  have hreal : ∀ x : E,
      ofReal (realPartOperator T x) = T (ofReal x) := by
    intro x
    exact eq_ofReal_re_of_im_eq_zero (T (ofReal x)) (hT x)
  rw [hz]
  simp only [map_add, map_smul, complexify_ofReal, hreal]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Convergence in operator norm preserves the property of mapping the real
copy into itself. -/
theorem mapsRealCopy_of_tendsto
    (T : ℕ → Eℂ →L[ℂ] Fℂ) (L : Eℂ →L[ℂ] Fℂ)
    (hT : ∀ n, MapsRealCopy (T n))
    (hlim : Tendsto T atTop (𝓝 L)) :
    MapsRealCopy L := by
  intro x
  let ev : (Eℂ →L[ℂ] Fℂ) →L[ℂ] Fℂ :=
    ContinuousLinearMap.apply ℂ Fℂ (ofReal x)
  have happly : Tendsto (fun n => T n (ofReal x)) atTop
      (𝓝 (L (ofReal x))) :=
    ev.continuous.continuousAt.tendsto.comp hlim
  have hcontIm : Continuous (im : Fℂ → F) :=
    continuous_snd.comp (WithLp.homeomorphProd 2 F F).continuous
  have him : Tendsto (fun n => im (T n (ofReal x))) atTop
      (𝓝 (im (L (ofReal x)))) :=
    hcontIm.continuousAt.tendsto.comp happly
  have hzero : Tendsto (fun _ : ℕ => (0 : F)) atTop (𝓝 0) :=
    tendsto_const_nhds
  have hseq : (fun n => im (T n (ofReal x))) = fun _ : ℕ => (0 : F) := by
    funext n
    exact hT n x
  have himzero : Tendsto (fun n => im (T n (ofReal x))) atTop (𝓝 0) := by
    rw [hseq]
    exact hzero
  exact tendsto_nhds_unique him himzero

end

end ExactSinTheta
end DavisKahan
end TauCeti
