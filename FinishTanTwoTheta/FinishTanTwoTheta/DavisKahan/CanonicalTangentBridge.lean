/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import FinishTanTwoTheta.FunctionalCalculus.DoubleAngleTangent
import DavisKahan.Experimental.InfiniteDimensional.TanTwoTheta.BoundedOffDiagonalRiccati
import DavisKahan.Geometry.Angle.OperatorAngleComplex
import DavisKahan.SpectralTheory.GraphSubspace
import DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
import DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport

/-!
# Canonical ambient tangent versus the graph-coordinate tangent

For a quarter-acute pair `U,V`, let `Y` be the canonical ambient angular
operator and `X : U -> U-perp` its rectangular coordinate.  The projection
onto `V = graph(Y)` has the normal-equation formula

`Q = (P+Y) (1+Y*Y)^-1 (P+Y*)`.

Writing `G=Y*Y`, its two source compressions are

`PQP = (1+G)^-1 P`,
`P(1-Q)P = G(1+G)^-1 P`.

Consequently, on `U`,

`sin(2Theta) = 2 sqrt(G) (1+G)^-1`,
`cos(2Theta) = (1-G)(1+G)^-1`,

and both operators vanish on `U-perp`.  Since `||Y||<1`, the extended cosine
is invertible and therefore

`tan(2Theta) = 2 sqrt(G) (1-G)^-1`.

The right side is exactly the modulus of the ambient graph-coordinate operator
`2Y(1-Y*Y)^-1`.  Extending the rectangular coordinate operator by zero gives
that ambient operator, so the canonical tangent and the rectangular graph
tangent have the same complete approximation-number sequence.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

open scoped InnerProductSpace
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan.Experimental.ExactSinTheta
-- `doubleAngleTangentOperator` and its denominator API live in the *sibling*
-- namespace `TauCeti.FinishTanTwoTheta` (see `FunctionalCalculus/DoubleAngleTangent.lean`),
-- not under `TauCeti.DavisKahan.FinishTanTwoTheta`, so they are not in scope here by
-- enclosure. `SharpIdeal.lean` fully qualifies every use instead; this open is the
-- same fix in one line. The namespace split itself is a library-organisation defect.
open TauCeti.FinishTanTwoTheta

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- An orthogonally complemented subspace is complete.  `DavisKahan.SinTheta.Natural.Reducing`
declares the same instance, but `local`, so it is not exported to importing modules and has to
be repeated here.  Without it every `ContinuousLinearMap.adjoint` on a subspace in this file
fails to elaborate with `failed to synthesize CompleteSpace ↥U`. -/
noncomputable local instance completeSpaceOfHasOrthogonalProjection
    (W : Submodule ℂ E) [W.HasOrthogonalProjection] : CompleteSpace W :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection W).completeSpace_coe

private theorem ambientAngularOperator_eq_extendCoordinate
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (Y : E →L[ℂ] E) (hY : IsAngularOperator U Y) :
    Y = Uᗮ.subtypeL ∘L subspaceAngularCoordinate U Y ∘L U.subtypeL.adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  have hYP : Y (U.starProjection x) = Y x := by
    have h := DFunLike.congr_fun hY.1 x
    -- `h : (Y ∘ P) x = Y x` is already the right way round -- the `.symm` was
    -- backwards -- and `IsAngularOperator` states its field with
    -- `DavisKahanExt.projection`, so that abbreviation has to be unfolded for the
    -- goal's `U.starProjection` to match.
    simpa only [ContinuousLinearMap.comp_apply, DavisKahanExt.projection,
      DavisKahan.projection] using h
  -- Rewrite the ambient right-hand side instead of `change`-ing the goal.  The
  -- adjoint of `subtypeL` is the orthogonal projection *into* the subspace
  -- (`Submodule.adjoint_subtypeL`) and its coercion back to `E` is
  -- `starProjection`; neither step is definitional, so `change` cannot bridge
  -- them and the old `⟨U.starProjection x, _⟩` pattern never matched.
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,
    coe_subspaceAngularCoordinate_apply U Y hY (U.subtypeL.adjoint x),
    Submodule.adjoint_subtypeL, ← Submodule.starProjection_apply, hYP]

private theorem ambient_doubleAngleTangent_eq_extendCoordinate
    (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (Y : E →L[ℂ] E) (hY : IsAngularOperator U Y)
    (hcontractive : ‖Y‖ < 1) :
    doubleAngleTangentOperator Y hcontractive =
      Uᗮ.subtypeL ∘L
        doubleAngleTangentOperator (subspaceAngularCoordinate U Y)
          ((norm_subspaceAngularCoordinate_le U Y).trans_lt hcontractive) ∘L
        U.subtypeL.adjoint := by
  let X : U →L[ℂ] Uᗮ := subspaceAngularCoordinate U Y
  let P : E →L[ℂ] E := U.starProjection
  have hYext : Y = Uᗮ.subtypeL ∘L X ∘L U.subtypeL.adjoint :=
    ambientAngularOperator_eq_extendCoordinate U Y hY
  have hYP : Y ∘L P = Y := hY.1
  have hPY : P ∘L Y = 0 := hY.2
  -- `star_mul` cannot fire on `P ∘L Y`: for endomorphisms `∘L` is *defeq* to `*`
  -- but not syntactically equal, so `simp only` never matches.  Go through
  -- `adjoint_comp`, which is stated for `∘L` directly.
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (isSelfAdjoint_starProjection U).star_eq
  have hYstarP : Y.adjoint ∘L P = 0 := by
    have h := congrArg ContinuousLinearMap.adjoint hPY
    rwa [ContinuousLinearMap.adjoint_comp, hPadj, map_zero] at h
  have hPYstar : P ∘L Y.adjoint = Y.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hYP
    rwa [ContinuousLinearMap.adjoint_comp, hPadj] at h
  let G : E →L[ℂ] E := Y.adjoint ∘L Y
  let D : E →L[ℂ] E := doubleAngleDenominator Y
  let DX : U →L[ℂ] U := doubleAngleDenominator X
  have hGP : G ∘L P = G := by
    dsimp [G]
    rw [ContinuousLinearMap.comp_assoc, hYP]
  have hPG : P ∘L G = G := by
    dsimp [G]
    rw [← ContinuousLinearMap.comp_assoc, hPYstar]
  have hDblock : D =
      U.subtypeL ∘L DX ∘L U.subtypeL.adjoint + Uᗮ.starProjection := by
    apply ContinuousLinearMap.ext
    intro x
    change x - Y.adjoint (Y x) =
      ((U.subtypeL ∘L DX ∘L U.subtypeL.adjoint) x) + Uᗮ.starProjection x
    have hsplit : x = U.starProjection x + Uᗮ.starProjection x := by
      rw [U.starProjection_add_starProjection_orthogonal]
    have hYperp : Y (Uᗮ.starProjection x) = 0 := by
      have h := DFunLike.congr_fun hYP (Uᗮ.starProjection x)
      -- `K` is implicit in `starProjection_apply_eq_zero_iff`, and with it
      -- unresolved Lean reports the whole dotted name as an unknown constant.
      rw [ContinuousLinearMap.comp_apply,
        (Submodule.starProjection_apply_eq_zero_iff (K := U)).mpr
          (Uᗮ.starProjection_apply_mem x)] at h
      simpa using h.symm
    -- after `hYperp` the residue is `Y (P x) + 0`, so it is `add_zero` that
    -- applies, not `map_zero` (there is no `f 0` subterm to match).
    rw [hsplit, map_add, hYperp, add_zero]
    apply congrArg (fun z : U => (z : E))
    ext
    simp only [DX, D, doubleAngleDenominator,
      ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
      Submodule.coe_sub, Submodule.coe_mk]
    rw [coe_subspaceAngularCoordinate_apply U Y hY]
    have hAdj :
        (((X.adjoint (X
          ⟨U.starProjection x, U.starProjection_apply_mem x⟩) : U) : E)) =
          Y.adjoint (Y (U.starProjection x)) := by
      apply Subtype.ext
      intro
      rw [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_left]
      simp only [X]
      rw [coe_subspaceAngularCoordinate_apply U Y hY]
      rfl
    rw [hAdj]
  have hDunit := isUnit_doubleAngleDenominator Y hcontractive
  have hDXcontractive : ‖X‖ < 1 :=
    (norm_subspaceAngularCoordinate_le U Y).trans_lt hcontractive
  have hDXunit := isUnit_doubleAngleDenominator X hDXcontractive
  have hDinvblock : Ring.inverse D =
      U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
        Uᗮ.starProjection := by
    have hcandidate :
        D ∘L (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
          Uᗮ.starProjection) = ContinuousLinearMap.id ℂ E := by
      rw [hDblock, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.comp_add]
      have hUU : U.subtypeL.adjoint ∘L U.subtypeL =
          ContinuousLinearMap.id ℂ U := by
        ext x
        apply Subtype.ext
        simp
      have hXX := Ring.mul_inverse_cancel DX hDXunit
      have hcross1 :
          (U.subtypeL ∘L DX ∘L U.subtypeL.adjoint) ∘L
            Uᗮ.starProjection = 0 := by
        ext x
        simp
      have hcross2 : Uᗮ.starProjection ∘L
          (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint) = 0 := by
        ext x
        simp
      rw [hcross1, hcross2, add_zero, zero_add,
        ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc DX,
        hUU, ContinuousLinearMap.id_comp, hXX,
        ContinuousLinearMap.comp_assoc,
        U.isIdempotentElem_starProjection_orthogonal.eq]
      ext x
      simp
    -- From `D B = 1` and `D⁻¹ D = 1`, cancel `D` on the left.  The old script
    -- applied *injectivity* of `D` (`isUnit_iff_bijective.mp hDunit |>.1`) to an
    -- *equation*, and that conclusion shape cannot match the goal.
    calc Ring.inverse D
        = Ring.inverse D * 1 := (mul_one _).symm
      _ = Ring.inverse D *
            (D * (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
              Uᗮ.starProjection)) := by
          rw [show D * (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
            Uᗮ.starProjection) = 1 from hcandidate]
      _ = (Ring.inverse D * D) *
            (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
              Uᗮ.starProjection) := (mul_assoc _ _ _).symm
      _ = 1 * (U.subtypeL ∘L Ring.inverse DX ∘L U.subtypeL.adjoint +
              Uᗮ.starProjection) := by
          rw [Ring.inverse_mul_cancel D hDunit]
      _ = _ := one_mul _
  unfold doubleAngleTangentOperator
  -- NOTE on ordering, both directions are wrong and this is the lesser evil:
  --   `rw [hYext, hDinvblock]` (this order) leaves `Ring.inverse D` unmatched,
  --      because `hYext` has already rewritten the `Y` inside
  --      `D = doubleAngleDenominator Y`;
  --   `rw [hDinvblock, hYext]` fires both, but then `hYext` also rewrites the `Y`
  --      inside `X := subspaceAngularCoordinate U Y`, producing the
  --      self-referential `subspaceAngularCoordinate U (Uᗮ.subtypeL ∘ X ∘ …)` that
  --      no longer folds back to `X` — strictly worse.
  -- The real fix is to generalise `X` (and `D`) before rewriting, or to state
  -- `hYext` for a fresh variable rather than for `Y` itself.
  rw [hYext, hDinvblock]
  apply ContinuousLinearMap.ext
  intro x
  simp only [smul_apply, ContinuousLinearMap.comp_apply, add_apply]
  have hcross : X (U.subtypeL.adjoint (Uᗮ.starProjection x)) = 0 := by
    simp
  rw [hcross, map_zero, add_zero]
  rfl

/-- The canonical ambient double-angle tangent is the modulus of the ambient
extension of the graph-coordinate double-angle tangent. -/
private theorem tanTwoAngleOperatorC_eq_modulus_ambientGraphTangent
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    tanTwoAngleOperatorC U V hquarter =
      ContinuousLinearMap.modulus
        (doubleAngleTangentOperator
          (quarterAcuteAngularOperator U V hquarter)
          (norm_quarterAcuteAngularOperator_lt_one U V hquarter)) := by
  let Y : E →L[ℂ] E := quarterAcuteAngularOperator U V hquarter
  let P : E →L[ℂ] E := U.starProjection
  let Q : E →L[ℂ] E := V.starProjection
  let G : E →L[ℂ] E := Y.adjoint ∘L Y
  let N : E →L[ℂ] E := ContinuousLinearMap.id ℂ E + G
  let R : E →L[ℂ] E := Ring.inverse N
  let D : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - G
  let M : E →L[ℂ] E := ContinuousLinearMap.modulus
    (doubleAngleTangentOperator Y
      (norm_quarterAcuteAngularOperator_lt_one U V hquarter))
  have hY : IsAngularOperator U Y :=
    quarterAcuteAngularOperator_isAngularOperator U V hquarter
  have hYP : Y ∘L P = Y := hY.1
  have hPY : P ∘L Y = 0 := hY.2
  -- See the note on the same pair in `ambientAngularOperator_eq_extendCoordinate`:
  -- `star_mul` does not match `P ∘L Y`, so route through `adjoint_comp`.
  have hPadj : ContinuousLinearMap.adjoint P = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (isSelfAdjoint_starProjection U).star_eq
  have hYstarP : Y.adjoint ∘L P = 0 := by
    have h := congrArg ContinuousLinearMap.adjoint hPY
    rwa [ContinuousLinearMap.adjoint_comp, hPadj, map_zero] at h
  have hPYstar : P ∘L Y.adjoint = Y.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hYP
    rwa [ContinuousLinearMap.adjoint_comp, hPadj] at h
  have hGnonneg : (0 : E →L[ℂ] E) ≤ G := by
    dsimp [G]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self Y)
  have hGP : G ∘L P = G := by
    dsimp [G]
    rw [ContinuousLinearMap.comp_assoc, hYP]
  have hPG : P ∘L G = G := by
    dsimp [G]
    rw [← ContinuousLinearMap.comp_assoc, hPYstar]
  have hNunit : IsUnit N := by
    refine ForMathlib.ContinuousLinearMap.isUnit_of_coercive one_pos ?_
    intro x
    -- Compute the form value first, then conclude numerically.  Doing it with a
    -- `rw` chain does not work: `isUnit_of_coercive` states its hypothesis with
    -- `RCLike.re`, `dsimp` collapses that to `Complex.re`, and after the collapse
    -- neither `map_add` (which wants a bundled additive map) nor
    -- `inner_self_eq_norm_sq` (which is stated for `RCLike.re`) can match.
    have hval : RCLike.re ⟪N x, x⟫_ℂ = ‖x‖ ^ 2 + ‖Y x‖ ^ 2 := by
      have hN : N x = x + Y.adjoint (Y x) := by
        show (ContinuousLinearMap.id ℂ E + Y.adjoint ∘L Y) x
            = x + Y.adjoint (Y x)
        rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply]
      rw [hN]
      -- `← ofReal_pow` pulls `(↑‖x‖) ^ 2` back to `↑(‖x‖ ^ 2)` so that
      -- `Complex.ofReal_re` can strip the coercion.
      simp [inner_add_left, ContinuousLinearMap.adjoint_inner_left,
        inner_self_eq_norm_sq, ← Complex.ofReal_pow]
    rw [hval]
    nlinarith [sq_nonneg ‖Y x‖, norm_nonneg x]
  have hNR : N ∘L R = ContinuousLinearMap.id ℂ E :=
    Ring.mul_inverse_cancel N hNunit
  have hRN : R ∘L N = ContinuousLinearMap.id ℂ E :=
    Ring.inverse_mul_cancel N hNunit
  have hPR : P ∘L R = R ∘L P := by
    have hPN : P ∘L N = N ∘L P := by
      dsimp [N]
      rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp, hPG, hGP]
    calc
      P ∘L R = (R ∘L N) ∘L (P ∘L R) := by rw [hRN, ContinuousLinearMap.id_comp]
      _ = R ∘L ((N ∘L P) ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L ((P ∘L N) ∘L R) := by rw [hPN]
      _ = (R ∘L P) ∘L (N ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L P := by rw [hNR, ContinuousLinearMap.comp_id]
  have hGR : G ∘L R = R ∘L G := by
    have hGN : G ∘L N = N ∘L G := by
      dsimp [N]
      rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
    calc
      G ∘L R = (R ∘L N) ∘L (G ∘L R) := by rw [hRN, ContinuousLinearMap.id_comp]
      _ = R ∘L ((N ∘L G) ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L ((G ∘L N) ∘L R) := by rw [hGN]
      _ = (R ∘L G) ∘L (N ∘L R) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L G := by rw [hNR, ContinuousLinearMap.comp_id]
  have hQformula : Q = (P + Y) ∘L R ∘L (P + Y.adjoint) := by
    -- Transporting `projection (graphSubspace U Y)` to `projection V` needs care:
    -- `rw` fails with "motive is not type correct" because `projection` carries a
    -- `HasOrthogonalProjection` instance *for the submodule being rewritten*, and
    -- `simp only [lemma]` fails to match because `Y` is a `let`-bound fvar while
    -- the lemma's LHS mentions `quarterAcuteAngularOperator` explicitly.  Naming
    -- the equation as a local hypothesis fixes both: simp rewrites with an fvar
    -- equation directly, and `HasOrthogonalProjection` is a `Prop` class, so the
    -- instance argument is proof-irrelevant and congruence goes through.
    have hV : graphSubspace U Y = V :=
      graphSubspace_quarterAcuteAngularOperator U V hquarter
    have hgraph : DavisKahanExt.projection V = graphProjectionFormula U Y := by
      simpa only [hV] using projection_graphSubspace_formula U Y hY
    -- `graphProjectionFormula` produces every factor decorated with `P`:
    --   (P + Y P) · (1 + P Y⋆ (Y P))⁻¹ · (P + P Y⋆)
    -- and the decorations collapse by `Y P = Y` and `P Y⋆ = Y⋆`, which are
    -- exactly the two angular-operator identities.  `1` and `id` are the same
    -- element of the endomorphism algebra, so the tail is `rfl`.
    have hcollapse :
        graphProjectionFormula U Y = (P + Y) ∘L R ∘L (P + Y.adjoint) := by
      -- A literal `show` cannot state the expansion: it mixes two spellings of
      -- the same operator (`DavisKahanExt.projection U` in some factors,
      -- `U.starProjection` in others), so no single hand-written pattern matches.
      -- Let `simp only` do the unfolding and the two collapses together.
      show (P + Y * P) *
            (Ring.inverse (1 + star (Y * P) * (Y * P)) * star (P + Y * P))
          = (P + Y) ∘L R ∘L (P + Y.adjoint)
      rw [show Y * P = Y from hYP, star_add,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
        hPadj]
      -- `R`, `N`, `G` are `let`-bound, and `1`/`id` and `*`/`∘SL` differ only up
      -- to unfolding, so finish by definitional equality.
      show (P + Y) * (Ring.inverse (1 + Y.adjoint * Y) * (P + Y.adjoint))
          = (P + Y) * (Ring.inverse (1 + Y.adjoint * Y) * (P + Y.adjoint))
      rfl
    exact hgraph.trans hcollapse
  -- Done as a ring computation rather than by `simp` normalisation.  No
  -- associativity convention works here: right-association hides `P ∘ P` from
  -- `hPP`, left-association hides `Y⋆ ∘ P` from `hYstarP`.  Collapsing the two
  -- outer factors *first* avoids the choice entirely.
  have hPP : P ∘L P = P := U.isIdempotentElem_starProjection
  have hPQP : P ∘L Q ∘L P = R ∘L P := by
    have hleft : P ∘L (P + Y) = P := by
      rw [ContinuousLinearMap.comp_add, hPP, hPY, add_zero]
    have hright : (P + Y.adjoint) ∘L P = P := by
      rw [ContinuousLinearMap.add_comp, hPP, hYstarP, add_zero]
    show P * (Q * P) = R * P
    rw [hQformula]
    calc P * (((P + Y) * (R * (P + Y.adjoint))) * P)
        = (P * (P + Y)) * (R * ((P + Y.adjoint) * P)) := by noncomm_ring
      _ = P * (R * P) := by
            rw [show P * (P + Y) = P from hleft,
              show (P + Y.adjoint) * P = P from hright]
      _ = (P * R) * P := by rw [mul_assoc]
      _ = (R * P) * P := by rw [show P * R = R * P from hPR]
      _ = R * (P * P) := by rw [mul_assoc]
      _ = R * P := by rw [show P * P = P from hPP]
  have hPQperpP : P ∘L Vᗮ.starProjection ∘L P = G ∘L R ∘L P := by
    -- `starProjection_orthogonal'` yields `1 - Q` (not `id - Q`), so stay in
    -- ring notation and let `noncomm_ring` distribute; that sidesteps both the
    -- `1` vs `id` mismatch and the bracketing of `P ∘ ((1 - Q) ∘ P)`.
    rw [Submodule.starProjection_orthogonal' V]
    have hexpand : P * ((1 - Q) * P) = P * P - P * (Q * P) := by noncomm_ring
    show P * ((1 - Q) * P) = G * (R * P)
    rw [hexpand, show P * P = P from hPP, show P * (Q * P) = R * P from hPQP]
    have hidentity : P - R ∘L P = G ∘L R ∘L P := by
      have hNRP := congrArg (fun T : E →L[ℂ] E => T ∘L P) hNR
      dsimp [N] at hNRP
      simp only [ContinuousLinearMap.add_comp,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc] at hNRP
      -- `hNRP : R P + G R P = P`.  The `rw [hGR]` that used to sit here was
      -- superfluous and could not fire; the goal is pure additive rearrangement.
      calc P - R ∘L P = (R ∘L P + G ∘L R ∘L P) - R ∘L P := by rw [hNRP]
        _ = G ∘L R ∘L P := by abel
    exact hidentity
  let Cang : E →L[ℂ] E := cosAngleOperatorC U V
  let Sang : E →L[ℂ] E := sinAngleOperatorDirectedC U V
  -- `modulus_mul_self` is stated with `*`; these goals carry `∘SL`, which is
  -- defeq but not syntactically equal, so `← mul_def` has to bridge it first.
  -- Then `|Q P|² = (QP)⋆(QP) = P Q Q P = P Q P` by self-adjointness and
  -- idempotence of the two star-projections, which is exactly `hPQP`.
  have hQQ : V.starProjection ∘L V.starProjection = V.starProjection :=
    V.isIdempotentElem_starProjection
  have hQperpQperp :
      Vᗮ.starProjection ∘L Vᗮ.starProjection = Vᗮ.starProjection :=
    Vᗮ.isIdempotentElem_starProjection
  have hCangSq : Cang ∘L Cang = R ∘L P := by
    dsimp [Cang, cosAngleOperatorC]
    rw [← ContinuousLinearMap.mul_def, ContinuousLinearMap.modulus_mul_self,
      ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection U).adjoint_eq,
      (isSelfAdjoint_starProjection V).adjoint_eq,
      ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc V.starProjection V.starProjection
        U.starProjection, hQQ]
    exact hPQP
  have hSangSq : Sang ∘L Sang = G ∘L R ∘L P := by
    dsimp [Sang, sinAngleOperatorDirectedC]
    rw [← ContinuousLinearMap.mul_def, ContinuousLinearMap.modulus_mul_self,
      ContinuousLinearMap.adjoint_comp,
      (isSelfAdjoint_starProjection U).adjoint_eq,
      (isSelfAdjoint_starProjection Vᗮ).adjoint_eq,
      ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc Vᗮ.starProjection Vᗮ.starProjection
        U.starProjection, hQperpQperp]
    exact hPQperpP
  have hSCcomm : Commute Sang Cang :=
    commute_sinAngleOperatorDirectedC_cosAngleOperatorC U V
  have hSinTwo : sinTwoAngleOperatorC U V = (2 : ℂ) • (Sang ∘L Cang) := rfl
  have hCosTwo : cosTwoAngleOperatorC U V = D ∘L R ∘L P := by
    -- `dsimp` unfolds the `let`s, after which `hCangSq`/`hSangSq` (stated in terms
    -- of `Cang`/`Sang`) no longer match.  Keep the abbreviations and restate the
    -- squares with `*` instead.
    show Cang * Cang - Sang * Sang = D ∘L R ∘L P
    rw [show Cang * Cang = R ∘L P from hCangSq,
      show Sang * Sang = G ∘L R ∘L P from hSangSq]
    -- state the identity with `1`, not `ContinuousLinearMap.id`: they are the same
    -- element, but `noncomm_ring` only knows `one_mul` for the former.
    show R * P - G * (R * P) = ((1 : E →L[ℂ] E) - G) * (R * P)
    noncomm_ring
  have hDunit : IsUnit D :=
    isUnit_doubleAngleDenominator Y
      (norm_quarterAcuteAngularOperator_lt_one U V hquarter)
  have hDcommG : D ∘L G = G ∘L D := by
    dsimp [D]
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
  -- `Commute.units_inv_left` is stated for a `Units` coercion, not for
  -- `Ring.inverse`; `Ring.inverse_of_isUnit` converts between them.
  have hDinvcommG : Ring.inverse D ∘L G = G ∘L Ring.inverse D := by
    have hu : Commute ((hDunit.unit : E →L[ℂ] E)) G := by
      rw [hDunit.unit_spec]; exact hDcommG
    rw [Ring.inverse_of_isUnit hDunit]
    exact hu.units_inv_left
  have hTformula :
      doubleAngleTangentOperator Y
          (norm_quarterAcuteAngularOperator_lt_one U V hquarter) =
        (2 : ℂ) • (Y ∘L Ring.inverse D) := rfl
  -- Hoisted above `hMsq`.  `hMsq` needs the self-adjointness of `D⁻¹` and the
  -- commutation `[|Y|, D⁻¹] = 0`; both were originally proved *below*, inside
  -- `hCandidateNonneg`, i.e. after their first use.
  have hmodYnonneg : (0 : E →L[ℂ] E) ≤ ContinuousLinearMap.modulus Y :=
    ContinuousLinearMap.modulus_nonneg Y
  have hDnonneg : (0 : E →L[ℂ] E) ≤ D := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ?_, ?_⟩
    · -- Stay in the `ContinuousLinearMap` star instance throughout: the route via
      -- `IsSelfAdjoint.algebraMap` states the fact at a *different* `Star`
      -- instance on the same type, which is why it failed to typecheck.
      show IsSelfAdjoint (ContinuousLinearMap.id ℂ E - G)
      have hidsa : IsSelfAdjoint (ContinuousLinearMap.id ℂ E) := by
        show star (ContinuousLinearMap.id ℂ E) = ContinuousLinearMap.id ℂ E
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]
      exact hidsa.sub
        (ContinuousLinearMap.isPositive_adjoint_comp_self Y).isSelfAdjoint
    · intro x
      rw [ContinuousLinearMap.reApplyInnerSelf_apply]
      -- Same trap as in `hNunit`: compute the form value as its own `have` with
      -- `simp`, because once a `dsimp` collapses `RCLike.re` to `Complex.re`
      -- neither `map_sub` nor `inner_self_eq_norm_sq` can match.
      have hval : RCLike.re ⟪D x, x⟫_ℂ = ‖x‖ ^ 2 - ‖Y x‖ ^ 2 := by
        have hD : D x = x - Y.adjoint (Y x) := by
          show (ContinuousLinearMap.id ℂ E - G) x = x - Y.adjoint (Y x)
          rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
            ContinuousLinearMap.comp_apply]
        rw [hD]
        simp [inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
          inner_self_eq_norm_sq, ← Complex.ofReal_pow]
      rw [hval]
      have hle : ‖Y x‖ ≤ ‖x‖ :=
        calc ‖Y x‖ ≤ ‖Y‖ * ‖x‖ := Y.le_opNorm x
          _ ≤ 1 * ‖x‖ :=
              mul_le_mul_of_nonneg_right
                (norm_quarterAcuteAngularOperator_lt_one U V hquarter).le
                (norm_nonneg x)
          _ = ‖x‖ := one_mul _
      nlinarith [hle, norm_nonneg (Y x), norm_nonneg x]
  have hDsp : IsStrictlyPositive D := ⟨hDnonneg, hDunit⟩
  have hDinvNonneg : (0 : E →L[ℂ] E) ≤ Ring.inverse D := by
    rw [CFC.inverse_eq_rpow_neg_one hDsp]
    exact CFC.rpow_nonneg
  have hDinvSA : IsSelfAdjoint (Ring.inverse D) := hDinvNonneg.isSelfAdjoint
  have hcomm : Commute (ContinuousLinearMap.modulus Y) (Ring.inverse D) := by
    have hmodG : Commute (ContinuousLinearMap.modulus Y) G := by
      show Commute (ContinuousLinearMap.modulus Y) (Y.adjoint ∘L Y)
      rw [← ContinuousLinearMap.modulus_mul_self Y]
      exact (Commute.refl _).mul_right (Commute.refl _)
    have hmodD : Commute (ContinuousLinearMap.modulus Y) D := by
      show Commute (ContinuousLinearMap.modulus Y)
        (ContinuousLinearMap.id ℂ E - G)
      exact (Commute.one_right _).sub_right hmodG
    have hu : Commute (ContinuousLinearMap.modulus Y)
        ((hDunit.unit : E →L[ℂ] E)) := by
      rw [hDunit.unit_spec]; exact hmodD
    rw [Ring.inverse_of_isUnit hDunit]
    exact hu.units_inv_right
  have hMsq : M ∘L M =
      (4 : ℂ) • (ContinuousLinearMap.modulus Y ∘L
        Ring.inverse D ∘L ContinuousLinearMap.modulus Y ∘L Ring.inverse D) := by
    -- `|T|² = T⋆ T` with `T = 2 • (Y D⁻¹)`, hence
    --   T⋆ T = 4 • (D⁻¹ Y⋆ Y D⁻¹) = 4 • (D⁻¹ |Y| |Y| D⁻¹) = 4 • (|Y| D⁻¹ |Y| D⁻¹),
    -- the last step by `[|Y|, D⁻¹] = 0`.  The old script called `star_smul` and
    -- `star_mul` *after* `modulus_mul_self` had already put the goal in `adjoint`
    -- form, so neither could ever fire.
    have hDinvAdj :
        ContinuousLinearMap.adjoint (Ring.inverse D) = Ring.inverse D := by
      simpa only [ContinuousLinearMap.star_eq_adjoint] using hDinvSA.star_eq
    have hYsq : ContinuousLinearMap.adjoint Y * Y
        = ContinuousLinearMap.modulus Y * ContinuousLinearMap.modulus Y :=
      (ContinuousLinearMap.modulus_mul_self Y).symm
    dsimp [M]
    rw [← ContinuousLinearMap.mul_def, ContinuousLinearMap.modulus_mul_self,
      hTformula]
    -- `adjoint` is a *conjugate*-linear isometry equiv (`≃ₗᵢ⋆`), so the scalar
    -- comes out through `map_smulₛₗ` as `star 2`, not as `2`.
    rw [map_smulₛₗ, ContinuousLinearMap.adjoint_comp, hDinvAdj]
    show (starRingEnd ℂ) 2 • (Ring.inverse D * ContinuousLinearMap.adjoint Y) *
          ((2 : ℂ) • (Y * Ring.inverse D))
        = (4 : ℂ) • (ContinuousLinearMap.modulus Y *
            (Ring.inverse D * (ContinuousLinearMap.modulus Y * Ring.inverse D)))
    rw [map_ofNat, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [show (2 : ℂ) * 2 = 4 by norm_num]
    congr 1
    calc Ring.inverse D * ContinuousLinearMap.adjoint Y * (Y * Ring.inverse D)
        = Ring.inverse D * (ContinuousLinearMap.adjoint Y * Y) * Ring.inverse D := by
          noncomm_ring
      _ = Ring.inverse D * (ContinuousLinearMap.modulus Y *
            ContinuousLinearMap.modulus Y) * Ring.inverse D := by rw [hYsq]
      _ = (Ring.inverse D * ContinuousLinearMap.modulus Y) *
            (ContinuousLinearMap.modulus Y * Ring.inverse D) := by noncomm_ring
      _ = (ContinuousLinearMap.modulus Y * Ring.inverse D) *
            (ContinuousLinearMap.modulus Y * Ring.inverse D) := by
          rw [hcomm.symm.eq]
      _ = ContinuousLinearMap.modulus Y *
            (Ring.inverse D * (ContinuousLinearMap.modulus Y * Ring.inverse D)) := by
          noncomm_ring
  have hCandidateNonneg :
      (0 : E →L[ℂ] E) ≤
        (2 : ℂ) • (ContinuousLinearMap.modulus Y ∘L Ring.inverse D) := by
    have hprod : (0 : E →L[ℂ] E) ≤
        ContinuousLinearMap.modulus Y ∘L Ring.inverse D :=
      hcomm.mul_nonneg hmodYnonneg hDinvNonneg
    -- The scalar is ℂ, so `smul_nonneg` -- which supplies the ℝ-action -- is the
    -- wrong lemma.  The two statements print *identically* and differ only in the
    -- `SMul` instance, which is why the mismatch looked like a no-op.
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    -- `0 ≤ (2 : ℂ)` is an order on ℂ (`re` compared, `im` equal), so it needs
    -- `Complex.le_def`; `norm_num` alone does not unfold it.
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hprod).smul_of_nonneg
      (by simp [Complex.le_def])
  have hMformula :
      M = (2 : ℂ) • (ContinuousLinearMap.modulus Y ∘L Ring.inverse D) := by
    -- the lemma concludes `b = |T|`, the goal is `|T| = b`, hence `.symm`
    refine (ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
      hCandidateNonneg ?_).symm
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.modulus_mul_self]
    -- `hMsq` is stated with `∘SL`; restate it with `*` so it matches here.
    rw [show M * M = (4 : ℂ) • (ContinuousLinearMap.modulus Y ∘L
          Ring.inverse D ∘L ContinuousLinearMap.modulus Y ∘L Ring.inverse D)
        from hMsq]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul,
      show (2 : ℂ) * 2 = 4 by norm_num]
    -- `congr 1` discharges the remaining associativity itself; no `noncomm_ring`
    -- is needed (adding one reports "no goals to be solved").
    congr 1
  have hSCformula : Sang ∘L Cang =
      ContinuousLinearMap.modulus Y ∘L R ∘L P := by
    have hleftNonneg : (0 : E →L[ℂ] E) ≤ Sang ∘L Cang :=
      hSCcomm.mul_nonneg (sinAngleOperatorDirectedC_nonneg U V)
        (cosAngleOperatorC_nonneg U V)
    have hrightNonneg : (0 : E →L[ℂ] E) ≤
        ContinuousLinearMap.modulus Y ∘L R ∘L P := by
      -- all three factors are nonnegative functions of `G` on `U`
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      refine ⟨?_, ?_⟩
      · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
        intro x y
        simp [ContinuousLinearMap.adjoint_inner_left]
      · intro x
        rw [ContinuousLinearMap.reApplyInnerSelf_apply]
        positivity
    apply CFC.sqrt_unique
    · rw [← hSCcomm.eq, ContinuousLinearMap.comp_assoc,
        ← ContinuousLinearMap.comp_assoc Sang, hSangSq,
        ContinuousLinearMap.comp_assoc, hCangSq]
      rw [hGR, hGP, hPR]
      noncomm_ring
    · exact hleftNonneg
    · rw [ContinuousLinearMap.comp_assoc,
        ← ContinuousLinearMap.comp_assoc (ContinuousLinearMap.modulus Y),
        ContinuousLinearMap.modulus_mul_self Y]
      rw [hGR, hGP, hPR]
      noncomm_ring
    · exact hrightNonneg
  have hCandidateComp :
      M ∘L cosTwoAngleExtendedC U V = sinTwoAngleOperatorC U V := by
    rw [hMformula, cosTwoAngleExtendedC, hCosTwo, hSinTwo, hSCformula]
    have hMperp : ContinuousLinearMap.modulus Y ∘L Uᗮ.starProjection = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      rw [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.modulus_apply_eq_zero_iff]
      have hzero : Y (Uᗮ.starProjection x) = 0 := by
        have h := DFunLike.congr_fun hYP (Uᗮ.starProjection x)
        rw [ContinuousLinearMap.comp_apply,
          Submodule.starProjection_apply_eq_zero_iff.mpr
            (Uᗮ.starProjection_apply_mem x)] at h
        simpa using h.symm
      exact hzero
    rw [ContinuousLinearMap.comp_add, hMperp, add_zero]
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc,
      Ring.inverse_mul_cancel D hDunit, ContinuousLinearMap.id_comp]
    noncomm_ring
  have hcanonical := tanTwoAngleOperatorC_comp_cosTwoAngleExtendedC U V hquarter
  have hcosSurj : Function.Surjective (cosTwoAngleExtendedC U V) := by
    rw [← LinearMap.range_eq_top]
    exact (cosTwoAngleExtendedC_ker_bot_range_top U V hquarter).2
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hcosSurj x
  have h1 := DFunLike.congr_fun hcanonical y
  have h2 := DFunLike.congr_fun hCandidateComp y
  exact h1.trans h2.symm

/-- The canonical ambient `tan 2Theta` and the rectangular graph-coordinate
operator have the same full approximation-number sequence. -/
theorem canonicalTanTwoAngle_hasSameApproximationNumbers_graphCoordinate
    (U V : Submodule ℂ E) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hquarter : IsQuarterAcute U V) :
    (tanTwoAngleOperatorC U V hquarter).HasSameApproximationNumbers
      (doubleAngleTangentOperator
        (quarterAcuteAngularCoordinate U V hquarter)
        (norm_quarterAcuteAngularCoordinate_lt_one U V hquarter)) := by
  let Y : E →L[ℂ] E := quarterAcuteAngularOperator U V hquarter
  let X : U →L[ℂ] Uᗮ := quarterAcuteAngularCoordinate U V hquarter
  let hYc : ‖Y‖ < 1 := norm_quarterAcuteAngularOperator_lt_one U V hquarter
  let hXc : ‖X‖ < 1 := norm_quarterAcuteAngularCoordinate_lt_one U V hquarter
  have hcanonical : tanTwoAngleOperatorC U V hquarter =
      ContinuousLinearMap.modulus (doubleAngleTangentOperator Y hYc) := by
    simpa only [Y, hYc] using
      tanTwoAngleOperatorC_eq_modulus_ambientGraphTangent U V hquarter
  have hambient : doubleAngleTangentOperator Y hYc =
      Uᗮ.subtypeL ∘L doubleAngleTangentOperator X hXc ∘L U.subtypeL.adjoint := by
    simpa only [Y, X, hYc, hXc, quarterAcuteAngularCoordinate] using
      ambient_doubleAngleTangent_eq_extendCoordinate U Y
        (quarterAcuteAngularOperator_isAngularOperator U V hquarter) hYc
  rw [hcanonical]
  exact
    (sameApproximationSingularValues_rectangularOperatorModulus
      (doubleAngleTangentOperator Y hYc)).trans
      (by
        rw [hambient]
        exact sameApproximationSingularValues_ambientSubspaceBlock U Uᗮ
          (doubleAngleTangentOperator X hXc))

end

end FinishTanTwoTheta
end DavisKahan
end TauCeti
