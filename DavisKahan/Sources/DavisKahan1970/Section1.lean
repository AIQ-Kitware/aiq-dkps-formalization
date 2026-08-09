/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Frontier.Section8Residual

/-!
# Davis--Kahan 1970, Section 1: the residual and its block column

Section 1 is almost all notation: the isometries `E₀, E₁` and `F₀, F₁` of (1.1), the block
representations (1.2)--(1.3), the unitaries `V` of (1.4)--(1.7).  Those are definitions, and
they are carried in this repository by the data records the theorems consume
(`UnboundedSinThetaData`, `PaperTheorem61Data`), whose fields *are* the trial map, the
compression and the residual.

Section 1 does make three claims, and this file gives them the paper's numbering:

* (1.8) itself, `R = (A + H)E₀ - E₀A₀`, which is `DavisKahan.residual`;
* the Section 1 remark that `R` is the first block *column* of the perturbation, `R = HE₀`;
* the identity `R⋆R = H₀² + B⋆B` and the conclusion the paper draws from it -- that among
  all choices of `A₀` the residual is smallest when `H₀ = 0`, which is the Rayleigh-quotient
  choice `A₀ = E₀⋆(A + H)E₀`.

The first two are already compiled; this file supplies the source names.  The third is proved
here, in the quadratic form the paper uses it in: for `u ∈ Pℋ`, `P(Hu)` is `E₀H₀u` and
`P̃(Hu)` is `E₁Bu`, and both isometries preserve norms, so
`‖Ru‖² = ‖H₀u‖² + ‖Bu‖²` is exactly the printed operator identity read at `u`.  Over `ℂ` a
self-adjoint operator is determined by its quadratic form, so nothing is lost by stating it
this way, and the coordinate isometries `E₀, E₁` are not needed.

The residual identities live upstream in `DavisKahan/Frontier/Section8Residual.lean`, where
Theorem 8.2's residual branch consumes them; they are cited by `:=` here rather than
restated, so there is a single source of truth.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

universe u

section Residual

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Davis--Kahan 1970, equation (1.8): the residual.**

`R = (A + H)E₀ - E₀A₀`, for `E₀` an isometric embedding of the trial space and `A₀` the
trial operator on it.  The compiled definition is more general than the printed one in one
respect: `E₀` is an arbitrary bounded map rather than an isometry, and `A₀` an arbitrary
operator on its source space rather than one whose eigenvalues approximate the `λⱼ`.  Every
source-facing consumer instantiates `E₀` at `P.subtypeL` and `A₀` at `compressOperator P A`,
which is the printed configuration. -/
alias Equation1_8 := DavisKahan.residual

/-- **Davis--Kahan 1970, Section 1: the residual is the first block column of the
perturbation**, `R = HE₀`.

The printed sentence is "the reader may want to check formally from (1.3) and (1.8) that
`R`, left-multiplied by the isometry `(E₀⋆; E₁⋆)`, gives the first column of `(H₀ B⋆; B H₁)`;
or that `R = HE₀`".  The hypothesis is the printed one: `Pℋ` reduces the unperturbed
operator, so on it the compression `A₀` is the honest restriction and the two `A` terms
cancel. -/
alias equation1_8_eq_perturbation_comp :=
  DavisKahan.Experimental.Frontier.Section8.residual_eq_comp_subtypeL

/-- **Davis--Kahan 1970, Section 1: `R⋆R = H₀² + B⋆B`.**

Stated as the quadratic form of that operator identity, which over `ℂ` carries the same
information: `P(Ku)` is the paper's `E₀H₀u` and `Pᗮ(Ku)` is its `E₁Bu`, and `E₀`, `E₁` are
isometries.  Once `R = KE₀` is known (`equation1_8_eq_perturbation_comp`) this is the
Pythagorean splitting of `Ku` along `Pℋ ⊕ P̃ℋ`.  The printed identity writes `H₀²` rather
than `H₀⋆H₀` because `H₀ = E₀⋆HE₀` is a compression of the self-adjoint `H` and so is itself
self-adjoint; the statement here is in norms, which needs no such hypothesis, and `K` is
accordingly an arbitrary bounded operator. -/
theorem equation1_8_norm_sq_eq_diagonal_add_offDiagonal
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (hPinv : ∀ x ∈ P, A x ∈ P) (u : P) :
    ‖DavisKahan.residual (A + K) P.subtypeL
        (DavisKahanExt.compressOperator P A) u‖ ^ 2 =
      ‖P.starProjection (K (u : H))‖ ^ 2 + ‖Pᗮ.starProjection (K (u : H))‖ ^ 2 := by
  have hR := congrArg (fun T : P →L[ℂ] H => T u)
    (DavisKahan.Experimental.Frontier.Section8.residual_eq_comp_subtypeL A K P hPinv)
  have hRu : DavisKahan.residual (A + K) P.subtypeL
      (DavisKahanExt.compressOperator P A) u = K (u : H) := hR
  rw [hRu]
  exact Submodule.norm_sq_eq_add_norm_sq_starProjection (K (u : H)) P

/-- **Davis--Kahan 1970, Section 1: the off-diagonal block is never larger than the
residual**, and equals it exactly when the diagonal block vanishes.

This is the mechanism behind the printed remark that "the size of `R` is minimized when `H₀`
is taken to be zero", which is what makes `A₀ = E₀⋆(A + H)E₀` -- the `m × m` generalization
of the Rayleigh quotient -- a good choice for the numerical analyst.  It is not that remark
verbatim: the printed one quantifies over choices of `A₀`, whereas `A₀` is fixed here at the
unperturbed compression and the comparison is made pointwise, with equality at `u` exactly
when the diagonal block kills `u`.  Ranging over `A₀` would require the trial operator to be
a variable of the statement, which the residual's compiled signature does not make it. -/
theorem equation1_8_norm_offDiagonal_le
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (hPinv : ∀ x ∈ P, A x ∈ P) (u : P) :
    ‖Pᗮ.starProjection (K (u : H))‖ ≤
        ‖DavisKahan.residual (A + K) P.subtypeL
          (DavisKahanExt.compressOperator P A) u‖ ∧
      (‖Pᗮ.starProjection (K (u : H))‖ =
          ‖DavisKahan.residual (A + K) P.subtypeL
            (DavisKahanExt.compressOperator P A) u‖ ↔
        P.starProjection (K (u : H)) = 0) := by
  set R := DavisKahan.residual (A + K) P.subtypeL
    (DavisKahanExt.compressOperator P A) u with hRdef
  have hsplit := equation1_8_norm_sq_eq_diagonal_add_offDiagonal A K P hPinv u
  have hle : ‖Pᗮ.starProjection (K (u : H))‖ ≤ ‖R‖ := by
    have hsq : ‖Pᗮ.starProjection (K (u : H))‖ ^ 2 ≤ ‖R‖ ^ 2 := by
      rw [hsplit]
      nlinarith [sq_nonneg ‖P.starProjection (K (u : H))‖]
    have hle' := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hle'
  refine ⟨hle, ?_, ?_⟩
  · intro heq
    have hzero : ‖P.starProjection (K (u : H))‖ ^ 2 = 0 := by
      rw [heq] at hsplit
      linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero)
  · intro hzero
    have hsq : ‖Pᗮ.starProjection (K (u : H))‖ ^ 2 = ‖R‖ ^ 2 := by
      rw [hsplit, hzero, norm_zero]
      ring
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

end Residual

end DavisKahan1970
end TauCeti
