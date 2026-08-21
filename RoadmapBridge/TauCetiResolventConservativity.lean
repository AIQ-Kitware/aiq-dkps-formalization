/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import ForTauCeti.Analysis.Normed.Operator.Resolvent.Unbounded

/-!
# Roadmap bridge: the unbounded-resolvent generalization is conservative over `ℝ`

**What this file certifies.** `ForTauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean`
generalizes the landed Tau Ceti module
`TauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean` from the real scalars to an
arbitrary `{𝕜 : Type*} [NontriviallyNormedField 𝕜]`.  A generalization is only safe to land
if it *loses nothing*: every statement the real-scalar module already offered must still be
available, verbatim, by specializing `𝕜 := ℝ`.

Up to here that was an authorial claim.  Each entry below **restates one upstream declaration
exactly as upstream writes it at `ℝ`** -- same binders, same hypothesis order, same
explicit/implicit split, same spelling of every hypothesis -- and discharges it with the
generalized declaration.  If an entry elaborates, the generalization really does subsume that
upstream statement, checked by the compiler rather than by comparing declaration names.  If a
future edit to the generalized file strengthens a hypothesis, reorders a binder, flips an
implicit to explicit, or shifts a conclusion, the corresponding entry stops elaborating and
this file fails the build.

The upstream module has exactly thirty declarations.  Twenty-seven are public and are
discharged below directly from the generalized module.  The remaining three are `private`
upstream and so unreachable from any other module; each is handled explicitly in
`§ The three private upstream declarations` and is not silently dropped.

## The one place where the claim has content

`|·|` does not exist on a general normed field, so two upstream statements had to change
shape.  Upstream

* `mem_resolventSet_of_norm_mul_lt_one` hypothesises `|mu - lambda| * ‖resolvent A lambda‖ < 1`;
* the private `exists_inverse_one_sub_smul_resolvent` hypothesises the same thing;

while the generalization writes `‖mu - lambda‖` in both.  Every other one of the thirty
statements is byte-identical to upstream after renaming `𝕜` to `ℝ` and the carrier `E` to `X`.

So the abs-versus-norm swap is the whole of the risk, and it is not taken on trust here: the
entry for `mem_resolventSet_of_norm_mul_lt_one` restates the upstream hypothesis with `|·|`
and derives it, via `Real.norm_eq_abs`.  Restating the *generalized* form and calling that a
match would have certified nothing, and is deliberately not what happens below.

## What an elaborating entry does and does not establish

It establishes that the generalized declaration, specialized to `ℝ`, inhabits the upstream
type: no hypothesis grew, no conclusion shrank, and the explicit-argument sequence is
unchanged.  It does not pin the *order* of implicit binders among themselves, and it does not
pin declaration names -- an upstream consumer that breaks on a rename would still break.  The
generalized declarations do carry one additional instance argument, `[NontriviallyNormedField 𝕜]`,
which at `𝕜 := ℝ` is discharged by Mathlib's instance; that is intrinsic to generalizing the
scalar and is visible in every entry below.

Implicit binder order was checked once out of band, by printing the elaborated signature of
each of the twenty-seven public declarations from each module in a separate file and
comparing: after deleting the two new `𝕜` binders and renaming `𝕜` to `ℝ` and `E` to `X`,
twenty-six of the twenty-seven agree character for character, and the twenty-seventh differs
in exactly the `|·|`-versus-`‖·‖` hypothesis discussed above.  That comparison cannot be run
from inside a single module -- the two modules declare the same fully qualified names, so no
file may import both -- which is why the per-declaration entries below, and not a signature
dump, are what the build re-checks.
-/

namespace RoadmapBridge.TauCetiResolvent

open TauCeti

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## 1. `IsResolventAt` — the structure, its constructor, and its three fields

A structure is not discharged by a single term, so its interface is checked in both
directions: the type former has the upstream arity and result sort, each of the three
projections is available with its upstream statement, and the anonymous constructor still
accepts exactly those three arguments in that order. -/

/-- Upstream declaration 1 of 30, type former: `IsResolventAt` still takes an unbounded
operator, a scalar and a bounded operator, and lands in `Prop`. -/
example : (X →ₗ.[ℝ] X) → ℝ → (X →L[ℝ] X) → Prop := LinearPMap.IsResolventAt

/-- Field 1 of `IsResolventAt`: the inverse takes its values in the domain of `A`. -/
theorem isResolventAt_mem_domain {A : X →ₗ.[ℝ] X} {lambda : ℝ} {R : X →L[ℝ] X}
    (h : LinearPMap.IsResolventAt A lambda R) (y : X) : R y ∈ A.domain :=
  h.mem_domain y

/-- Field 2 of `IsResolventAt`: `R` is a right inverse of `lambda • I - A`. -/
theorem isResolventAt_smul_sub_apply {A : X →ₗ.[ℝ] X} {lambda : ℝ} {R : X →L[ℝ] X}
    (h : LinearPMap.IsResolventAt A lambda R) (y : X) :
    lambda • R y - A ⟨R y, h.mem_domain y⟩ = y :=
  h.smul_sub_apply y

/-- Field 3 of `IsResolventAt`: `R` is a left inverse of `lambda • I - A` on `D(A)`. -/
theorem isResolventAt_apply_smul_sub {A : X →ₗ.[ℝ] X} {lambda : ℝ} {R : X →L[ℝ] X}
    (h : LinearPMap.IsResolventAt A lambda R) (x : A.domain) :
    R (lambda • (x : X) - A x) = (x : X) :=
  h.apply_smul_sub x

/-- The constructor: the three upstream fields, in the upstream order, still build the
structure.  Together with the three projections above this pins the structure's interface. -/
theorem isResolventAt_mk {A : X →ₗ.[ℝ] X} {lambda : ℝ} {R : X →L[ℝ] X}
    (hmem : ∀ y : X, R y ∈ A.domain)
    (hright : ∀ y : X, lambda • R y - A ⟨R y, hmem y⟩ = y)
    (hleft : ∀ x : A.domain, R (lambda • (x : X) - A x) = (x : X)) :
    LinearPMap.IsResolventAt A lambda R :=
  ⟨hmem, hright, hleft⟩

/-! ## 2–5. Inverting `lambda • I - A` -/

/-- Upstream declaration 2 of 30: `TauCeti.LinearPMap.IsResolventAt.unique`. -/
theorem isResolventAt_unique {A : X →ₗ.[ℝ] X} {lambda : ℝ} {R : X →L[ℝ] X}
    (h : LinearPMap.IsResolventAt A lambda R) {R' : X →L[ℝ] X}
    (h' : LinearPMap.IsResolventAt A lambda R') : R = R' :=
  h.unique h'

/-- Upstream declaration 3 of 30: `TauCeti.LinearPMap.IsResolventAt.smul_sub_injective`. -/
theorem isResolventAt_smul_sub_injective {A : X →ₗ.[ℝ] X} {lambda : ℝ} {R : X →L[ℝ] X}
    (h : LinearPMap.IsResolventAt A lambda R) :
    Function.Injective fun x : A.domain => lambda • (x : X) - A x :=
  h.smul_sub_injective

/-- Upstream declaration 4 of 30: `TauCeti.LinearPMap.IsResolventAt.smul_sub_surjective`. -/
theorem isResolventAt_smul_sub_surjective {A : X →ₗ.[ℝ] X} {lambda : ℝ} {R : X →L[ℝ] X}
    (h : LinearPMap.IsResolventAt A lambda R) :
    Function.Surjective fun x : A.domain => lambda • (x : X) - A x :=
  h.smul_sub_surjective

/-- Upstream declaration 5 of 30: `TauCeti.LinearPMap.IsResolventAt.smul_sub_bijective`. -/
theorem isResolventAt_smul_sub_bijective {A : X →ₗ.[ℝ] X} {lambda : ℝ} {R : X →L[ℝ] X}
    (h : LinearPMap.IsResolventAt A lambda R) :
    Function.Bijective fun x : A.domain => lambda • (x : X) - A x :=
  h.smul_sub_bijective

/-! ## 6–17. The resolvent set and the resolvent -/

/-- Upstream declaration 6 of 30: `TauCeti.LinearPMap.resolventSet`.  A definition is pinned
by its type and its defining equation; both are checked, the latter by `rfl`. -/
example : (X →ₗ.[ℝ] X) → Set ℝ := LinearPMap.resolventSet

theorem resolventSet_def (A : X →ₗ.[ℝ] X) :
    LinearPMap.resolventSet A =
      {lambda : ℝ | ∃ R : X →L[ℝ] X, LinearPMap.IsResolventAt A lambda R} :=
  rfl

/-- Upstream declaration 7 of 30: `TauCeti.LinearPMap.mem_resolventSet_iff`. -/
theorem mem_resolventSet_iff {A : X →ₗ.[ℝ] X} {lambda : ℝ} :
    lambda ∈ LinearPMap.resolventSet A ↔
      ∃ R : X →L[ℝ] X, LinearPMap.IsResolventAt A lambda R :=
  LinearPMap.mem_resolventSet_iff

/-- Upstream declaration 8 of 30: `TauCeti.LinearPMap.IsResolventAt.mem_resolventSet`. -/
theorem isResolventAt_mem_resolventSet {A : X →ₗ.[ℝ] X} {lambda : ℝ} {R : X →L[ℝ] X}
    (h : LinearPMap.IsResolventAt A lambda R) : lambda ∈ LinearPMap.resolventSet A :=
  h.mem_resolventSet

/-- Upstream declaration 10 of 30: `TauCeti.LinearPMap.resolvent`.  Its body is a
`Classical.choose`, so there is no defining equation to check; the type is pinned here and
the characterizing properties are declarations 11 and 12 below.  (Declaration 9 is `private`
upstream; see the closing section.) -/
noncomputable example : (X →ₗ.[ℝ] X) → ℝ → (X →L[ℝ] X) := LinearPMap.resolvent

/-- Upstream declaration 11 of 30: `TauCeti.LinearPMap.isResolventAt_resolvent`. -/
theorem isResolventAt_resolvent {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (h : lambda ∈ LinearPMap.resolventSet A) :
    LinearPMap.IsResolventAt A lambda (LinearPMap.resolvent A lambda) :=
  LinearPMap.isResolventAt_resolvent h

/-- Upstream declaration 12 of 30: `TauCeti.LinearPMap.resolvent_eq_of_isResolventAt`. -/
theorem resolvent_eq_of_isResolventAt {A : X →ₗ.[ℝ] X} {lambda : ℝ} {R : X →L[ℝ] X}
    (h : LinearPMap.IsResolventAt A lambda R) : LinearPMap.resolvent A lambda = R :=
  LinearPMap.resolvent_eq_of_isResolventAt h

/-- Upstream declaration 13 of 30: `TauCeti.LinearPMap.resolvent_mem_domain`. -/
theorem resolvent_mem_domain {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (h : lambda ∈ LinearPMap.resolventSet A) (y : X) :
    LinearPMap.resolvent A lambda y ∈ A.domain :=
  LinearPMap.resolvent_mem_domain h y

/-- Upstream declaration 14 of 30: `TauCeti.LinearPMap.smul_sub_apply_resolvent`. -/
theorem smul_sub_apply_resolvent {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (h : lambda ∈ LinearPMap.resolventSet A) (y : X) :
    lambda • LinearPMap.resolvent A lambda y -
        A ⟨LinearPMap.resolvent A lambda y, LinearPMap.resolvent_mem_domain h y⟩ = y :=
  LinearPMap.smul_sub_apply_resolvent h y

/-- Upstream declaration 15 of 30: `TauCeti.LinearPMap.resolvent_smul_sub_apply`. -/
theorem resolvent_smul_sub_apply {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (h : lambda ∈ LinearPMap.resolventSet A) (x : A.domain) :
    LinearPMap.resolvent A lambda (lambda • (x : X) - A x) = (x : X) :=
  LinearPMap.resolvent_smul_sub_apply h x

/-- Upstream declaration 16 of 30: `TauCeti.LinearPMap.apply_resolvent`. -/
theorem apply_resolvent {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (h : lambda ∈ LinearPMap.resolventSet A) (y : X) :
    A ⟨LinearPMap.resolvent A lambda y, LinearPMap.resolvent_mem_domain h y⟩ =
      lambda • LinearPMap.resolvent A lambda y - y :=
  LinearPMap.apply_resolvent h y

/-- Upstream declaration 17 of 30: `TauCeti.LinearPMap.smul_sub_bijective`. -/
theorem smul_sub_bijective {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (h : lambda ∈ LinearPMap.resolventSet A) :
    Function.Bijective fun x : A.domain => lambda • (x : X) - A x :=
  LinearPMap.smul_sub_bijective h

/-- Upstream declaration 18 of 30: `TauCeti.LinearPMap.eq_of_le_of_mem_resolventSet`.  This is
the declaration upstream `main` added after the pinned `external/TauCeti` commit, so it is
also the entry that certifies the generalization tracks current upstream rather than the pin. -/
theorem eq_of_le_of_mem_resolventSet {lambda : ℝ} {A B : X →ₗ.[ℝ] X} (hAB : A ≤ B)
    (hA : lambda ∈ LinearPMap.resolventSet A) (hB : lambda ∈ LinearPMap.resolventSet B) :
    A = B :=
  LinearPMap.eq_of_le_of_mem_resolventSet hAB hA hB

/-- Upstream declaration 19 of 30: `TauCeti.LinearPMap.resolvent_apply_comm`. -/
theorem resolvent_apply_comm {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (h : lambda ∈ LinearPMap.resolventSet A) (x : A.domain) :
    LinearPMap.resolvent A lambda (A x) =
      A ⟨LinearPMap.resolvent A lambda (x : X),
        LinearPMap.resolvent_mem_domain h (x : X)⟩ :=
  LinearPMap.resolvent_apply_comm h x

/-! ## 20–22. The resolvent identity -/

/-- Upstream declaration 20 of 30: `TauCeti.LinearPMap.resolvent_sub_resolvent_apply`.  The
sign convention `(mu - lambda) •` is part of the statement and is pinned here. -/
theorem resolvent_sub_resolvent_apply {A : X →ₗ.[ℝ] X} {lambda mu : ℝ}
    (hl : lambda ∈ LinearPMap.resolventSet A) (hm : mu ∈ LinearPMap.resolventSet A) (y : X) :
    LinearPMap.resolvent A lambda y - LinearPMap.resolvent A mu y
      = (mu - lambda) • LinearPMap.resolvent A lambda (LinearPMap.resolvent A mu y) :=
  LinearPMap.resolvent_sub_resolvent_apply hl hm y

/-- Upstream declaration 21 of 30: `TauCeti.LinearPMap.resolvent_sub_resolvent`. -/
theorem resolvent_sub_resolvent {A : X →ₗ.[ℝ] X} {lambda mu : ℝ}
    (hl : lambda ∈ LinearPMap.resolventSet A) (hm : mu ∈ LinearPMap.resolventSet A) :
    LinearPMap.resolvent A lambda - LinearPMap.resolvent A mu
      = (mu - lambda) • (LinearPMap.resolvent A lambda ∘L LinearPMap.resolvent A mu) :=
  LinearPMap.resolvent_sub_resolvent hl hm

/-- Upstream declaration 22 of 30: `TauCeti.LinearPMap.resolvent_comm`. -/
theorem resolvent_comm {A : X →ₗ.[ℝ] X} {lambda mu : ℝ}
    (hl : lambda ∈ LinearPMap.resolventSet A) (hm : mu ∈ LinearPMap.resolventSet A) :
    LinearPMap.resolvent A lambda ∘L LinearPMap.resolvent A mu
      = LinearPMap.resolvent A mu ∘L LinearPMap.resolvent A lambda :=
  LinearPMap.resolvent_comm hl hm

/-! ## 24–25. Openness of the resolvent set — the abs-versus-norm entry

This is the only section in which the generalized statement is not the upstream statement,
and therefore the only section that carries real risk.  Declaration 24 is restated with the
upstream `|mu - lambda|` and *derived*; the derivation is the one-line `Real.norm_eq_abs`
recorded immediately below it. -/

/-- The whole content of the abs-versus-norm change, isolated: on `ℝ` the norm of a scalar is
its absolute value, so `‖mu - lambda‖ * ‖R‖ < 1` and `|mu - lambda| * ‖R‖ < 1` are the same
hypothesis and the generalization neither strengthened nor weakened it. -/
theorem real_norm_eq_abs (r : ℝ) : ‖r‖ = |r| := Real.norm_eq_abs r

/-- Upstream declaration 24 of 30: `TauCeti.LinearPMap.mem_resolventSet_of_norm_mul_lt_one`,
stated with the upstream `|mu - lambda|`, not with the generalized `‖mu - lambda‖`. -/
theorem mem_resolventSet_of_norm_mul_lt_one {A : X →ₗ.[ℝ] X} {lambda mu : ℝ} [CompleteSpace X]
    (h : lambda ∈ LinearPMap.resolventSet A)
    (hmu : |mu - lambda| * ‖LinearPMap.resolvent A lambda‖ < 1) :
    mu ∈ LinearPMap.resolventSet A :=
  LinearPMap.mem_resolventSet_of_norm_mul_lt_one h (by rwa [Real.norm_eq_abs])

/-- Upstream declaration 25 of 30: `TauCeti.LinearPMap.isOpen_resolventSet`.  The topology on
the scalars is the one `ℝ` already carries, so the openness statement is unchanged; had the
generalization introduced a different topology on `𝕜`, this entry would not elaborate. -/
theorem isOpen_resolventSet [CompleteSpace X] (A : X →ₗ.[ℝ] X) :
    IsOpen (LinearPMap.resolventSet A) :=
  LinearPMap.isOpen_resolventSet A

/-! ## 27–30. The bridge to Mathlib's Banach-algebra resolvent -/

/-- Upstream declaration 27 of 30: `TauCeti.LinearPMap.isUnit_of_isResolventAt_toPMap_top`. -/
theorem isUnit_of_isResolventAt_toPMap_top {lambda : ℝ} {R T : X →L[ℝ] X}
    (h : LinearPMap.IsResolventAt ((T : X →ₗ[ℝ] X).toPMap ⊤) lambda R) :
    IsUnit (algebraMap ℝ (X →L[ℝ] X) lambda - T) :=
  LinearPMap.isUnit_of_isResolventAt_toPMap_top h

/-- Upstream declaration 28 of 30: `TauCeti.LinearPMap.isResolventAt_toPMap_top_of_isUnit`.
The conclusion names the algebra inverse `h.unit⁻¹` explicitly, so this entry also pins which
operator the generalized declaration exhibits, not merely that one exists. -/
theorem isResolventAt_toPMap_top_of_isUnit {lambda : ℝ} {T : X →L[ℝ] X}
    (h : IsUnit (algebraMap ℝ (X →L[ℝ] X) lambda - T)) :
    LinearPMap.IsResolventAt ((T : X →ₗ[ℝ] X).toPMap ⊤) lambda
      ((h.unit⁻¹ : (X →L[ℝ] X)ˣ) : X →L[ℝ] X) :=
  LinearPMap.isResolventAt_toPMap_top_of_isUnit h

/-- Upstream declaration 29 of 30: `TauCeti.LinearPMap.mem_resolventSet_toPMap_top_iff`. -/
theorem mem_resolventSet_toPMap_top_iff (T : X →L[ℝ] X) (lambda : ℝ) :
    lambda ∈ LinearPMap.resolventSet ((T : X →ₗ[ℝ] X).toPMap ⊤) ↔
      lambda ∈ _root_.resolventSet ℝ T :=
  LinearPMap.mem_resolventSet_toPMap_top_iff T lambda

/-- Upstream declaration 30 of 30: `TauCeti.LinearPMap.resolvent_toPMap_top`. -/
theorem resolvent_toPMap_top (T : X →L[ℝ] X) {lambda : ℝ}
    (h : lambda ∈ _root_.resolventSet ℝ T) :
    LinearPMap.resolvent ((T : X →ₗ[ℝ] X).toPMap ⊤) lambda = _root_.resolvent T lambda :=
  LinearPMap.resolvent_toPMap_top T h

/-! ## The three private upstream declarations

Declarations 9, 23 and 26 are `private` in both modules and therefore unreachable from here.
Being private, none of them can have an out-of-module consumer, so none of them can be a
route by which the generalization loses something a caller depended on: whatever they supply
reaches the outside world only through the public declarations already discharged above.
They are nonetheless accounted for individually rather than dropped from the count.

* **Declaration 9, `exists_isResolventAt_of_mem`.** Its exact upstream statement is restated
  and discharged below from the generalized module's *public* API, so this one is a genuine
  bridge entry despite the privacy.

* **Declaration 23, `exists_inverse_one_sub_smul_resolvent`.** Deliberately *not* restated.
  Its statement mentions an existentially quantified Neumann inverse `U` that no public
  declaration returns, so it cannot be discharged from the generalized module; the only
  alternative would be to re-run upstream's proof here, which would certify a fact about
  Mathlib and nothing at all about the generalization.  Its single upstream consumer is
  declaration 24, and declaration 24 is discharged above *with the upstream `|mu - lambda|`
  hypothesis* -- which is exactly the abs-versus-norm content this private lemma carries.

* **Declaration 26, `algebraMap_sub_apply`.** Restated below.  Read it as an availability
  check only: the statement mentions no declaration of either module, so it is a fact about
  Mathlib's `algebraMap` that happens to be true at `ℝ`, and its proof here cannot and does
  not route through the generalized module.  The substantive claim it supports upstream --
  that `algebraMap ℝ (X →L[ℝ] X) lambda - T` is the operator `lambda • I - T` used by the
  unbounded notion -- is certified by declarations 27 to 30 above, which are genuine bridge
  entries. -/

/-- Upstream declaration 9 of 30, `exists_isResolventAt_of_mem`: restated verbatim, and
discharged from the generalized module's public `resolvent` and `isResolventAt_resolvent`. -/
theorem exists_isResolventAt_of_mem (A : X →ₗ.[ℝ] X) (lambda : ℝ) :
    ∃ R : X →L[ℝ] X, lambda ∈ LinearPMap.resolventSet A →
      LinearPMap.IsResolventAt A lambda R :=
  ⟨LinearPMap.resolvent A lambda, fun h => LinearPMap.isResolventAt_resolvent h⟩

/-- Upstream declaration 26 of 30, `algebraMap_sub_apply`: restated verbatim.  See the caveat
in the section header -- this is an availability check, not evidence about the
generalization. -/
theorem algebraMap_sub_apply (T : X →L[ℝ] X) (lambda : ℝ) (y : X) :
    (algebraMap ℝ (X →L[ℝ] X) lambda - T) y = lambda • y - T y := by
  simp [Algebra.algebraMap_eq_smul_one]

end RoadmapBridge.TauCetiResolvent
