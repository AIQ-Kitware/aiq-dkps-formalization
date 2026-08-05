/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
import DavisKahan.BoundedOperator.Compat
import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Closed densely defined operators

The bundled closed-operator interface: domain, graph closedness, the Mathlib
partial-map view, bounded extensions, graph norms, relative boundedness, and
the real resolvent set and spectrum.

Everything here is proved.  The declarations that remain open obligations --
the bundled adjoint, the relatively bounded sum, the unbounded spectral
projection, and the perturbation theorems that depend on them -- stay in
`DavisKahan.Experimental.InfiniteDimensional.Core.Unbounded`, which imports
this file.  Splitting them apart is what lets the source-faithful sine-theta
layer reach `ClosedOperator` without inheriting an admission closure.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Experimental.Foundation

open DavisKahan

open scoped InnerProductSpace
open Filter Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Densely defined closed operator. -/
structure ClosedOperator where
  domain : Submodule 𝕜 E
  toLinearMap : domain →ₗ[𝕜] E
  dense_domain : Dense (domain : Set E)
  closed_graph : IsClosed (Set.range fun x : domain => ((x : E), toLinearMap x))

namespace ClosedOperator

/-- Apply a closed operator to a vector carrying its domain witness. -/
def apply (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (x : A.domain) : E :=
  A.toLinearMap x

/-- The domain of a closed operator, as a submodule. -/
instance : CoeFun (ClosedOperator (𝕜 := 𝕜) (E := E))
    (fun A => A.domain → E) where
  coe A := A.apply

/-- The canonical Mathlib partial-linear-map view of a closed operator. -/
def toLinearPMap (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : E →ₗ.[𝕜] E where
  domain := A.domain
  toFun := A.toLinearMap

omit [CompleteSpace E] in
/-- The domain of the underlying partial map is the closed operator's domain. -/
@[simp] theorem toLinearPMap_domain
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.toLinearPMap.domain = A.domain := rfl

omit [CompleteSpace E] in
/-- The underlying partial map acts as the closed operator. -/
@[simp] theorem toLinearPMap_apply
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) (x : A.domain) :
    A.toLinearPMap x = A.toLinearMap x := rfl

omit [CompleteSpace E] in
/-- The partial-linear-map view retains the closed graph. -/
theorem toLinearPMap_isClosed
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.toLinearPMap.IsClosed := by
  change IsClosed (A.toLinearPMap.graph : Set (E × E))
  have hgraph : (A.toLinearPMap.graph : Set (E × E)) =
      Set.range (fun x : A.domain => ((x : E), A.toLinearMap x)) := by
    ext p
    change p ∈ A.toLinearPMap.graph ↔
      ∃ x : A.domain, ((x : E), A.toLinearMap x) = p
    rw [LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨x, hx, hAx⟩
      exact ⟨x, Prod.ext hx hAx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩
  rw [hgraph]
  exact A.closed_graph

omit [CompleteSpace E] in
/-- The partial-linear-map view retains the dense domain. -/
theorem toLinearPMap_dense
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    Dense (A.toLinearPMap.domain : Set E) := by
  simpa using A.dense_domain

/-- The partial-map adjoint of a densely defined closed operator is closed. -/
theorem toLinearPMap_adjoint_isClosed
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.toLinearPMap.adjoint.IsClosed :=
  LinearPMap.adjoint_isClosed A.toLinearPMap_dense

/-- Compatibility facade for equality of the canonical partial-map domains. -/
abbrev SameDomain (A B : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  TauCeti.LinearPMap.SameDomain A.toLinearPMap B.toLinearPMap

omit [CompleteSpace E] in
/-- Equality of domains is reflexive. -/
@[refl] theorem SameDomain.refl (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.SameDomain A :=
  TauCeti.LinearPMap.SameDomain.refl A.toLinearPMap

omit [CompleteSpace E] in
/-- Equality of domains is symmetric. -/
@[symm] theorem SameDomain.symm {A B : ClosedOperator (𝕜 := 𝕜) (E := E)}
    (h : A.SameDomain B) : B.SameDomain A :=
  TauCeti.LinearPMap.SameDomain.symm h

omit [CompleteSpace E] in
/-- Equality of domains is transitive. -/
@[trans] theorem SameDomain.trans {A B C : ClosedOperator (𝕜 := 𝕜) (E := E)}
    (hAB : A.SameDomain B) (hBC : B.SameDomain C) : A.SameDomain C :=
  TauCeti.LinearPMap.SameDomain.trans hAB hBC

/-- Compatibility facade for domain transport between canonical partial maps. -/
abbrev MapsDomainTo
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : ClosedOperator (𝕜 := 𝕜) (E := F))
    (X : F →L[𝕜] E) : Prop :=
  TauCeti.LinearPMap.MapsDomainTo A.toLinearPMap B.toLinearPMap X

/-- The identity map preserves every operator domain. -/
theorem MapsDomainTo.id (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.MapsDomainTo A (ContinuousLinearMap.id 𝕜 E) :=
  TauCeti.LinearPMap.MapsDomainTo.id A.toLinearPMap

omit [CompleteSpace E] in
/-- Domain transport composes with bounded maps. -/
theorem MapsDomainTo.comp
    {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperator (𝕜 := 𝕜) (E := F)}
    {C : ClosedOperator (𝕜 := 𝕜) (E := G)}
    {X : F →L[𝕜] E} {Y : G →L[𝕜] F}
    (hX : A.MapsDomainTo B X) (hY : B.MapsDomainTo C Y) :
    A.MapsDomainTo C (X ∘L Y) :=
  TauCeti.LinearPMap.MapsDomainTo.comp hX hY

/-- Compatibility alias for the reusable bounded-extension record. -/
abbrev BoundedExtension
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (D : Submodule 𝕜 F) (T : D →ₗ[𝕜] E) :=
  TauCeti.LinearPMap.BoundedExtension D T

/-- Regard a bounded operator as a closed operator with full domain.

Only the closed-graph field uses the general closed-graph theorem; the domain
and action are definitionally the expected ones so bounded specializations can
be reduced to the general API without a second operator model. -/
noncomputable def ofBounded (A : E →L[𝕜] E) :
    ClosedOperator (𝕜 := 𝕜) (E := E) where
  domain := ⊤
  toLinearMap := A.toLinearMap.domRestrict ⊤
  dense_domain := by simp
  closed_graph := by
    apply IsSeqClosed.isClosed
    rintro φ ⟨x, y⟩ hmem hlim
    choose xn hxn using hmem
    have hfst : (fun n => ((xn n : (⊤ : Submodule 𝕜 E)) : E)) =
        fun n => (φ n).1 := by
      funext n
      exact congrArg Prod.fst (hxn n)
    have hsnd : (fun n => A ((xn n : (⊤ : Submodule 𝕜 E)) : E)) =
        fun n => (φ n).2 := by
      funext n
      exact congrArg Prod.snd (hxn n)
    have hx : Tendsto (fun n => ((xn n : (⊤ : Submodule 𝕜 E)) : E))
        atTop (𝓝 x) := by
      rw [hfst]
      exact hlim.fst_nhds
    have hy : Tendsto (fun n => A ((xn n : (⊤ : Submodule 𝕜 E)) : E))
        atTop (𝓝 y) := by
      rw [hsnd]
      exact hlim.snd_nhds
    have hAx : Tendsto (fun n => A ((xn n : (⊤ : Submodule 𝕜 E)) : E))
        atTop (𝓝 (A x)) :=
      (A.continuous.tendsto x).comp hx
    have hyeq : y = A x := tendsto_nhds_unique hy hAx
    refine ⟨⟨x, Submodule.mem_top⟩, ?_⟩
    ext
    · rfl
    · simp [hyeq]

omit [CompleteSpace E] in
/-- A bounded operator, viewed as closed, has full domain. -/
@[simp] theorem ofBounded_domain (A : E →L[𝕜] E) :
    (ofBounded A).domain = ⊤ := rfl

omit [CompleteSpace E] in
/-- A bounded operator, viewed as closed, acts as itself. -/
@[simp] theorem ofBounded_apply (A : E →L[𝕜] E)
    (x : (ofBounded A).domain) :
    (ofBounded A) x = A (x : E) := rfl

omit [CompleteSpace E] in
/-- The bounded closed-operator embedding agrees with Mathlib's full-domain
partial-linear-map constructor. -/
@[simp] theorem toLinearPMap_ofBounded (A : E →L[𝕜] E) :
    (ofBounded A).toLinearPMap = A.toLinearMap.toPMap ⊤ := rfl

/-- A bounded symmetric operator becomes self-adjoint after embedding it as a
full-domain closed operator. -/
theorem toLinearPMap_ofBounded_isSelfAdjoint (A : E →L[𝕜] E)
    (hA : A.toLinearMap.IsSymmetric) :
    IsSelfAdjoint (ofBounded A).toLinearPMap := by
  rw [LinearPMap.isSelfAdjoint_def]
  change (A.toLinearMap.toPMap ⊤).adjoint = A.toLinearMap.toPMap ⊤
  rw [A.toPMap_adjoint_eq_adjoint_toPMap_of_dense (by simp)]
  rw [hA.clm_adjoint_eq]

omit [CompleteSpace E] in
/-- Every bounded map lands in the full domain of a bounded closed operator. -/
theorem MapsDomainTo.ofBounded_left
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] E)
    (B : ClosedOperator (𝕜 := 𝕜) (E := F))
    (X : F →L[𝕜] E) :
    (ofBounded A).MapsDomainTo B X := by
  intro x
  simp

/-- Compatibility facade for extension of canonical partial maps. -/
abbrev Extends (A B : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  TauCeti.LinearPMap.Extends A.toLinearPMap B.toLinearPMap

omit [CompleteSpace E] in
/-- Every closed operator extends itself. -/
@[refl] theorem Extends.refl (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.Extends A :=
  TauCeti.LinearPMap.Extends.refl A.toLinearPMap

omit [CompleteSpace E] in
/-- Extension of closed operators is transitive. -/
@[trans] theorem Extends.trans {A B C : ClosedOperator (𝕜 := 𝕜) (E := E)}
    (hAB : A.Extends B) (hBC : B.Extends C) : A.Extends C :=
  TauCeti.LinearPMap.Extends.trans hAB hBC

/-- Compatibility facade for symmetry of the canonical partial map. -/
abbrev IsSymmetric (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  TauCeti.LinearPMap.IsSymmetric A.toLinearPMap

omit [CompleteSpace E] in
/-- Rewrite symmetry of the canonical partial map through the historical
`toLinearMap` compatibility field. -/
theorem IsSymmetric.toLinearMap_inner_eq
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    (hA : A.IsSymmetric) (x y : A.domain) :
    ⟪A.toLinearMap x, (y : E)⟫_𝕜 =
      ⟪(x : E), A.toLinearMap y⟫_𝕜 := by
  simpa only [toLinearPMap_apply] using hA x y
/-- A closed operator is self-adjoint when its canonical Mathlib partial
operator equals its Hilbert-space adjoint.

This definition uses the genuine domain-aware adjoint relation already provided
by `LinearPMap`; it does not depend on the provisional bundled-adjoint
constructor above.  Maximal symmetry alone is intentionally insufficient. -/
def IsSelfAdjoint (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  _root_.IsSelfAdjoint A.toLinearPMap

/-- Unfold self-adjointness into equality with the Mathlib partial-map adjoint. -/
theorem isSelfAdjoint_iff_toLinearPMap_adjoint_eq
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.IsSelfAdjoint ↔ A.toLinearPMap.adjoint = A.toLinearPMap :=
  LinearPMap.isSelfAdjoint_def

/-- A self-adjoint closed operator equals its partial-map adjoint. -/
theorem IsSelfAdjoint.toLinearPMap_adjoint_eq
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    (hA : A.IsSelfAdjoint) :
    A.toLinearPMap.adjoint = A.toLinearPMap :=
  (A.isSelfAdjoint_iff_toLinearPMap_adjoint_eq).mp hA

/-- A self-adjoint closed operator is symmetric on its operator domain. -/
theorem IsSelfAdjoint.isSymmetric
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    (hA : A.IsSelfAdjoint) : A.IsSymmetric := by
  rw [isSelfAdjoint_iff_toLinearPMap_adjoint_eq] at hA
  have hformal := LinearPMap.adjoint_isFormalAdjoint A.toLinearPMap_dense
  rw [hA] at hformal
  intro x y
  exact hformal x y

/-- A symmetric bounded operator becomes self-adjoint in the full-domain closed
operator model.  This is the analytic bridge that makes bounded theorems true
specializations of the canonical unbounded API. -/
theorem ofBounded_isSelfAdjoint (A : E →L[𝕜] E)
    (hA : A.IsSymmetric) :
    (ofBounded A).IsSelfAdjoint :=
  toLinearPMap_ofBounded_isSelfAdjoint A hA

/-- Compatibility facade for the graph norm of the canonical partial map. -/
noncomputable abbrev graphNorm (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : ℝ :=
  TauCeti.LinearPMap.graphNorm A.toLinearPMap x

omit [CompleteSpace E] in
/-- The graph norm is nonnegative. -/
theorem graphNorm_nonneg (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : 0 ≤ A.graphNorm x :=
  TauCeti.LinearPMap.graphNorm_nonneg A.toLinearPMap x

omit [CompleteSpace E] in
/-- Squaring the graph norm recovers the defining sum of squares. -/
theorem graphNorm_sq (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) :
    A.graphNorm x ^ 2 = ‖(x : E)‖ ^ 2 + ‖A.toLinearMap x‖ ^ 2 :=
  TauCeti.LinearPMap.graphNorm_sq A.toLinearPMap x

omit [CompleteSpace E] in
/-- The ambient norm is controlled by the graph norm. -/
theorem norm_coe_le_graphNorm (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : ‖(x : E)‖ ≤ A.graphNorm x :=
  TauCeti.LinearPMap.norm_coe_le_graphNorm A.toLinearPMap x

omit [CompleteSpace E] in
/-- The operator-value norm is controlled by the graph norm. -/
theorem norm_apply_le_graphNorm (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : ‖A.toLinearMap x‖ ≤ A.graphNorm x :=
  TauCeti.LinearPMap.norm_apply_le_graphNorm A.toLinearPMap x

/-- Sum with a bounded perturbation, on the original domain.

Construction route: retain `A.domain`, define the graph map by
`x ↦ A x + V x`, and prove closedness by showing the new graph norm is
equivalent to the old one using boundedness of `V`. -/
noncomputable def addBounded (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : E →L[𝕜] E) : ClosedOperator (𝕜 := 𝕜) (E := E) where
  domain := A.domain
  toLinearMap := A.toLinearMap + V.toLinearMap.domRestrict A.domain
  dense_domain := A.dense_domain
  closed_graph := by
    apply IsSeqClosed.isClosed
    rintro φ ⟨x, y⟩ hmem hlim
    choose xn hxn using hmem
    have hfst : (fun n => ((xn n : A.domain) : E)) = fun n => (φ n).1 := by
      funext n
      exact congrArg Prod.fst (hxn n)
    have hsnd :
        (fun n => A.toLinearMap (xn n) + V ((xn n : A.domain) : E)) =
          fun n => (φ n).2 := by
      funext n
      exact congrArg Prod.snd (hxn n)
    have hx : Tendsto (fun n => ((xn n : A.domain) : E)) atTop (𝓝 x) := by
      rw [hfst]
      exact hlim.fst_nhds
    have hsum : Tendsto
        (fun n => A.toLinearMap (xn n) + V ((xn n : A.domain) : E))
        atTop (𝓝 y) := by
      rw [hsnd]
      exact hlim.snd_nhds
    have hV : Tendsto (fun n => V ((xn n : A.domain) : E))
        atTop (𝓝 (V x)) :=
      (V.continuous.tendsto x).comp hx
    have hAseq : Tendsto (fun n => A.toLinearMap (xn n))
        atTop (𝓝 (y - V x)) := by
      simpa only [add_sub_cancel_right] using hsum.sub hV
    have hgraph : (x, y - V x) ∈
        Set.range (fun z : A.domain => ((z : E), A.toLinearMap z)) :=
      A.closed_graph.mem_of_tendsto (hx.prodMk_nhds hAseq)
        (Eventually.of_forall fun n => ⟨xn n, rfl⟩)
    rcases hgraph with ⟨z, hz⟩
    have hzx : (z : E) = x := congrArg Prod.fst hz
    have hzA : A.toLinearMap z = y - V x := congrArg Prod.snd hz
    refine ⟨z, ?_⟩
    ext
    · exact hzx
    · change A.toLinearMap z + V (z : E) = y
      rw [hzA, hzx]
      abel

omit [CompleteSpace E] in
/-- Adding a bounded operator does not change the domain -- which is the whole point of the
construction, and why bounded perturbation preserves closedness. -/
@[simp] theorem addBounded_domain (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : E →L[𝕜] E) : (A.addBounded V).domain = A.domain := rfl

omit [CompleteSpace E] in
/-- Adding a bounded operator acts pointwise. -/
@[simp] theorem addBounded_apply (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : E →L[𝕜] E) (x : (A.addBounded V).domain) :
    (A.addBounded V) x = A.toLinearMap x + V (x : E) := rfl

/-- Compatibility facade for relative boundedness over the canonical partial map. -/
abbrev RelativelyBounded (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : A.domain →ₗ[𝕜] E) (a b : ℝ) : Prop :=
  TauCeti.LinearPMap.RelativelyBounded A.toLinearPMap V a b

namespace RelativelyBounded

omit [CompleteSpace E] in
/-- The zero perturbation has zero relative bound. -/
theorem zero (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    RelativelyBounded A (0 : A.domain →ₗ[𝕜] E) 0 0 :=
  TauCeti.LinearPMap.RelativelyBounded.zero A.toLinearPMap

omit [CompleteSpace E] in
/-- Relative bounds may be weakened by increasing either coefficient. -/
theorem mono
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {V : A.domain →ₗ[𝕜] E} {a b a' b' : ℝ}
    (hV : RelativelyBounded A V a b)
    (haa' : a ≤ a') (hbb' : b ≤ b') :
    RelativelyBounded A V a' b' :=
  TauCeti.LinearPMap.RelativelyBounded.mono hV haa' hbb'

omit [CompleteSpace E] in
/-- Relative bounds add under addition of perturbations. -/
theorem add
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {V W : A.domain →ₗ[𝕜] E} {a b c d : ℝ}
    (hV : RelativelyBounded A V a b)
    (hW : RelativelyBounded A W c d) :
    RelativelyBounded A (V + W) (a + c) (b + d) :=
  TauCeti.LinearPMap.RelativelyBounded.add hV hW

omit [CompleteSpace E] in
/-- Relative bounds scale by the norm of the scalar. -/
theorem smul
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {V : A.domain →ₗ[𝕜] E} {a b : ℝ}
    (hV : RelativelyBounded A V a b) (c : 𝕜) :
    RelativelyBounded A (c • V) (‖c‖ * a) (‖c‖ * b) :=
  TauCeti.LinearPMap.RelativelyBounded.smul hV c

omit [CompleteSpace E] in
/-- Relative bounds are preserved by negation. -/
theorem neg
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {V : A.domain →ₗ[𝕜] E} {a b : ℝ}
    (hV : RelativelyBounded A V a b) :
    RelativelyBounded A (-V) a b :=
  TauCeti.LinearPMap.RelativelyBounded.neg hV

omit [CompleteSpace E] in
/-- Relative bounds add under subtraction of perturbations. -/
theorem sub
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {V W : A.domain →ₗ[𝕜] E} {a b c d : ℝ}
    (hV : RelativelyBounded A V a b)
    (hW : RelativelyBounded A W c d) :
    RelativelyBounded A (V - W) (a + c) (b + d) :=
  TauCeti.LinearPMap.RelativelyBounded.sub hV hW

omit [CompleteSpace E] in
/-- Restricting a bounded ambient operator to the domain gives relative bound
`(‖V‖, 0)`. -/
theorem domRestrict (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : E →L[𝕜] E) :
    RelativelyBounded A (V.toLinearMap.domRestrict A.domain) ‖V‖ 0 :=
  TauCeti.LinearPMap.RelativelyBounded.domRestrict A.toLinearPMap V

end RelativelyBounded

/-- Real resolvent set of a closed operator.  A real parameter belongs
to this set when the shifted operator has a bounded two-sided inverse: the
left inverse law is imposed on the operator domain, while the right inverse
law includes the domain witness for the image of the inverse. -/
abbrev realResolventSet
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Set ℝ :=
  TauCeti.LinearPMap.realResolventSet A.toLinearPMap

/-- Real spectrum of a closed operator, defined as the complement of the real
resolvent set.  For a self-adjoint complex operator this agrees definitionally
with the real slice of the Spectra resolvent. -/
abbrev realSpectrum
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Set ℝ :=
  TauCeti.LinearPMap.realSpectrum A.toLinearPMap

/-- Spectral-set separation for closed operators, possibly acting on
different Hilbert spaces.  The separation condition depends only on the two
real spectra, so requiring a common ambient space would be artificial and
would block the diagonal-block Riccati theory. -/
abbrev SpectralSetsSeparated
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : ClosedOperator (𝕜 := 𝕜) (E := F))
    (s t : Set ℝ) (d : ℝ) : Prop :=
  TauCeti.LinearPMap.SpectralSetsSeparated
    A.toLinearPMap B.toLinearPMap s t d

/-- Spectral-set separation is symmetric in the two operators. -/
theorem SpectralSetsSeparated.symm
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperator (𝕜 := 𝕜) (E := F)}
    {s t : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d) :
    SpectralSetsSeparated B A t s d :=
  TauCeti.LinearPMap.SpectralSetsSeparated.symm h

omit [CompleteSpace E] in
/-- Weakening the required gap preserves spectral-set separation. -/
theorem SpectralSetsSeparated.mono_gap
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperator (𝕜 := 𝕜) (E := F)}
    {s t : Set ℝ} {d e : ℝ}
    (h : SpectralSetsSeparated A B s t d) (hed : e ≤ d) :
    SpectralSetsSeparated A B s t e :=
  TauCeti.LinearPMap.SpectralSetsSeparated.mono_gap h hed

omit [CompleteSpace E] in
/-- Restricting either selected spectral set preserves separation. -/
theorem SpectralSetsSeparated.mono_sets
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperator (𝕜 := 𝕜) (E := F)}
    {s s' t t' : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d)
    (hs : s' ⊆ s) (ht : t' ⊆ t) :
    SpectralSetsSeparated A B s' t' d :=
  TauCeti.LinearPMap.SpectralSetsSeparated.mono_sets h hs ht
end ClosedOperator
end DavisKahanExt
end TauCeti