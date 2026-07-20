/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.SpectralTheory.Compatibility
import Mathlib.Analysis.InnerProductSpace.LinearPMap

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

namespace ForMathlib
namespace DavisKahanExt

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

instance : CoeFun (ClosedOperator (𝕜 := 𝕜) (E := E))
    (fun A => A.domain → E) where
  coe A := A.apply

/-- The canonical Mathlib partial-linear-map view of a closed operator. -/
def toLinearPMap (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : E →ₗ.[𝕜] E where
  domain := A.domain
  toFun := A.toLinearMap

omit [CompleteSpace E] in
@[simp] theorem toLinearPMap_domain
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.toLinearPMap.domain = A.domain := rfl

omit [CompleteSpace E] in
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

/-- Two closed operators have the same operator domain. -/
def SameDomain (A B : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  A.domain = B.domain

omit [CompleteSpace E] in
/-- Equality of domains is reflexive. -/
@[refl] theorem SameDomain.refl (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.SameDomain A := rfl

omit [CompleteSpace E] in
/-- Equality of domains is symmetric. -/
@[symm] theorem SameDomain.symm {A B : ClosedOperator (𝕜 := 𝕜) (E := E)}
    (h : A.SameDomain B) : B.SameDomain A := Eq.symm h

omit [CompleteSpace E] in
/-- Equality of domains is transitive. -/
@[trans] theorem SameDomain.trans {A B C : ClosedOperator (𝕜 := 𝕜) (E := E)}
    (hAB : A.SameDomain B) (hBC : B.SameDomain C) : A.SameDomain C :=
  Eq.trans hAB hBC

/-- A bounded map sends the domain of `B` into the domain of `A`. -/
def MapsDomainTo
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : ClosedOperator (𝕜 := 𝕜) (E := F))
    (X : F →L[𝕜] E) : Prop :=
  ∀ x : B.domain, X (x : F) ∈ A.domain

/-- The identity map preserves every operator domain. -/
theorem MapsDomainTo.id (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.MapsDomainTo A (ContinuousLinearMap.id 𝕜 E) := by
  intro x
  simp

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
    A.MapsDomainTo C (X ∘L Y) := by
  intro z
  exact hX ⟨Y (z : G), hY z⟩

/-- A linear map defined on a dense operator domain has a bounded extension to
the ambient Hilbert space. -/
structure BoundedExtension
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (D : Submodule 𝕜 F) (T : D →ₗ[𝕜] E) where
  operator : F →L[𝕜] E
  agrees : ∀ x : D, operator (x : F) = T x

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
@[simp] theorem ofBounded_domain (A : E →L[𝕜] E) :
    (ofBounded A).domain = ⊤ := rfl

omit [CompleteSpace E] in
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

/-- Extension relation for partially defined operators. -/
def Extends (A B : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  ∃ hdom : A.domain ≤ B.domain,
    ∀ x : A.domain,
      B.toLinearMap ⟨(x : E), hdom x.property⟩ = A.toLinearMap x

omit [CompleteSpace E] in
/-- Every closed operator extends itself. -/
@[refl] theorem Extends.refl (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    A.Extends A := by
  refine ⟨le_rfl, ?_⟩
  intro x
  rfl

omit [CompleteSpace E] in
/-- Extension of closed operators is transitive. -/
@[trans] theorem Extends.trans {A B C : ClosedOperator (𝕜 := 𝕜) (E := E)}
    (hAB : A.Extends B) (hBC : B.Extends C) : A.Extends C := by
  rcases hAB with ⟨hdomAB, hactAB⟩
  rcases hBC with ⟨hdomBC, hactBC⟩
  refine ⟨hdomAB.trans hdomBC, ?_⟩
  intro x
  calc
    C.toLinearMap ⟨(x : E), hdomBC (hdomAB x.property)⟩ =
        B.toLinearMap ⟨(x : E), hdomAB x.property⟩ :=
      hactBC ⟨(x : E), hdomAB x.property⟩
    _ = A.toLinearMap x := hactAB x

/-- Symmetric closed operator. -/
def IsSymmetric (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Prop :=
  ∀ x y : A.domain, ⟪A.toLinearMap x, (y : E)⟫_𝕜 = ⟪(x : E), A.toLinearMap y⟫_𝕜
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

/-- Graph norm. -/
noncomputable def graphNorm (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : ℝ :=
  Real.sqrt (‖(x : E)‖ ^ 2 + ‖A.toLinearMap x‖ ^ 2)

omit [CompleteSpace E] in
/-- The graph norm is nonnegative. -/
theorem graphNorm_nonneg (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : 0 ≤ A.graphNorm x :=
  Real.sqrt_nonneg _

omit [CompleteSpace E] in
/-- Squaring the graph norm recovers the defining sum of squares. -/
theorem graphNorm_sq (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) :
    A.graphNorm x ^ 2 = ‖(x : E)‖ ^ 2 + ‖A.toLinearMap x‖ ^ 2 := by
  unfold graphNorm
  exact Real.sq_sqrt (by positivity)

omit [CompleteSpace E] in
/-- The ambient norm is controlled by the graph norm. -/
theorem norm_coe_le_graphNorm (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : ‖(x : E)‖ ≤ A.graphNorm x := by
  rw [graphNorm]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖A.toLinearMap x‖])

omit [CompleteSpace E] in
/-- The operator-value norm is controlled by the graph norm. -/
theorem norm_apply_le_graphNorm (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (x : A.domain) : ‖A.toLinearMap x‖ ≤ A.graphNorm x := by
  rw [graphNorm]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖(x : E)‖])

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
@[simp] theorem addBounded_domain (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : E →L[𝕜] E) : (A.addBounded V).domain = A.domain := rfl

omit [CompleteSpace E] in
@[simp] theorem addBounded_apply (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : E →L[𝕜] E) (x : (A.addBounded V).domain) :
    (A.addBounded V) x = A.toLinearMap x + V (x : E) := rfl

/-- Relative boundedness with respect to a closed operator. -/
def RelativelyBounded (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : A.domain →ₗ[𝕜] E) (a b : ℝ) : Prop :=
  ∀ x, ‖V x‖ ≤ a * ‖(x : E)‖ + b * ‖A.toLinearMap x‖

namespace RelativelyBounded

omit [CompleteSpace E] in
/-- The zero perturbation has zero relative bound. -/
theorem zero (A : ClosedOperator (𝕜 := 𝕜) (E := E)) :
    RelativelyBounded A (0 : A.domain →ₗ[𝕜] E) 0 0 := by
  intro x
  simp

omit [CompleteSpace E] in
/-- Relative bounds may be weakened by increasing either coefficient. -/
theorem mono
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {V : A.domain →ₗ[𝕜] E} {a b a' b' : ℝ}
    (hV : RelativelyBounded A V a b)
    (haa' : a ≤ a') (hbb' : b ≤ b') :
    RelativelyBounded A V a' b' := by
  intro x
  exact (hV x).trans <| add_le_add
    (mul_le_mul_of_nonneg_right haa' (norm_nonneg (x : E)))
    (mul_le_mul_of_nonneg_right hbb' (norm_nonneg (A.toLinearMap x)))

omit [CompleteSpace E] in
/-- Relative bounds add under addition of perturbations. -/
theorem add
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {V W : A.domain →ₗ[𝕜] E} {a b c d : ℝ}
    (hV : RelativelyBounded A V a b)
    (hW : RelativelyBounded A W c d) :
    RelativelyBounded A (V + W) (a + c) (b + d) := by
  intro x
  calc
    ‖(V + W) x‖ ≤ ‖V x‖ + ‖W x‖ := norm_add_le _ _
    _ ≤ (a * ‖(x : E)‖ + b * ‖A.toLinearMap x‖) +
        (c * ‖(x : E)‖ + d * ‖A.toLinearMap x‖) :=
      add_le_add (hV x) (hW x)
    _ = (a + c) * ‖(x : E)‖ + (b + d) * ‖A.toLinearMap x‖ := by ring

omit [CompleteSpace E] in
/-- Relative bounds scale by the norm of the scalar. -/
theorem smul
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {V : A.domain →ₗ[𝕜] E} {a b : ℝ}
    (hV : RelativelyBounded A V a b) (c : 𝕜) :
    RelativelyBounded A (c • V) (‖c‖ * a) (‖c‖ * b) := by
  intro x
  rw [LinearMap.smul_apply, norm_smul]
  calc
    ‖c‖ * ‖V x‖ ≤ ‖c‖ *
        (a * ‖(x : E)‖ + b * ‖A.toLinearMap x‖) :=
      mul_le_mul_of_nonneg_left (hV x) (norm_nonneg c)
    _ = (‖c‖ * a) * ‖(x : E)‖ +
        (‖c‖ * b) * ‖A.toLinearMap x‖ := by ring

omit [CompleteSpace E] in
/-- Relative bounds are preserved by negation. -/
theorem neg
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {V : A.domain →ₗ[𝕜] E} {a b : ℝ}
    (hV : RelativelyBounded A V a b) :
    RelativelyBounded A (-V) a b := by
  simpa using hV.smul (-1 : 𝕜)

omit [CompleteSpace E] in
/-- Relative bounds add under subtraction of perturbations. -/
theorem sub
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {V W : A.domain →ₗ[𝕜] E} {a b c d : ℝ}
    (hV : RelativelyBounded A V a b)
    (hW : RelativelyBounded A W c d) :
    RelativelyBounded A (V - W) (a + c) (b + d) := by
  simpa [sub_eq_add_neg] using hV.add hW.neg

omit [CompleteSpace E] in
/-- Restricting a bounded ambient operator to the domain gives relative bound
`(‖V‖, 0)`. -/
theorem domRestrict (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (V : E →L[𝕜] E) :
    RelativelyBounded A (V.toLinearMap.domRestrict A.domain) ‖V‖ 0 := by
  intro x
  simpa using V.le_opNorm (x : E)

end RelativelyBounded

/-- Real resolvent set of a closed operator.  A real parameter belongs
to this set when the shifted operator has a bounded two-sided inverse: the
left inverse law is imposed on the operator domain, while the right inverse
law includes the domain witness for the image of the inverse. -/
def realResolventSet
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Set ℝ :=
  { lam : ℝ | ∃ R : E →L[𝕜] E,
      (∀ x : A.domain,
        R (A.toLinearMap x - (lam : 𝕜) • (x : E)) = (x : E)) ∧
      (∀ y : E, ∃ h : R y ∈ A.domain,
        A.toLinearMap ⟨R y, h⟩ - (lam : 𝕜) • R y = y) }

/-- Real spectrum of a closed operator, defined as the complement of the real
resolvent set.  For a self-adjoint complex operator this agrees definitionally
with the real slice of the Spectra resolvent. -/
def realSpectrum
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Set ℝ :=
  (realResolventSet A)ᶜ

/-- Spectral-set separation for closed operators, possibly acting on
different Hilbert spaces.  The separation condition depends only on the two
real spectra, so requiring a common ambient space would be artificial and
would block the diagonal-block Riccati theory. -/
def SpectralSetsSeparated
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    (A : ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : ClosedOperator (𝕜 := 𝕜) (E := F))
    (s t : Set ℝ) (d : ℝ) : Prop :=
  ∀ a ∈ A.realSpectrum, a ∈ s →
    ∀ b ∈ B.realSpectrum, b ∈ t → d ≤ |a - b|

/-- Spectral-set separation is symmetric in the two operators. -/
theorem SpectralSetsSeparated.symm
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperator (𝕜 := 𝕜) (E := F)}
    {s t : Set ℝ} {d : ℝ}
    (h : SpectralSetsSeparated A B s t d) :
    SpectralSetsSeparated B A t s d := by
  intro b hb ht a ha hs
  simpa [abs_sub_comm] using h a ha hs b hb ht

omit [CompleteSpace E] in
/-- Weakening the required gap preserves spectral-set separation. -/
theorem SpectralSetsSeparated.mono_gap
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [CompleteSpace F]
    {A : ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : ClosedOperator (𝕜 := 𝕜) (E := F)}
    {s t : Set ℝ} {d e : ℝ}
    (h : SpectralSetsSeparated A B s t d) (hed : e ≤ d) :
    SpectralSetsSeparated A B s t e := by
  intro a ha hs b hb ht
  exact hed.trans (h a ha hs b hb ht)

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
    SpectralSetsSeparated A B s' t' d := by
  intro a ha has' b hb hbt'
  exact h a ha (hs has') b hb (ht hbt')
end ClosedOperator
end DavisKahanExt
end ForMathlib
