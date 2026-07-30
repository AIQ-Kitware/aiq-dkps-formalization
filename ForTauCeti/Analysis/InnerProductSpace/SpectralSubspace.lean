/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForTauCeti.Analysis.InnerProductSpace.CourantFischer
import ForTauCeti.Analysis.InnerProductSpace.ProjectionGap

/-!
# Finite-dimensional spectral subspaces

Restricted spectra, reducing subspaces, canonical spectral projectors, and the
quadratic-form bridges used by finite Davis--Kahan theorems.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Core/SpectralSubspace.lean`
before the dependency-closed base of the sin-Θ core moved into the staging
layer.  Statements, proofs, signatures and namespaces are
unchanged; the declarations already lived in `TauCeti.DavisKahan*`, so the move
was a path change and an import repoint and nothing else.

The move became possible only once Y3(b2) took the `ForMathlib`
inner-product-space component into `ForTauCeti`: before that this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.
-/

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
/-- A subspace is **invariant** under an operator when the operator maps it into
itself.

Named for what it says.  It was called `Reduces`, which collided with
`ContinuousLinearMap.Reduces` — a genuinely *stronger* predicate requiring
`Uᗮ` to be invariant too — so one name meant two things in one library and a
reader meeting `IsInvariant A U` in a docstring could not tell which.  For a
symmetric operator the two coincide, and `isInvariant_orthogonal_of_isSymmetric`
is what supplies that; but the implication is one-directional in general, which
is exactly why the names had to be separated. -/
def IsInvariant (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Prop :=
  ∀ x ∈ U, A x ∈ U

/-- A nonzero eigenvector of a symmetric operator at a real eigenvalue. -/
def IsEigenvectorAt (A : E →ₗ[𝕜] E) (lam : ℝ) (x : E) : Prop :=
  x ≠ 0 ∧ A x = (lam : 𝕜) • x

/-- The finite-dimensional point spectrum of `A` carried by `U`.

For symmetric operators this is the spectrum of the restriction to `U` once
`U` reduces `A`.  The definition avoids exposing a choice of restricted
coordinate space in theorem statements. -/
def restrictedSpectrum (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) : Set ℝ :=
  {lam | ∃ x, x ∈ U ∧ IsEigenvectorAt A lam x}

/-- Every eigenvalue of `A` carried by `U` lies in `Ω`. -/
def SpectrumIn (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (Ω : Set ℝ) : Prop :=
  restrictedSpectrum A U ⊆ Ω

/-- Canonical finite-dimensional spectral subspace selected by a real set. -/
noncomputable def spectralSubspace (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 {x | ∃ lam ∈ Ω, IsEigenvectorAt A lam x}

/-- Canonical orthogonal spectral projector. -/
noncomputable def spectralProjection (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    E →ₗ[𝕜] E :=
  ((spectralSubspace A Ω).starProjection : E →L[𝕜] E)

/-- The orthogonal projector onto a finite-dimensional subspace, as a linear
map. -/
noncomputable def projection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    E →ₗ[𝕜] E :=
  ((U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)

/-- The complementary projector. -/
noncomputable def complementaryProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  projection Uᗮ

omit [FiniteDimensional 𝕜 E] in
/-- An orthogonal projector is symmetric. -/
theorem projection_isSymmetric (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : (projection U).IsSymmetric :=
  U.starProjection_isSymmetric

/-- An orthogonal projector is its own adjoint. -/
@[simp] theorem projection_adjoint (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    (projection U).adjoint = projection U :=
  (projection_isSymmetric U).adjoint_eq

omit [FiniteDimensional 𝕜 E] in
/-- A symmetric operator leaves the orthogonal complement of an invariant
subspace invariant.
-/
theorem isInvariant_orthogonal_of_isSymmetric {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E} (hU : IsInvariant A U) :
    IsInvariant A Uᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [← hA u x]
  exact Submodule.inner_right_of_mem_orthogonal (hU u hu) hx

omit [FiniteDimensional 𝕜 E] in
/-- The canonical spectral subspace reduces its operator.  Symmetry is not
needed for this algebraic fact; it is needed later for orthogonal reduction and
for completeness of the real eigenvector decomposition.
-/
theorem isInvariant_spectralSubspace (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    IsInvariant A (spectralSubspace A Ω) := by
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨lam, hlam, hy⟩
    rw [hy.2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨lam, hlam, hy⟩)
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using (spectralSubspace A Ω).add_mem hx hy
  · intro c x _ hx
    simpa only [map_smul] using (spectralSubspace A Ω).smul_mem c hx

/-! ### Restriction to an invariant subspace and the restricted-spectrum bridge

These give the concrete restriction `A.restrict hU : U →ₗ[𝕜] U` of an operator to
an invariant subspace and identify its full point spectrum with the `U`-carried
point spectrum of `A`.  This is the bridge used to discharge the spectral
hypotheses of the residual/perturbation `sin Θ` theorems on the subtype. -/

omit [FiniteDimensional 𝕜 E] in
/-- The restriction of a symmetric operator to an invariant subspace is
symmetric (mathlib's `LinearMap.IsSymmetric.restrict_invariant`, restated for the
`IsInvariant` predicate). -/
theorem isSymmetric_restrict {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U) :
    (A.restrict hU).IsSymmetric :=
  hA.restrict_invariant hU

omit [FiniteDimensional 𝕜 E] in
/-- **The restricted-spectrum bridge.**  The point spectrum of the restriction
`A.restrict hU : U →ₗ[𝕜] U` (over the whole `⊤`) equals the `U`-carried point
spectrum of `A`.  Eigenvectors transport across the subtype coercion. -/
theorem restrictedSpectrum_restrict (A : E →ₗ[𝕜] E)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U) :
    restrictedSpectrum (A.restrict hU) ⊤ = restrictedSpectrum A U := by
  ext lam
  constructor
  · rintro ⟨x, -, hx0, hxEig⟩
    refine ⟨(x : E), x.2, fun hx => hx0 (Subtype.ext hx), ?_⟩
    have h := congrArg (Subtype.val) hxEig
    rwa [LinearMap.coe_restrict_apply, Submodule.coe_smul] at h
  · rintro ⟨x, hxU, hx0, hxEig⟩
    refine ⟨⟨x, hxU⟩, Submodule.mem_top, fun hxu => hx0 (congrArg Subtype.val hxu), ?_⟩
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply, Submodule.coe_smul]
    exact hxEig

omit [FiniteDimensional 𝕜 E] in
/-- The containment form of the restricted-spectrum bridge: `A.restrict hU` has
spectrum in `s` iff `A` carries spectrum in `s` on `U`. -/
theorem spectrumIn_restrict_iff (A : E →ₗ[𝕜] E)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U) (s : Set ℝ) :
    SpectrumIn (A.restrict hU) ⊤ s ↔ SpectrumIn A U s := by
  unfold SpectrumIn
  rw [restrictedSpectrum_restrict]

omit [FiniteDimensional 𝕜 E] in
/-- **A symmetric operator commutes with the projection onto a reducing
subspace.**  For `A` symmetric and `U` an `A`-invariant subspace (so `Uᗮ` is
invariant too), `P_U (A x) = A (P_U x)`. -/
theorem projection_apply_comm_of_isInvariant {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : IsInvariant A U) (x : E) :
    projection U (A x) = A (projection U x) := by
  have hUperp : IsInvariant A Uᗮ := isInvariant_orthogonal_of_isSymmetric hA hU
  have hpx : U.starProjection x ∈ U := U.starProjection_apply_mem x
  have hrest : x - U.starProjection x ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hApx : A (U.starProjection x) ∈ U := hU _ hpx
  have hArest : A (x - U.starProjection x) ∈ Uᗮ := hUperp _ hrest
  have hsplit : A x = A (U.starProjection x) + A (x - U.starProjection x) := by
    rw [← map_add]; congr 1; abel
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change U.starProjection (A x) = A (U.starProjection x)
  rw [hsplit, map_add, U.starProjection_eq_self_iff.mpr hApx,
    (Submodule.starProjection_apply_eq_zero_iff U).mpr hArest, add_zero]

omit [FiniteDimensional 𝕜 E] in
/-- The complementary projection onto `Uᗮ` also commutes with `A` when `A` is
symmetric and `U` reduces `A`. -/
theorem complementaryProjection_apply_comm_of_isInvariant {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : IsInvariant A U) (x : E) :
    complementaryProjection U (A x) = A (complementaryProjection U x) :=
  projection_apply_comm_of_isInvariant hA (isInvariant_orthogonal_of_isSymmetric hA hU) x

/-! ### Spectral gap ⟹ quadratic-form coercivity bridge

These convert the abstract eigenvalue-set hypotheses (`SpectrumIn A U s`) into the
quadratic-form bounds `re ⟪A x, x⟫ ≤ c ‖x‖²` (or `≥`) that the dimension-free
operator-norm Sylvester/`sin Θ` machinery consumes.  This is the point where
finite-dimensional spectral decomposition (an eigenbasis of the restriction) is
genuinely used. -/

/-- If every eigenvalue of a symmetric `T` is `≤ c`, the quadratic form is
bounded above by `c ‖·‖²` (diagonalization: `∑ λᵢ ‖repr xᵢ‖² ≤ c ∑ ‖repr xᵢ‖²`). -/
theorem re_inner_le_of_forall_eigenvalue_le {n : ℕ} {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {c : ℝ}
    (hc : ∀ i, hT.eigenvalues hn i ≤ c) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  refine LinearMap.IsSymmetric.re_inner_apply_self_le_of_mem_spanIndices hT hn (s := Set.univ)
    (fun i _ => hc i) ?_
  have htop : (hT.eigenvectorBasis hn).spanIndices (Set.univ : Set (Fin n)) = ⊤ := by
    rw [OrthonormalBasis.spanIndices, eq_top_iff,
      ← (hT.eigenvectorBasis hn).toBasis.span_eq]
    exact Submodule.span_mono (by rintro y ⟨i, rfl⟩; exact ⟨i, trivial, rfl⟩)
  rw [htop]; exact Submodule.mem_top

/-- Dual: if every eigenvalue of a symmetric `T` is `≥ c`, the quadratic form is
bounded below by `c ‖·‖²`. -/
theorem le_re_inner_of_forall_le_eigenvalue {n : ℕ} {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {c : ℝ}
    (hc : ∀ i, c ≤ hT.eigenvalues hn i) (x : E) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  refine LinearMap.IsSymmetric.le_re_inner_apply_self_of_mem_spanIndices hT hn (s := Set.univ)
    (fun i _ => hc i) ?_
  have htop : (hT.eigenvectorBasis hn).spanIndices (Set.univ : Set (Fin n)) = ⊤ := by
    rw [OrthonormalBasis.spanIndices, eq_top_iff,
      ← (hT.eigenvectorBasis hn).toBasis.span_eq]
    exact Submodule.span_mono (by rintro y ⟨i, rfl⟩; exact ⟨i, trivial, rfl⟩)
  rw [htop]; exact Submodule.mem_top

/-- **The spectral-gap coercivity bridge (upper).**  If `A` is symmetric, `U`
reduces `A`, and the `U`-carried spectrum lies in `Set.Iic c`, then the quadratic
form of `A` is bounded above by `c ‖·‖²` on `U`. -/
theorem re_inner_le_of_spectrumIn {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U) {c : ℝ}
    (hspec : SpectrumIn A U (Set.Iic c)) {x : E} (hx : x ∈ U) :
    RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  have hA'sym : (A.restrict hU).IsSymmetric := isSymmetric_restrict hA hU
  have hev : ∀ i, hA'sym.eigenvalues rfl i ≤ c := fun i => by
    have hmem : hA'sym.eigenvalues rfl i ∈ restrictedSpectrum (A.restrict hU) ⊤ :=
      ⟨hA'sym.eigenvectorBasis rfl i, Submodule.mem_top,
        (hA'sym.eigenvectorBasis rfl).orthonormal.ne_zero i,
        hA'sym.apply_eigenvectorBasis rfl i⟩
    rw [restrictedSpectrum_restrict] at hmem
    exact hspec hmem
  have hquad := re_inner_le_of_forall_eigenvalue_le hA'sym rfl hev ⟨x, hx⟩
  rw [Submodule.coe_inner, LinearMap.coe_restrict_apply] at hquad
  exact hquad

/-- **The spectral-gap coercivity bridge (lower).**  If `A` is symmetric, `U`
reduces `A`, and the `U`-carried spectrum lies in `Set.Ici c`, then the quadratic
form of `A` is bounded below by `c ‖·‖²` on `U`. -/
theorem le_re_inner_of_spectrumIn {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} (hU : IsInvariant A U) {c : ℝ}
    (hspec : SpectrumIn A U (Set.Ici c)) {x : E} (hx : x ∈ U) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜 := by
  have hA'sym : (A.restrict hU).IsSymmetric := isSymmetric_restrict hA hU
  have hev : ∀ i, c ≤ hA'sym.eigenvalues rfl i := fun i => by
    have hmem : hA'sym.eigenvalues rfl i ∈ restrictedSpectrum (A.restrict hU) ⊤ :=
      ⟨hA'sym.eigenvectorBasis rfl i, Submodule.mem_top,
        (hA'sym.eigenvectorBasis rfl).orthonormal.ne_zero i,
        hA'sym.apply_eigenvectorBasis rfl i⟩
    rw [restrictedSpectrum_restrict] at hmem
    exact hspec hmem
  have hquad := le_re_inner_of_forall_le_eigenvalue hA'sym rfl hev ⟨x, hx⟩
  rw [Submodule.coe_inner, LinearMap.coe_restrict_apply] at hquad
  exact hquad

/-- The canonical projector has the expected range.
-/
theorem range_spectralProjection (A : E →ₗ[𝕜] E) (Ω : Set ℝ) :
    LinearMap.range (spectralProjection A Ω) = spectralSubspace A Ω := by
  exact Submodule.range_starProjection (spectralSubspace A Ω)

omit [FiniteDimensional 𝕜 E] in
/-- Spectral selection is independent of the chosen eigenbasis.
-/
theorem spectralSubspace_eq_span_eigenvectors (A : E →ₗ[𝕜] E)
    (Ω : Set ℝ) :
    spectralSubspace A Ω =
      Submodule.span 𝕜 {x | ∃ lam ∈ Ω, IsEigenvectorAt A lam x} :=
  rfl


end TauCeti
