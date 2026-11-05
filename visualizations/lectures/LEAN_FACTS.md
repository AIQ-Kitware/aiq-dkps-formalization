# Lean companions for the lectures

Each lesson states its mathematical facts, then gives each corresponding Lean
statement its own card. The symbolic formula stays beside the code. A short
plain-language scope statement names the common assumptions; the complete Lean
context, imports, and examples remain in the copyable `facts.lean` companion.
The renderer reads each example directly from that file rather than maintaining
a separate transcription. JuliaMono supplies consistent mathematical glyphs;
Lean 4 syntax is colored, and the library-proof application is highlighted in
green beneath the statement. `DKVIS_LEAN_FONT` selects another installed font.

The core is followed by an explicitly optional numerical bonus slide, then the
two multiple-choice study questions. Numerical details are not needed to follow
the core argument or answer its conceptual questions.

| Lecture | Companion | Library declarations used |
| --- | --- | --- |
| Projections | [facts.lean](001000_projections/facts.lean) | Mathlib `Submodule.starProjection_add_starProjection_orthogonal`; Tau Ceti `Submodule.offDiagBlock_eq_zero_iff` |
| Singular-value norms | [facts.lean](002000_singular_norms/facts.lean) | Tau Ceti `schatten_apply_of_ne_top` in `TauCeti.UnitarilyInvariantSeminorm`, and `LinearMap.singularValues_linearIsometryEquiv_comp` / `singularValues_comp_linearIsometryEquiv` |
| Matrix exponential | [facts.lean](002500_matrix_exponential/facts.lean) | Tau Ceti `ContinuousLinearMap.exp_add_smul`; Mathlib `NormedSpace.exp_mem_unitary_of_mem_skewAdjoint` and `Commute.exp_left` |
| Variations | [facts.lean](003000_variations/facts.lean) | Mathlib `IsLocalMin.hasDerivAt_eq_zero` and `Matrix.trace_conjTranspose_mul_self_eq_zero_iff` |
| Min-max | [facts.lean](002666_minmax/facts.lean) | Tau Ceti `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner` and `abs_eigenvalue_sub_eigenvalue_le_norm` |
| Polar decomposition | [facts.lean](002833_polar/facts.lean) | Tau Ceti `LinearMap.polarFactor_comp_operatorAbs` and `norm_polarFactor_apply` |
| Sylvester | [facts.lean](003500_sylvester/facts.lean) | Tau Ceti `ContinuousLinearMap.sylvester_apply` and `mul_norm_le_norm_sylvester_apply_of_le_re_inner_of_re_inner_le` |

These are applications of existing APIs, not new mathematical declarations or
additional Davis–Kahan completion obligations. Attribution identifies the
library supplying the declaration, not a claim that every declaration originated
in this project. The Tau Ceti names and signatures above were inspected at the
repository's pinned revision `5f78b5307b932e1e2ac7848dc7d4fedc6a52d6c1`.
Mathlib is pinned at `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`.

## Reading the code

- A `Submodule` is a linear subspace. `K.starProjection` maps the ambient space
  to itself; `K.HasOrthogonalProjection` supplies the projection. The splitting
  example works without assuming finite dimension.
- `K.offDiagBlock T` is the sum of the two crossing blocks relative to
  `K` and its orthogonal complement. Its zero criterion is an equivalence.
- `schatten` packages a unitarily invariant seminorm. Tau Ceti separately proves
  that its kernel is zero. The example uses a finite exponent at least one;
  `ℝ≥0∞` allows infinity, `Fact (1 ≤ p)` supplies the lower bound, and `hp`
  excludes infinity. `singularValues` is a sequence with a zero tail; its finite
  sum agrees with the usual finite singular-value list.
- `E →ₗ[ℝ] E` means a real linear map. `E →L[ℝ] E` means a bounded real linear
  map. Multiplication of endomorphisms and `.comp` mean composition.
  `E ≃ₗᵢ[ℝ] E` is an isometric linear isomorphism. In finite real orthonormal
  coordinates it is an orthogonal matrix.
- `skewAdjoint` means the adjoint is the negative of the operator. Real
  `unitary` means orthogonal. The local rational-algebra instance in the
  exponential companion supplies scalar structure for the general exponential
  API; it adds no mathematical hypothesis on the Hilbert space.
- The variations examples certify the scalar stationarity rule and the
  finite-matrix positivity test. They do not by themselves certify feasibility
  of a curve or the objective's derivative formula. Those connections are
  explained in the preceding slides; the complete matching argument also needs
  them. Real transpose is obtained from conjugate transpose by simplifying
  trivial conjugation.

## Check the companions

From the repository root, with the pinned dependencies built:

```bash
lake env lean visualizations/lectures/001000_projections/facts.lean
lake env lean visualizations/lectures/002000_singular_norms/facts.lean
lake env lean visualizations/lectures/002500_matrix_exponential/facts.lean
lake env lean visualizations/lectures/003000_variations/facts.lean
```

Validation in the authoring environment used the available Lean 4.36.0-rc1
compiled dependency cache. The projection, norm and variations companions passed
directly. The pinned Tau Ceti revision moves the flow theorem from
`TauCeti.exp_add_smul` to `ContinuousLinearMap.exp_add_smul`; the exponential
companion uses the current name. Its check compiled the exact pinned flow theorem
in an ignored scratch module, then checked the companion against it. All four
sets of examples were accepted with this cache. A clean check with the root's
Lean 4.36.0-rc2 toolchain still requires refreshing the stale dependency cache;
the commands above are the intended normal validation. The pin and toolchain
were not changed for the lectures.

The three operator-lecture companions were inspected against accepted source at
`85f3eb5579df5ca44ba8cd0921d614b41ab72174`. Their local compiler check uses
the same available rc1 dependency cache described above; it is not a clean
root-toolchain rebuild. Their provenance is detailed in the
[operator topic guide](../dkvis/learning/operators/README.md).

The November 5 typography revision reflowed the examples and rechecked all seven
companions against the available rc1 cache. The exponential check again supplied
the exact current-pin flow proof in an ignored scratch file, since the cache
still exposes its older namespace. This does not claim a clean rc2 rebuild.
The singular-value invariance statement uses a prefix application to keep lines
short; the variations trace proof uses ordinary simplification of real conjugation.
