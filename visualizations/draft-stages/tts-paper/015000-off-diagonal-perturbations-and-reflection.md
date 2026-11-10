# 015000 — Off-diagonal perturbations and reflection

**Track:** G3 audio paper track. **Draft:** adapted from G2 lecture 114000. **Section:** reflection-selection. **Audience:** prior linear algebra and basic analysis.

<!-- BEGIN SPOKEN LECTURE -->

# Off-diagonal perturbations and block reflection

Let T be self-adjoint, with a reducing subspace U and a spectral gap between its two diagonal blocks. Perturb T to S and compare U with a reducing subspace of S. A useful tool is reflection through a subspace: it preserves the diagonal blocks of an operator and reverses the off-diagonal blocks. This elementary symmetry explains why perturbation estimates involving twice the principal angles arise.

We will derive this identity entirely from the two-by-two block matrix of an orthogonal splitting.

## Split the ambient space into two components

Let H be a real or complex Hilbert space, and let U be a closed subspace. Write P for orthogonal projection onto U, and Q for the complementary projection, identity minus P.

Relative to the orthogonal decomposition H equals U plus U perpendicular, every bounded operator T has four blocks. The upper-left block sends U into U; the lower-right sends U perpendicular into itself; and the two off-diagonal blocks cross between the spaces.

Suppose T is self-adjoint and U is reducing for T. Then the off-diagonal blocks vanish. We may write T as a diagonal block matrix with A plus on U and A minus on U perpendicular.

The source's two-block gap hypothesis says the quadratic form of A plus is at least b times squared length, while the form of A minus is at most a times squared length, where b is greater than a. The gap is b minus a.

We have not assumed A plus or A minus is a scalar matrix. Each block may have many eigenvalues. Only the uniform form inequalities matter.

## Define the reflection

The reflection through U is J equal to P minus Q, or equivalently twice P minus the identity.

It acts as plus one on U and minus one on U perpendicular. Because P and Q are orthogonal projections, J is self-adjoint, J squared is the identity, and J preserves all lengths. Thus J is a unitary or orthogonal operator.

In the two-by-two block picture, J is diagonal with entries plus identity and minus identity.

Conjugate T by J. Its upper-left block is unchanged; its lower-right block is unchanged; and each off-diagonal block changes sign. This is immediate from multiplying by the signs on the left and right.

For a general T, subtracting T from J T J therefore removes both diagonal blocks and doubles the negative of the off-diagonal blocks.

## Define an off-diagonal perturbation

Let S equal T plus H, with H self-adjoint. We call H off-diagonal with respect to U when its two diagonal compressions vanish: P H P equals zero and Q H Q equals zero.

Then H maps U into its perpendicular complement and maps that complement back into U. Its matrix has zero diagonal blocks and off-diagonal blocks K and K adjoint.

Conjugation gives J H J equals negative H. We say H anticommutes with J, because J H equals negative H J.

This identity is stronger than saying H has small norm. It is an exact structural restriction. A perturbation can be arbitrarily large and still be off-diagonal.

Because T is block diagonal, J T J equals T. Consequently J S J equals T minus H, while S equals T plus H. Their difference is negative two H. In every unitarily invariant norm, its size is precisely twice the size of H.

There is another useful choice of reflection: the one through a reducing subspace of the perturbed operator S. That reflection gives a bound by twice the perturbation norm without requiring H itself to be off-diagonal.

## Verify everything in two dimensions

Take U to be the horizontal axis. Let T be diagonal with entries three and negative one. The quadratic form gap between the two blocks is four.

Let H have zero diagonal entries and equal off-diagonal entries h. Then S has rows three, h and h, negative one.

The reflection J is diagonal with entries one and negative one. Multiplying J S J gives a matrix with the same diagonal entries three and negative one, but off-diagonal entries negative h.

Subtract S, and the result has zero diagonal entries and off-diagonal entries negative two h. Its operator norm is two times the absolute value of h.

If h equals zero, the original subspace U remains invariant. If h is nonzero, the new eigenvectors tilt away from the coordinate axes even though the perturbation has zero diagonal compressions.

## Why this structure affects the spectrum

Set c equal to the midpoint between a and b. Consider J multiplied by T minus c times the identity.

On U, both J and T minus c are positive in the sense needed for the quadratic form, because T is at least b. On U perpendicular, both factors change sign: J is negative, and T minus c is at most a minus c, a negative number. Their product is again positive.

More precisely, the real part of the inner product of J times T minus c with a vector is at least half the gap times the squared length of that vector.

Now add the off-diagonal perturbation H. Since H anticommutes with self-adjoint J, the product J H is skew-adjoint. Its quadratic form has zero real part.

Therefore the same positive lower bound holds for the real part of J times S minus c. The off-diagonal perturbation cannot cancel the positive real part that comes from the diagonal block gap.

This observation is the starting point for spectral repulsion. For every real point strictly between a and b, we can repeat the midpoint argument with that point as the center and obtain a positive lower bound. In finite dimensions S therefore has no eigenvalue inside the open gap.

The resulting gap protection is one ingredient in selecting a specific perturbed spectral subspace and proving that it lies on the small-angle branch.

## Distinguish two reflections

The same construction applies to a reducing subspace V of another operator S: write J V for reflection through V.

Since V reduces S, J V commutes with S. Thus J V S J V equals S.

Rearrange S equals T plus H. We obtain J V T J V minus T equals H minus J V H J V. Its norm is at most twice the norm of H, since reflection preserves unitarily invariant norms.

The quantity J V T J V minus T is called the mirror defect of T through V. It is small whenever H is small. It will provide the right-hand side of the sine-two-theta theorem.

This second reflection is the bridge between an operator perturbation and a geometric doubled angle. The first reflection exposed the off-diagonal structure; the second transports an exact reducing subspace across a perturbed symmetry.

## Why the distinction matters

The sine-two-theta theorem does not require the perturbation itself to be off-diagonal. It uses a two-block gap and a mirror-defect estimate that works for any self-adjoint perturbation.

The tangent-two-theta theorem has a stronger geometric conclusion: the selected subspaces remain on the branch strictly below forty-five degrees. The off-diagonal hypothesis is what supplies that conclusion in its classical form.

In a principal plane, reflecting one line across another doubles the angle between their directions. The block reflection converts that planar identity into an operator estimate for the doubled principal angles; spectral selection is an additional requirement when a tangent bound is sought.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For `P=P_U`, `Q=I-P`, `J=P-Q`, and `S=T+H`, with `U` reducing self-adjoint `T`,

\[J^*=J,\quad J^2=I,\quad JTJ=T.\]

Off-diagonal `H` means `PHP=QHQ=0`, equivalently `JHJ=-H`; hence `JSJ-S=-2H`. For any reducing `V` of self-adjoint `S`, `J_V S J_V=S`, so

\[J_V T J_V-T=H-J_VHJ_V,\qquad N(J_V T J_V-T)\le 2N(H).\]

The source distinguishes the finite block-reflection algebra from the general mirror-defect inequality; the latter requires the reducing comparison operator.

### Source declaration excerpts

`DavisKahan/FiniteDimensional/DoubleAngle/TanTheta.lean` — `starProjection_comp_comp_starProjection_eq_zero` (exact declaration header; body omitted):

```lean
theorem starProjection_comp_comp_starProjection_eq_zero
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] {H : E →ₗ[𝕜] E}
    (hH : ∀ u ∈ U, ∀ u' ∈ U, ⟪u, H u'⟫_𝕜 = 0) :
    (U.starProjection : E →ₗ[𝕜] E) ∘ₗ H ∘ₗ (U.starProjection : E →ₗ[𝕜] E) = 0 := by
```

`DavisKahan/BoundedOperator/Reflection.lean` — `reflectionDefect` (exact declaration header; body omitted):

```lean
noncomputable def reflectionDefect (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
```

`DavisKahan/BoundedOperator/Reflection.lean` — `reflectionOperator_comp_reflectionDefect` (exact declaration header; body omitted):

```lean
theorem reflectionOperator_comp_reflectionDefect
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (A : E →L[𝕜] E) :
    U.reflectionOperator ∘L reflectionDefect U A =
      -(reflectionDefect U A ∘L U.reflectionOperator) := by
```

`DavisKahan/BoundedOperator/Reflection.lean` — `norm_reflectionDefect_le_two_mul` (exact declaration header; body omitted):

```lean
theorem norm_reflectionDefect_le_two_mul
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : Submodule.IsReducing V B) :
    ‖reflectionDefect V A‖ ≤ 2 * ‖A - B‖ := by
```

**Mapping.** `starProjection_comp_comp_starProjection_eq_zero` formalizes vanishing diagonal compressions. `reflectionDefect` uses a continuous linear map and is zero for an operator reduced by the reflecting subspace. `norm_reflectionDefect_le_two_mul` is the norm estimate used by the doubled-angle perturbation proof. The finite two-block form gap appears in `sin_two_theta_reflection_le`.
