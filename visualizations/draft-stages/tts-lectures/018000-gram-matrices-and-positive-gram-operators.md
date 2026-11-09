# Gram matrices and positive Gram operators

<!-- BEGIN SPOKEN LECTURE -->

Given vectors v one through v n, the synthesis map S takes coefficients c and returns their linear combination. Its adjoint S star analyzes a vector by taking inner products with the selected vectors. The composite S star S acts on coefficient lists; it is the Gram operator.

It may look like a device for storing a table of inner products. But that table encodes much more. It records lengths, angles, linear dependence, and enough information to reconstruct the geometry of a finite collection of vectors, up to an appropriate change of coordinates.

We are not assuming a spectral theorem today. We will prove the basic facts directly from inner products, so that when we eventually study eigenvalues of Gram operators, we know exactly what those eigenvalues are describing.

## Make the table by measuring each vector against every other

Take two vectors in the ordinary plane. Let v one point one unit to the right. Let v two point one unit to the right and one unit up.

We can ask four questions. What is the inner product of v one with itself? What is the inner product of v one with v two? What is the inner product of v two with v one? And what is the inner product of v two with itself?

The answers are one, one, one, and two, in that order.

Arrange them in a two-by-two table. Its first row is one, one. Its second row is one, two. This is the Gram matrix of our two vectors.

The diagonal entries are squared lengths: one and two. The off-diagonal entries measure overlap. In a real inner-product space, the overlap between vectors of lengths one and square root of two is the product of those lengths times the cosine of the angle between them.

Thus a Gram matrix does not merely count vectors or record their coordinates. It records their relationships. A different choice of ambient coordinate axes could change the displayed vectors without changing the Gram matrix.

Over complex scalars, the same construction uses complex inner products. The table is conjugate-symmetric, rather than necessarily symmetric with real entries. We call that property Hermitian. Its diagonal entries remain real and nonnegative.

## Why the Gram operator is analysis after synthesis

Let S send a coefficient list c to the linear combination of vectors v indexed by c, and let S star measure the inner products with those vectors. We can derive each Gram-matrix entry from this pair of maps.

Start with coefficients a and b. Synthesis builds a times v one plus b times v two. Analysis measures that synthesized vector against v one and v two.

The first measurement is a times the inner product of v one with v one, plus b times the inner product of v one with v two. The second is the corresponding expression with v two as the measuring vector.

These are precisely the rows of the Gram matrix multiplied by the coefficient list. So the Gram operator is analysis after synthesis.

This connection matters. The matrix entries are not arbitrary numbers written down by hand. They arise from a composition of two linear maps that are adjoints of each other.

If S stands for synthesis, and S star is analysis, then the Gram operator is S star times S. This algebraic form explains its positivity.

## Positivity has a physical interpretation

Let c be any coefficient list. Form the inner product of c with the Gram operator applied to c.

Use the definition of the Gram operator. We have the inner product of c with S star S of c. Move S star across the inner product using the adjoint identity. The answer is the squared length of S of c.

In words: the Gram quadratic form of a coefficient list equals the squared length of the vector those coefficients synthesize.

A squared length is never negative. Therefore every Gram operator is positive semidefinite.

Let's check this for our numerical example. Coefficients a and b synthesize the vector whose coordinates are a plus b and b. Its squared length is the square of a plus b, plus the square of b. That expression can never be negative.

If we expand it, we get a squared plus two a b plus two b squared, which is exactly the quadratic form of the Gram matrix with rows one, one and one, two.

The calculation also explains why Gram matrices have a stronger property than just nonnegative entries. A Gram matrix can contain negative off-diagonal entries if the vectors point partly against one another. Positivity means the *whole quadratic form* is nonnegative for every coefficient list. It does not mean that each entry is nonnegative.

## When positivity becomes strict

Can that quadratic form equal zero for a nonzero coefficient list?

Yes, if different selected vectors cancel. Take two identical unit vectors pointing right. The Gram matrix has one in every entry. Coefficients one and negative one synthesize zero, so the Gram quadratic form is zero even though the coefficient list is not zero.

This gives a clean characterization. A finite Gram matrix is *positive definite*—meaning its quadratic form is positive for every nonzero coefficient list—exactly when its vectors are linearly independent.

Here is the proof. If the family is linearly independent, synthesizing a nonzero coefficient list cannot give zero. So its squared length, and therefore the Gram quadratic form, is strictly positive. Conversely, if the family is dependent, there is a nonzero coefficient list that synthesizes zero, and its Gram quadratic form vanishes.

So the difference between positive semidefinite and positive definite is not merely a numerical detail. It detects whether the selected vectors contain exact redundancy.

## The kernel and rank

We can push that argument further.

A coefficient list belongs to the kernel of the Gram operator exactly when it belongs to the kernel of synthesis.

One direction is immediate: if synthesis sends c to zero, then analysis after synthesis also sends c to zero. For the other direction, suppose the Gram operator sends c to zero. Its quadratic form is then zero. By the identity for a Gram operator, that quadratic form equals the squared length of synthesis of c. Hence synthesis of c is zero.

The kernels are identical.

In finite dimensions, two linear maps with the same domain and the same kernel have the same rank, because rank equals domain dimension minus kernel dimension. Thus the rank of the Gram matrix equals the dimension of the span of the selected vectors.

For our original two vectors, there is no redundancy. They span the plane, so their Gram matrix has rank two. For two identical vectors, the span has dimension one, so the Gram matrix has rank one.

Notice how much geometric information has emerged from a matrix whose size is determined by the *number of chosen vectors*, not necessarily by the dimension of the ambient space.

## Same Gram matrix, same geometry

Now for a result that feels almost surprising. Suppose we have two finite families of vectors, perhaps living in different inner-product spaces, and their Gram matrices are exactly equal.

Does that mean the two configurations have the same geometry? Yes, in a precise sense: there is a length- and inner-product-preserving linear correspondence between their spans that sends each vector in the first family to the matching vector in the second.

Let's build it rather than just assert it.

Start with a vector in the span of the first family. It can be synthesized from some coefficient list c. Send it to the vector obtained by synthesizing the *same coefficients* from the second family.

There is a possible problem: the first vector might have more than one coefficient representation. How do we know the output is independent of which representation we choose?

Suppose two coefficient lists produce the same first vector. Their difference synthesizes to zero. Its squared length is therefore zero, and that squared length is computed from the first Gram matrix. But the two Gram matrices agree. So synthesizing the same difference from the second family also produces a vector of squared length zero. That vector must be zero.

Therefore both representations give the same output. Our proposed correspondence is well-defined.

The same Gram identity shows that it preserves lengths, and by polarization it preserves inner products. Every vector in the span of the second family can be reached, since it has some coefficient representation. We have constructed an isometric isomorphism between the two spans.

This is called a Gram rigidity principle.

Do not extend the conclusion too far. We have proved a correspondence between the spans. To extend it to a unitary map of the *entire* ambient spaces, we would also need compatible perpendicular complements. In different-dimensional ambient spaces, such an extension may be impossible.

## Gram matrices and distances

A final connection will matter when we study spectral embeddings. The squared distance between two vectors equals the squared length of the first plus the squared length of the second, minus twice the real part of their inner product.

That means a Gram matrix determines all pairwise distances among the vectors.

The converse needs some care. Pairwise distances do not remember where the origin was placed. If you translate every point by the same vector, all pairwise distances stay the same, but the Gram matrix of the point positions usually changes.

To recover a Gram matrix from distances, we first need to choose an origin convention, often by centering the points so their average is zero. For centered point configurations, the relation between squared distances and inner products can be inverted to reconstruct the Gram matrix. The centering condition fixes the translation ambiguity; without it, distances alone do not locate an origin.

## Reconstruct the Gram argument

Try to reconstruct four arguments. Why is every Gram operator positive semidefinite? Why does positive definiteness correspond to independence? Why does the Gram kernel equal the synthesis kernel? And why does equality of two Gram matrices give a well-defined isometry between the corresponding spans?

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical statements and Lean correspondence (display only)

For a finite family \(v=(v_i)_{i\in I}\subset H\) and synthesis \(S_v:\mathbb K^I\to H\), define \(G_v=S_v^*S_v\). With the project's inner-product convention, \((G_v)_{ij}=\langle v_i,v_j\rangle\). Then

\[
\langle c,G_vc\rangle=\|S_vc\|^2\ge0,\quad
\ker G_v=\ker S_v,\quad
\operatorname{rank}G_v=\dim\operatorname{span}\{v_i\}.
\]

A finite Gram matrix is positive definite exactly when the family is linearly independent. If two families have the same Gram matrix, the map \(S_v(c)\mapsto S_w(c)\) is a well-defined inner-product-preserving linear isomorphism between their spans.

**Lean bridge.** The DKPS-staged `ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean` gives the operator and its entrywise formula:

```lean
/-- Gram operator `analysis ∘ synthesis` on coefficient space. -/
noncomputable def finiteGramOperator (v : ι → E) :
    EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι :=
  (finiteAnalysis 𝕜 v).comp (finiteSynthesis 𝕜 v)

/-- Entrywise formula for the Gram operator: it acts by the Gram matrix `(⟪v i, v j⟫)ᵢⱼ`. -/
@[simp]
theorem finiteGramOperator_apply (v : ι → E) (c : EuclideanSpace 𝕜 ι) (i : ι) :
    finiteGramOperator 𝕜 v c i = ∑ j, inner 𝕜 (v i) (v j) * c j := by
  rw [finiteGramOperator, LinearMap.comp_apply, finiteAnalysis_apply, finiteSynthesis_apply,
    inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right]
  ring

/-- The Gram operator is positive. -/
theorem finiteGramOperator_isPositive (v : ι → E) :
    (finiteGramOperator 𝕜 v).IsPositive := by
  rw [finiteGramOperator_eq_selfCompAdjoint]
  exact (finiteAnalysis 𝕜 v).isPositive_self_comp_adjoint
```

Here `EuclideanSpace 𝕜 ι` is the coefficient space, `inner 𝕜 (v i) (v j)` supplies the matrix entry, and `IsPositive` packages the self-adjoint and nonnegative-quadratic-form properties. The proof uses the general fact that a map composed with its adjoint yields a positive operator. For a general rectangular linear map `A`, `ForTauCeti/Analysis/InnerProductSpace/Gram/Operator.lean` separately defines `rightGram A = A.adjoint ∘ₗ A` and `leftGram A = A ∘ₗ A.adjoint`. Those are the two products whose later spectral theory governs singular vectors.

Both files carry original DKPS development provenance despite their `TauCeti` namespace. These excerpts were checked against the supplied source snapshot; no new Lean code was compiled.
