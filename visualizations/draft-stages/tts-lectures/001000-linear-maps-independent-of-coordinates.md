# Linear maps independent of coordinates

<!-- BEGIN SPOKEN LECTURE -->

A matrix is an array of numbers. A linear transformation is a rule that takes vectors to vectors while respecting addition and scaling. Those two things are related, but they are not the same thing. In this lesson we will see exactly how a matrix describes a transformation, why the numbers change when we choose different coordinates, and which parts of a transformation survive that change.

There is a useful conclusion we can know from the beginning. A linear map does not need coordinates to exist. Coordinates are a way of doing calculations with it. If we change our coordinate system correctly, we get a different matrix for the same map, and any claim about the map itself must survive that change.

We assume that vectors and matrix multiplication are available from basic linear algebra. We are going to look more closely at what those calculations mean.

## A rule, not an array

Consider the plane. Define a transformation that doubles the horizontal component of every vector and leaves its vertical component unchanged. An arrow pointing one unit to the right becomes an arrow pointing two units to the right. An arrow pointing one unit upward stays as it was. An arrow pointing diagonally up and right is stretched horizontally but not vertically.

In the usual coordinates, this transformation has a two-by-two matrix with two in its upper-left entry, one in its lower-right entry, and zeros elsewhere.

The first column tells us what happens to the horizontal coordinate vector. The second column tells us what happens to the vertical coordinate vector. The matrix is therefore a compact record of what our rule does to two chosen vectors.

Why is knowing the action on those two vectors enough? Because every vector in the plane can be written as a multiple of the first, plus a multiple of the second. A linear transformation respects those combinations. If a vector is three times the first basis vector minus four times the second, the image must be three times the image of the first, minus four times the image of the second.

That is the entire reason a finite-dimensional linear map can be represented by a matrix: choose a basis, record the images of its vectors as columns, and use linearity to recover the action on everything else.

Let us say explicitly what linearity requires. For any two input vectors, the image of their sum is the sum of their images. And for any scalar, meaning a real or complex number in our setting, the image of a scaled vector is the same scale applied to the image. A rule that adds a fixed nonzero offset to every output fails the first condition. A rule that squares each coordinate generally fails both. Linear maps are special because the behavior of a few basis vectors determines the entire rule.

Notice that none of this definition referred to a particular matrix. The definition is a statement about vectors and a rule relating them.

## The same map in a different language

Now we describe the same plane using a different pair of basis vectors. Keep the first basis vector pointing horizontally right. Let the second one point one unit right and one unit up. These two vectors are not perpendicular, but they do form a basis: every arrow in the plane can still be written uniquely as a combination of them.

Call them the first new basis vector and the second new basis vector.

Our original transformation doubles horizontal components and leaves vertical components unchanged. Applied to the first new basis vector, it produces twice that first vector. So the first column of the new matrix is two, followed by zero.

Applied to the second new basis vector, the transformation takes the arrow with components one and one to the arrow with components two and one. But in the new basis, that output is one copy of the first basis vector plus one copy of the second. So the second column of the new matrix is one, followed by one.

The new matrix therefore has first row two, one, and second row zero, one.

This is not the diagonal matrix we started with. It even has an off-diagonal entry, although the transformation has not changed at all. We changed the basis in which we describe it.

This example is worth holding in mind. A nonzero off-diagonal matrix entry does not, by itself, mean the underlying transformation suddenly gained a new physical effect. It may mean only that our coordinate axes are tilted relative to the directions the transformation naturally respects.

There is a second subtlety. The original diagonal matrix is symmetric, and the new matrix is not. This does not contradict the intrinsic geometry of the original transformation. Symmetry of a coordinate matrix represents self-adjointness in the simple transpose form only when the basis is orthonormal. Our new basis is not orthogonal. Later, when we study inner products and adjoints, we will make that statement precise.

## The change-of-basis calculation

It helps to reconstruct the general formula rather than memorize it.

Imagine that a column of numbers gives a vector's coordinates in our new basis. To obtain the same vector's standard coordinates, we combine the new basis vectors using those numbers. Put the new basis vectors into the columns of a matrix, and call that matrix P. Multiplication by P converts new coordinates to old coordinates.

We then apply the original matrix A, because A describes our transformation in the old coordinates.

Finally, we convert the output back into new coordinates. That conversion uses the inverse of P.

Reading those three actions in order, we first apply P, then A, then P inverse. Matrix multiplication composes actions from right to left, so the new matrix is P inverse times A times P.

This is called a similarity transformation. It describes a single linear map from a space to itself, expressed using one basis before and after the change.

There is a good way to check the order. A new-coordinate input cannot be fed directly into A unless we first convert it into old coordinates. That is why P goes on the right. The output of A is still in old coordinates. That is why P inverse goes on the left.

The formula records the coordinate conversion into the original basis, the action of the map, and conversion back.

If the input and output belong to different vector spaces, we may choose one basis for the inputs and another for the outputs. Then there are two conversion matrices. If P converts new input coordinates to old input coordinates, and Q converts new output coordinates to old output coordinates, the new matrix is Q inverse times A times P. Only when the two spaces are the same and we use the same basis change do we obtain the similarity formula.

This distinction matters later because many important operators are rectangular: they map between different spaces, or between a small coordinate space and a larger space of vectors.

## What stays unchanged

The transformation has a collection of vectors that it sends to zero. We call that collection its kernel. In our stretching example, only the zero vector maps to zero, so its kernel contains nothing else.

The transformation also has a range: all outputs it can produce. Our stretching map can produce every vector in the plane. Given a desired horizontal output, we can halve its horizontal component to find an input. The vertical component can be copied directly. Thus the range is the whole plane.

The kernel and range are geometric sets of vectors. Their coordinate descriptions change with a basis, but the underlying sets do not. Their dimensions do not change, either. The dimension of the range is the rank. The dimension of the kernel is the nullity.

Now consider a less reversible transformation. Suppose the rule sends an input with horizontal coordinate x and vertical coordinate y to an output with horizontal coordinate x and vertical coordinate zero. Every vertical vector is sent to zero. The kernel is the vertical axis. Every output lies on the horizontal axis, so that axis is the range. No change of basis can make this operator genuinely invertible; there will always be a nonzero vector in the kernel.

A basis change can make a matrix look different, but it cannot restore information that the transformation really destroys.

Another important property is being an eigenvector. An eigenvector is a nonzero vector whose image points along the same one-dimensional direction: the transformation simply scales it. The scale is the eigenvalue.

Our horizontal-stretching map has a horizontal eigenvector with eigenvalue two and a vertical eigenvector with eigenvalue one. In the tilted basis, the eigenvectors have different coordinate columns, but the geometric vectors and their scale factors are the same.

Here is how the similarity formula preserves an eigenvalue. Start with a vector that A scales by some number. Convert that vector into the new coordinates using P inverse. Apply the new matrix, which is P inverse times A times P. The P on the right cancels the P inverse used to make the new coordinates. What remains is the original transformation, followed by conversion back to the new basis. Since the original transformation merely scaled the vector, we obtain the same scale factor in the new coordinates.

Thus changing the basis preserves the eigenvalues of an endomorphism. That word, endomorphism, just means a linear map from a vector space back to itself. It is a useful name because eigenvalues are defined for maps whose inputs and outputs can be compared as vectors in the same space.

An arbitrary change of coordinates does not preserve every numerical measurement made directly from a matrix. For example, taking the ordinary Euclidean length of coordinate columns after a non-orthogonal basis change can give a misleading comparison. The physical length of a vector depends on an inner product, and the coordinate expression for that inner product also changes. We will return to this when we develop norms and Hilbert spaces.

## Why composition matters

Linear maps can be combined. If one map sends vectors from E to F, and another sends vectors from F to G, then their composition sends vectors from E to G. It means: perform the first action, then the second.

We can establish its linearity directly. The first map respects addition; the second map also respects addition. So applying their composition to a sum produces the sum of their composed images. The same two-step reasoning works for scalar multiplication.

Matrices represent composition by matrix multiplication once all the domain and codomain bases have been fixed. The dimensions of the matrices enforce the same requirement: the first map's output must fit the second map's input.

Composition order is essential in operator theory. For example, an operator followed by a projection and a coordinate embedding followed by a compression generally act on different intermediate spaces. The order of composition tells us which space each intermediate vector lives in. Getting that order wrong can produce an invalid mathematical statement even when its symbols look plausible.

## A short reconstruction

Here is a way to test your understanding without memorizing a formula.

Return to the tilted basis from earlier: the first vector is one unit right, and the second is one unit right and one unit up. Our transformation doubles horizontal components and leaves vertical components unchanged.

What happens to the geometric vertical vector, the one that points zero units right and one unit up? In the tilted coordinates it is minus one copy of the first basis vector plus one copy of the second. So its coordinate column is negative one, one.

The new matrix has first row two, one, and second row zero, one. Multiplying it by the column negative one, one, produces negative one, one again. This verifies that the vertical direction remains an eigenvector with eigenvalue one, even though its coordinate column is not the old standard one.

For a second reconstruction, imagine two coordinate systems but forget the formula for changing matrices. Ask yourself: What conversion must be performed first to feed the new coordinates into the old matrix? What conversion must be performed after applying that matrix? If you can answer those two questions, you can derive the similarity formula again.

## What we have established

A linear map is characterized by preserving addition and scalar multiplication. A basis lets us encode that map as a matrix, whose columns record the images of basis vectors. Changing basis changes the matrix, but not the map. For a map from a space to itself, the new matrix under a single basis change is P inverse times A times P. Kernel, range dimension, and eigenvalues are properties of the map rather than of one particular coordinate display.

A basis change never alters the underlying linear transformation. Norms add a separate question: how do we measure vectors without depending on the choice of coordinates?

<!-- END SPOKEN LECTURE -->

---

## Companion: symbolic facts and Lean correspondence (not TTS narration)

**Facts developed in this lecture.** For linear maps \(T:E\to F\) and \(S:F\to G\),
\[
T(x+y)=T(x)+T(y),\quad T(ax)=aT(x),\qquad
(S\circ T)(x)=S(T(x)).
\]
For \(T:E\to E\), if \(P\) changes new coordinates into old coordinates, \([T]_{\mathrm{new}}=P^{-1}[T]_{\mathrm{old}}P\). For distinct input and output changes \(P,Q\), \([T]_{\mathrm{new}}=Q^{-1}[T]_{\mathrm{old}}P\).

**Actual source correspondence.** The following definition is from `ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean` in the supplied source snapshot. It is included here to show how Lean records the two defining obligations of a linear map; the finite-frame construction itself will be developed in lecture `017000`.

```lean
noncomputable def finiteSynthesis (v : ι → E) : EuclideanSpace 𝕜 ι →ₗ[𝕜] E where
  toFun c := ∑ i, c i • v i
  map_add' a b := by
    simp only [PiLp.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' r a := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
```

`E →ₗ[𝕜] F` is the type of linear maps between modules over scalar field `𝕜`; `toFun` specifies the action and the two `map_...` fields certify preservation of addition and scaling. The source also uses `∘ₗ` for composition of linear maps and `LinearMap.comp_apply` to rewrite the composed map at a vector. These are the formal counterparts of the mathematical operations in the transcript.

**Source location/provenance.** `ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean` is a DKPS-developed finite-frame construction staged for TauCeti, as recorded in that file's provenance header. The quotation is from the provided source snapshot, not a freshly compiled Lean companion. This appendix is display-only; narration should stop at `END SPOKEN LECTURE`.
