# 100000 — Modulus, polar factors, and ideal invariance

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `035000` operator modulus, `037000` polar decomposition, `038000` partial isometries, `098000` symmetric ideals, `099000` Schatten classes. **Next:** `101000` ideal estimates for compressions and block sums.

<!-- BEGIN SPOKEN LECTURE -->

# What a linear map does to lengths, and what it does to directions

Consider a map on the plane that takes the vector pointing straight up, stretches it by three, and sends it to the right. It sends every horizontal vector to zero.

There are two different effects in that description. The map decides how much of an input survives and how long its output becomes. It also decides which direction that output points.

Can we separate those two effects?

That question leads to the modulus of an operator and its polar decomposition. It also gives us a way to show that changing output directions does not change singular-value norms, including the norms used for Hilbert–Schmidt and trace-class operators.

We'll do the calculation in the plane first. Then we'll see why the same reasoning works for rectangular operators and infinite-dimensional Hilbert spaces.

## The simple map

Let T take an input with coordinates x and y and return a vector with first coordinate three y and second coordinate zero.

The input pointing right has coordinates one and zero. T sends it to zero. The input pointing up has coordinates zero and one. T sends it to a vector of length three pointing right.

The matrix of T has a three in its upper-right position and zeros everywhere else.

Now ask what the length of T applied to an arbitrary input is. The answer is three times the absolute value of y. The x coordinate contributes nothing.

Suppose we want another operator that preserves exactly this length information, but doesn't redirect the surviving vertical coordinate into the horizontal direction. A natural choice is the diagonal operator that kills the first coordinate and multiplies the second by three.

This second operator sends x,y to zero,three y. On every input, its output has exactly the same length as the output of T.

That second operator is the modulus of T. The modulus records the stretching without the directional rearrangement.

## Why the modulus has that definition

For a general bounded operator T from a Hilbert space E to a Hilbert space F, the source and target may be different. We begin with its adjoint, which runs from F back to E.

Compose T with its adjoint in the order T adjoint followed by T. The resulting operator acts on the source E.

Here's the key identity. Pair T adjoint T applied to x with x. The answer is the squared length of T x.

This tells us that T adjoint T is positive. It can therefore have a unique positive square root. We call that square root the modulus, or absolute T.

In our plane example, T adjoint T is diagonal with entries zero and nine. Its positive square root is diagonal with entries zero and three, just as we guessed.

The definition is designed to ensure that T and absolute T give outputs of equal length for every input. It also ensures that they lose exactly the same input directions: their kernels agree.

We have separated out the length data. What restores the direction?

## Restore the direction with a partial isometry

In the plane example, the modulus sends the upward unit vector to a vertical vector of length three. To recover T, we need to turn that surviving vertical direction into a horizontal direction, without changing its length.

Define U to send the upward unit vector to the rightward unit vector. Define U to send the rightward unit vector to zero.

Then applying the modulus first and U second gives exactly T. The modulus supplies the factor three; U chooses the direction.

Notice that U is not a rotation of the whole plane. It kills one direction. It only preserves lengths on the part of the source that survives the modulus.

That is what a partial isometry does. It acts isometrically on an initial subspace and vanishes on the orthogonal complement of that subspace. In particular, its operator norm is at most one.

Now we can build U for any bounded T, even without a matrix or a basis of singular vectors.

First consider a vector that can be written as absolute T applied to some x. Send it to T x. This prescription is well-defined: if two choices of x give the same output under the modulus, their difference lies in the common kernel and gives the same output under T.

And it preserves lengths, because T x and absolute T x have equal lengths.

Extend that isometry to the closure of the range of the modulus. On its orthogonal complement, which is the kernel of T, set it to zero.

That gives the canonical polar factor U. We obtain the polar decomposition: T is U followed by the modulus.

There's an equally useful reverse identity. The modulus is U adjoint followed by T. In the example, T sends the vertical direction to the horizontal one, and U adjoint turns that horizontal output back to the vertical direction. The stretch of three is unchanged.

These two factorizations are the heart of the ideal-norm argument.

## Why every symmetric ideal gauge is unchanged

Let's first recall what an operator ideal gives us. Its gauge is a way to measure an operator's size, defined on the appropriate family of operators. A symmetric ideal family has the property that composing with bounded operators on the left or right cannot enlarge the gauge by more than the product of their operator norms.

Think about multiplying a matrix by a rotation. Its singular values stay the same. The ideal inequality extends the useful part of that observation beyond invertible rotations, to contractions and partial isometries.

Since U is a contraction and T equals U times absolute T, the gauge of T is no greater than the gauge of absolute T.

Now run the calculation backward. Absolute T equals U adjoint times T. U adjoint is also a contraction, so the gauge of absolute T is no greater than the gauge of T.

Each is at most the other. Therefore they are equal.

We have also proved something about membership. Some ideals include only operators whose gauge is finite. The same comparison works with extended gauges that may be infinite. So T belongs to the ideal if and only if its modulus belongs to the ideal.

Let's check the conclusion on our little matrix. The only nonzero singular value of T is three, and the modulus has the same singular values, three and zero. The operator norm is three. The Hilbert–Schmidt norm is three. The trace norm is also three.

The fact that all three norms agree in this example is incidental. The fact that each norm of T equals the corresponding norm of its modulus is the general result.

## Why a full unitary is unnecessary

Our map loses the horizontal direction. We cannot demand that U preserve lengths on every direction in the source, because the full operator T is allowed to have a kernel.

In higher or infinite dimensions, the source and target might not even have the same dimension. A full unitary between them might not exist.

But nothing in our proof needed one. We used a partial isometry from the source to the target and its adjoint in the reverse direction. Both have norm at most one, and their compositions are valid between the relevant Hilbert spaces.

The construction also explains why the canonical factor is specified to be zero on the kernel. If we only required a factorization, other choices could be possible on directions that the modulus already kills. Setting U to zero there removes the ambiguity.

As another check, imagine a map from the plane into three-dimensional space. It preserves only the upward input coordinate, stretches it, and sends it along some chosen axis in three-dimensional space. The modulus still acts on the source plane. U carries the surviving direction into the target. The two ideal-gauge inequalities are identical to the ones we just used.

## Infinite dimensions and what the result buys us

A bounded operator on a Hilbert space need not have a finite singular-vector basis. Its range need not be closed. That's why the general construction used the closure of the modulus range instead of assuming that every output is reached by a finite set of eigenvectors.

The modulus is positive, so it can be studied with the spectral theorem. Many inequalities are easier to understand for positive operators than for arbitrary maps between different spaces.

Polar decomposition lets us prove an estimate for the positive modulus, then transfer it back to the original operator without changing its symmetric ideal gauge.

In particular, compactness, Hilbert–Schmidt membership, and trace-class membership agree between T and its modulus.

The central calculation is now easy to remember. T factors through a partial isometry in one direction. Its modulus factors through the adjoint partial isometry in the other. Both factors are contractions. Those two inequalities force equality of ideal size, even for rectangular maps with kernels.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For T:E→F, |T|=(T* T)^{1/2} acts on E. The canonical polar factor U:E→F is a contraction satisfying T=U|T| and |T|=U* T. Every symmetric ideal gauge obeys gauge(A T B)≤‖A‖ gauge(T) ‖B‖ for bounded composable A,B. Thus gauge(T)≤gauge(|T|) and gauge(|T|)≤gauge(T), giving equality in the extended nonnegative reals. Consequently Mem(T) iff Mem(|T|). No invertibility or equality of source and target dimensions is required.

### Worked example: canonical partial isometry

For \(T=\begin{pmatrix}0&3\\0&0\end{pmatrix}\) on \(\mathbb R^2\),
\[
T^*T=\begin{pmatrix}0&0\\0&9\end{pmatrix},\qquad
|T|=\begin{pmatrix}0&0\\0&3\end{pmatrix},\qquad
U=\begin{pmatrix}0&1\\0&0\end{pmatrix}.
\]
Then \(T=U|T|\), \(|T|=U^*T\), and \(U^*U=\operatorname{diag}(0,1)\). The initial space of the canonical polar factor is \(\operatorname{span}(e_2)\), and the kernel is \(\operatorname{span}(e_1)\). Both \(T\) and \(|T|\) have singular values \((3,0)\).

### Actual Lean source declarations

`ForTauCeti/Analysis/OperatorIdeal/Family/Modulus.lean` — `norm_polarFactor_le_one_rectangular` (declaration header, proof omitted):

```lean
theorem norm_polarFactor_le_one_rectangular (T : E →L[K] F) :
    ‖T.polarFactor‖ ≤ 1 := by
```

`ForTauCeti/Analysis/OperatorIdeal/Family/Modulus.lean` — `gauge_modulus_eq` (declaration header, proof omitted):

```lean
theorem gauge_modulus_eq
    (N : SymmetricOperatorIdealFamily.{u, v} K) (T : E →L[K] F) :
    N.toOperatorIdealFamily.gauge T.modulus =
      N.toOperatorIdealFamily.gauge T := by
```

`ForTauCeti/Analysis/OperatorIdeal/Family/Modulus.lean` — `modulus_mem_iff` (declaration header, proof omitted):

```lean
theorem modulus_mem_iff
    (N : SymmetricOperatorIdealFamily.{u, v} K) (T : E →L[K] F) :
    T.modulus ∈ (N.toOperatorIdealFamily.operatorGauge E E).finiteSubmodule ↔
      T ∈ (N.toOperatorIdealFamily.operatorGauge E F).finiteSubmodule := by
```

**Type and hypothesis map.** The polar factor is contractive for `T : E →L[K] F`, even when source and target differ. The two contractions `T.polarFactor` and its adjoint give both inequalities and hence equality of extended gauges. Finiteness of the gauge gives equivalence between membership of `T` and membership of `T.modulus`.

These are exact excerpts from the supplied DKPS source snapshot. The mathematical narration develops its arguments independently; citing these declarations does not assert that the narrated intermediate proof has been separately compiled in Lean. Where the current declaration lives in `ForTauCeti`, its placement does not imply the mathematical result originated outside the DKPS project.
