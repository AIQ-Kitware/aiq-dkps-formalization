# 007000 — Block operators and reducing subspaces

**Track:** G3 audio paper track. **Draft:** adapted from G2 lecture 016000. **Section:** machinery. **Audience:** prior linear algebra and basic analysis.

<!-- BEGIN SPOKEN LECTURE -->

A subspace U is invariant under A if A maps U into itself. It is reducing if its orthogonal complement is invariant too. In a reducing decomposition, A acts independently on two perpendicular summands. A general operator can also be expressed in four blocks, whose off-diagonal entries measure the failure of reduction.

This construction is important because the Davis–Kahan theorems often distinguish a perturbation that acts *within* a spectral subspace from one that moves vectors *between* two spectral subspaces. A block decomposition lets us say exactly what those two effects are. For now, the central objects are the diagonal and off-diagonal blocks of an operator. First we need to know how the blocks are made.

## One vector, two perpendicular components

Imagine a horizontal line drawn through the origin of a plane. Every vector has a horizontal component and a vertical component. The two components add to give the original vector, and they meet at a right angle.

The same idea works in a Hilbert space. Choose a closed subspace, which we will call M. Let M perp mean all vectors perpendicular to every vector in M. The projection theorem tells us that any vector x can be written uniquely as m plus n, where m belongs to M and n belongs to M perp.

The closedness of M matters. It ensures that the nearest-point projection onto M exists, so the perpendicular decomposition works for *every* vector of the Hilbert space. We call this decomposition an orthogonal direct sum.

There is an immediate length formula. Because the components are perpendicular, the squared length of x equals the squared length of m plus the squared length of n. This is the Pythagorean theorem in Hilbert-space form.

It also works backward. If we take one vector from M and one from M perp, add them, and measure the sum, we obtain exactly that Pythagorean expression. So the pair of component spaces, equipped with the square-root-of-sum-of-squares length, describes the original Hilbert space without distortion.

The word *direct* says that the representation is unique. If m plus n equals zero and the two terms are perpendicular, both terms must be zero. No nonzero vector belongs to both components.

## Turning a single operator into four maps

Now let T be a bounded linear operator on our Hilbert space. Start with an input x, and split it into m plus n. Linearity gives T of x equals T of m plus T of n.

But each of those two outputs can itself be split into a part in M and a part in M perp. We therefore get four kinds of motion.

The first kind starts in M and ends in M. The second starts in M perp and ends in M. The third starts in M and ends in M perp. The fourth starts in M perp and ends in M perp.

We arrange them in a two-by-two table of operators. The top row contains outputs in M. The bottom row contains outputs in M perp. The left column handles inputs from M, and the right column handles inputs from M perp.

It is tempting to call this a matrix, but its entries need not be numbers. Each entry is itself a linear map between two spaces. Those spaces could be large or infinite-dimensional. This is a *block-operator matrix*.

To produce the top-left block, take an input from M, apply T, then project the output back onto M. To produce the bottom-left block, take the same kind of input but project the output onto M perp instead. Do the analogous operations for inputs from M perp to obtain the two right-hand blocks.

The projection after T matters. The input subspace alone does not guarantee that T returns a vector to that subspace.

## A two-dimensional calculation

Consider the operator on the ordinary plane whose first output coordinate is twice the first input plus three times the second, and whose second output coordinate is three times the first plus five times the second.

Choose M to be the horizontal axis. Its perpendicular complement is the vertical axis.

A horizontal input with coordinate a produces output coordinates two a and three a. Its horizontal output is two a, while its vertical output is three a. So the left column of our block matrix has the numbers two and three.

A vertical input with coordinate b produces three b horizontally and five b vertically. So the right column has the numbers three and five.

Relative to our horizontal-plus-vertical splitting, the four blocks are two, three, three, and five. The diagonal blocks are two and five. The off-diagonal blocks are the two threes.

The diagonal blocks tell us what T does *within* each axis. The off-diagonal blocks tell us how it carries vectors *across* the splitting.

Now replace T with the operator that merely doubles horizontal vectors and multiplies vertical vectors by five. Both off-diagonal blocks become zero. The subspace is reducing, and the two directions evolve independently.

But replace T instead with the operator that swaps the two coordinates. The diagonal blocks become zero, while the off-diagonal blocks remain nonzero. Every horizontal vector is sent vertically, and every vertical vector is sent horizontally. That is an *off-diagonal operator*. It is emphatically not a reducing operator relative to either axis.

## The diagonal and off-diagonal parts

We can separate any operator T into two new operators. The *diagonal part* retains the top-left and bottom-right blocks and sets the other blocks to zero. The *off-diagonal part* retains the two crossing blocks and sets the diagonal blocks to zero.

Adding those parts recovers T exactly. Nothing is discarded.

There is a useful description using projections. Call the projection onto M, P, and the projection onto M perp, Q. The diagonal part applies P, then T, then P again, and adds the analogous Q, T, Q composition. The off-diagonal part is what remains after subtracting the diagonal part from T.

The diagonal block operator obtained by discarding the crossings is called the pinching of an operator. It keeps the parts that act within each selected summand. Subtracting the pinching leaves the off-diagonal part, which exchanges the two summands.

For our numerical example, pinching removes the two threes. The resulting diagonal operator doubles the horizontal component and multiplies the vertical component by five. The remaining off-diagonal operator moves horizontal input vertically by a factor of three and vertical input horizontally by the same factor.

We have two separate questions now. Does the whole operator have crossing blocks? And does the operator have within-subspace blocks? The words *reducing* and *off-diagonal* answer different questions, as our examples show.

## How the adjoint changes the blocks

The block picture becomes even more powerful when T has an adjoint. Recall that taking an adjoint reverses the direction of a map: a block taking M into M perp becomes an adjoint block taking M perp into M.

Consequently, the adjoint of a block matrix is obtained by taking the adjoint of each block and swapping the two off-diagonal positions.

If T is self-adjoint, the diagonal blocks are self-adjoint operators on their respective spaces, and the lower-left block is the adjoint of the upper-right block. Those crossing blocks cannot vary independently.

Return to our operator with entries two, three, three, and five. Its crossing blocks match because the matrix is self-adjoint. If we changed the bottom-left three to four while leaving the top-right three unchanged, we would lose self-adjointness.

This illustrates a general self-adjointness fact: if a self-adjoint operator has zero crossing in one direction, it must have zero crossing in the other. For self-adjoint operators, invariance of one summand therefore forces reduction.

## A reflection that detects crossing

Here is a compact trick we will use much later. Reflect a vector through M: leave its M component alone, and reverse the sign of its M-perp component. Call this reflection J.

Now apply J, then T, then J again. What happens to the four blocks?

A block that stays entirely inside M has no sign change. A block that stays entirely inside M perp passes through two sign changes, so it also stays the same. But a block that crosses from one component to the other experiences exactly one sign change. Both crossing blocks reverse sign.

Therefore J T J has the same diagonal part as T and the *negative* of its off-diagonal part.

We can recover the diagonal part by averaging T with J T J. We can recover the off-diagonal part by taking half their difference.

That algebraic identity is a useful piece of future double-angle reasoning. A reflection can separate the part of an operator that respects a splitting from the part that crosses it, without choosing coordinates or explicitly writing a four-block table.

## Check that you can reconstruct it

Try three small problems. First, given an operator on the plane and the horizontal axis, determine all four blocks by applying it to one horizontal and one vertical vector. Second, explain why the adjoint swaps the crossing blocks. Third, starting with the reflection that keeps M and reverses M perp, explain why conjugating an operator by the reflection changes exactly the off-diagonal signs.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematical statements and Lean correspondence (display only)

Let \(H=M\oplus M^\perp\) with orthogonal projections \(P\) and \(Q=I-P\). For bounded \(T:H\to H\), relative to this splitting,

\[
T=\begin{bmatrix}A&B\\C&D\end{bmatrix},\quad
D_M(T)=PTP+QTQ,\quad O_M(T)=PTQ+QTP,
\quad T=D_M(T)+O_M(T).
\]

The types are \(A:M\to M\), \(B:M^\perp\to M\), \(C:M\to M^\perp\), and \(D:M^\perp\to M^\perp\). For self-adjoint \(T\), \(A=A^*\), \(D=D^*\), and \(C=B^*\). With \(J=P-Q=2P-I\),

\[
JTJ=D_M(T)-O_M(T),\quad D_M(T)=\frac{T+JTJ}{2},\quad O_M(T)=\frac{T-JTJ}{2}.
\]

**Lean bridge.** The local DKPS module `DavisKahan/FiniteDimensional/Core/OperatorBlocks.lean` defines the block separation directly:

```lean
/-- The diagonal part (pinch) of an operator relative to `U ⊕ Uᗮ`. -/
@[expose]
noncomputable def pinch (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  U.starProjection.toLinearMap ∘ₗ H ∘ₗ U.starProjection.toLinearMap +
    Uᗮ.starProjection.toLinearMap ∘ₗ H ∘ₗ Uᗮ.starProjection.toLinearMap

/-- The off-diagonal part of an operator relative to `U ⊕ Uᗮ`. -/
noncomputable def offDiagonalPart (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (H : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  H - pinch U H

/-- Davis--Kahan's vanishing-pinch hypothesis. -/
def IsOffDiagonal (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (H : E →ₗ[𝕜] E) : Prop :=
  pinch U H = 0
```

`U.starProjection` is the projection onto `U`, `Uᗮ` is its orthogonal complement, and `∘ₗ` is composition of algebraic linear maps. The file uses `E →ₗ[𝕜] E` with a finite-dimensional assumption; the spoken block calculations also apply to bounded operators on arbitrary Hilbert spaces. `IsOffDiagonal` means the two diagonal blocks vanish, not that `U` reduces `H`. These declarations originate in the DKPS source; a `TauCeti` namespace does not by itself mean an upstream mathematical origin.
