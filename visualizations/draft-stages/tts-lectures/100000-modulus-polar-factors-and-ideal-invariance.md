# 100000 — Modulus, polar factors, and ideal invariance

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `035000` operator modulus, `037000` polar decomposition, `038000` partial isometries, `098000` symmetric ideals, `099000` Schatten classes. **Next:** `101000` ideal estimates for compressions and block sums.

<!-- BEGIN SPOKEN LECTURE -->

# Moving operator size without losing it

We have built a theory of symmetric ideal gauges for rectangular operators. Now we will prove a structural identity that makes the theory practical.

Let T be any bounded map between Hilbert spaces, with no assumption that it is invertible or square. Its modulus is the positive square root of T adjoint T. The polar decomposition writes T as a partial isometry followed by its modulus.

For a symmetric operator ideal, T and its modulus have exactly the same membership status and the same gauge. Our goal is to prove that statement using only the ideal composition inequality and the basic properties of the polar factor.

## Review the modulus carefully

Suppose T maps E to F. Its adjoint maps F back to E. Therefore T adjoint T acts on E, even though T itself need not act on a single space.

The operator T adjoint T is positive because its quadratic form at x equals the squared norm of T x. The positive square-root theorem gives a unique positive operator whose square is T adjoint T. We call it the modulus, written absolute T.

By construction, applying T and applying absolute T produce outputs with the same length on every input. Indeed, both squared lengths equal the quadratic form of T adjoint T at that input.

Consequently, T and its modulus have the same kernel. A direction lost by T is also lost by the modulus, and conversely.

This identity contains the metric information of T. The polar factor will supply the orientation information.

## Construct the canonical polar factor

On the range of absolute T, define a map by sending absolute T applied to x to T applied to x.

Why is this well-defined? If two vectors have the same image under absolute T, their difference belongs to the kernel of absolute T and therefore to the kernel of T. So they also have the same image under T.

Why is the map an isometry on this range? The length identity gives the answer: the norm of T x equals the norm of absolute T x.

Extend this isometry by continuity to the closure of the range of absolute T. On its orthogonal complement, which is the kernel of T, set the map equal to zero. The resulting bounded operator U from E to F is the canonical polar factor.

It is a partial isometry. It preserves norms on its initial space, annihilates the orthogonal complement, and has operator norm at most one.

The polar decomposition is T equals U composed with absolute T.

The other identity is equally important: absolute T equals U adjoint composed with T. This is valid for the canonical factor because U adjoint U is the projection onto the closure of the range of absolute T, where the modulus already takes its values.

## The two-sided gauge comparison

Let N be a symmetric operator ideal family, with extended gauge so that the statement also covers operators outside its carrier.

The ideal inequality says that composing on the left with a contraction cannot increase the gauge. Because the polar factor U has norm at most one, the factorization T equals U absolute T gives gauge of T at most gauge of absolute T.

Now use the reverse identity, absolute T equals U adjoint T. The adjoint of a partial isometry is also a contraction. The same ideal inequality gives gauge of absolute T at most gauge of T.

Put the two estimates together. The gauges are equal.

This is a proof that does not refer to a singular-value basis and does not require T to be invertible. It even works when the gauge is infinite, because both inequalities live in the extended nonnegative reals.

Since an operator belongs to the ideal exactly when its extended gauge is finite, equality of gauges also proves that T belongs if and only if its modulus belongs.

The argument is short because all the geometric work was already invested in the canonical polar factor.

## A two-dimensional example with a kernel

Consider the map on the Euclidean plane that sends the second standard basis vector to three times the first and sends the first basis vector to zero.

Its matrix has a three in the upper right corner and zeros everywhere else. Its adjoint times itself is the diagonal matrix with entries zero and nine. The modulus is therefore diagonal with entries zero and three.

The polar factor sends the second basis vector to the first and annihilates the first. It is not invertible, and it cannot be unitary on the whole plane. Nevertheless, multiplying this polar factor by the modulus reconstructs T.

Both T and its modulus have singular values three and zero. Their operator norm is three, their Frobenius norm is three, and their trace norm is three. Equality is not an accident of this example; it is the general gauge identity we just proved.

Notice also that we were free to rotate the nonzero output direction without changing the ideal gauge. The kernel information remained in the modulus.

## Why uniqueness uses the zero-kernel convention

If T has a nontrivial kernel, a unitary extension of the isometric part may be nonunique, when such an extension exists at all. On the unused directions, different choices can act differently and still reconstruct T after multiplication by its modulus, because the modulus kills those directions.

The canonical polar factor avoids that ambiguity. We require it to be zero on the kernel and an isometry on the closure of the modulus range. Those two requirements determine it completely. The ideal-gauge proof therefore uses a canonical contraction and remains valid even when a full unitary extension is impossible.

## Rectangular maps and zero padding

Suppose instead that E has dimension two and F has dimension three. Let T send one source basis vector to a nonzero target vector and annihilate the other source vector.

The modulus still acts on the two-dimensional source E. The polar factor maps E into the three-dimensional target F. There need not be a unitary equivalence between the whole spaces, since their dimensions differ.

The polar proof still works because it uses contractions, adjoints, and legal compositions, not a unitary between entire spaces. This is why the formulation is the right one for rectangular operators and for different Hilbert spaces.

If we want to compare a complete list of singular values, we insert the appropriate zeros when dimensions differ. But the proof of gauge equality needs no arbitrary completion of the polar factor to a full unitary.

## Compactness and Schatten classes

If T is compact, its modulus is compact. One way to see this is via the compact spectral theorem for T adjoint T and continuity of the positive square root. Conversely, T equals U absolute T, and the composition of a compact operator with a bounded operator is compact.

The same argument applies to every symmetric ideal satisfying the composition rules. For instance, T is Hilbert–Schmidt exactly when its modulus is, and their Hilbert–Schmidt norms agree. The corresponding trace-class statement is also true.

This relationship lets us reduce many ideal inequalities to positive operators. Once an estimate is proved for positive moduli, the polar factor carries it back to arbitrary rectangular maps without altering the gauge.

## Preparing compression and block estimates

In the next lecture we will compress operators to selected subspaces and combine operators into orthogonal block sums. Both operations involve projections, inclusions, and partial isometries, all of which are contractions.

Our result tells us exactly how to control those operations in symmetric ideals. A projection can only decrease the gauge under composition. A canonical polar factor preserves it. These are the building blocks for transporting Davis–Kahan sine, tangent, and residual estimates from geometric operators to their positive singular-value representatives.

The principle to keep is the pair of factorization identities. One gives an inequality in one direction, and the adjoint factorization gives the reverse inequality. That is the complete proof of modulus invariance.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

For T:E→F, |T|=(T* T)^{1/2} acts on E. The canonical polar factor U:E→F is a contraction satisfying T=U|T| and |T|=U* T. Every symmetric ideal gauge obeys gauge(A T B)≤‖A‖ gauge(T) ‖B‖ for bounded composable A,B. Thus gauge(T)≤gauge(|T|) and gauge(|T|)≤gauge(T), giving equality in the extended nonnegative reals. Consequently Mem(T) iff Mem(|T|). No invertibility or equality of source and target dimensions is required.

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
