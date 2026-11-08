# 109000 — Directed sine as a rectangular modulus

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `035000` operator modulus; `042000` principal angles; `043000` cross projections; `108000` complementary Sylvester equation. **Next:** `110000` the single-angle sine theorem.

<!-- BEGIN SPOKEN LECTURE -->

# Directed sine as a rectangular modulus

Let X be the bounded overlap map that takes trial coordinates into the exact complementary spectral coordinates. A residual identity makes X solve a Sylvester equation, so a gap between the trial and complementary spectra controls its norm. The remaining geometric step is to identify the singular values of X with the sines of the directed principal angles.

The main identity is a Gram-operator calculation. It works for real or complex Hilbert spaces, for finite-dimensional or infinite-dimensional trial spaces, and without choosing individual principal vectors.

## Define the two projections

Let U be the exact target subspace of a Hilbert space H. Write P for the orthogonal projection onto U. Let E be an isometry from a trial-coordinate Hilbert space F into H. Its range is the trial subspace V.

Split E into two parts. The component inside the target space is C equals P E. The component outside is S equals the identity minus P, composed with E.

The maps C and S both start in F and end in H. Their ranges are orthogonal, because one lands in U and the other in U perpendicular. Their sum is E.

Because E preserves lengths, the sum of the squares of the output lengths of C and S equals the input length squared. In operator language, C adjoint C plus S adjoint S equals the identity on F.

The positive square roots of these two Gram operators are the cosine and sine magnitudes associated with the trial space relative to the exact target. Their eigenvalues are the squared cosines and squared sines of the directed principal angles, because the two orthogonal components of each unit trial vector have squared lengths summing to one.

## Construct the sine modulus

Consider S adjoint S. Since S equals the identity minus P times E, and the complementary projection is self-adjoint and idempotent, S adjoint S equals E adjoint times the identity minus P times E.

This is a positive operator on the trial-coordinate space F. Its unique positive square root is the modulus of S, written absolute value of S.

For a unit coordinate vector x, the squared norm of S x is the amount of the trial vector E x that lies outside U. The largest such amount is the square of the operator norm of S.

In finite dimensions, diagonalize S adjoint S. Its eigenvalues lie between zero and one. If they are the squares of numbers s one, s two, and so on, those s values are the singular values of S. Define each directed angle theta by sine theta equals the corresponding s, with theta between zero and ninety degrees.

This definition is geometrically natural. A trial vector already lying in U produces sine zero. A trial vector perpendicular to U produces sine one, corresponding to a right angle. Intermediate values measure how much of the vector escapes the exact target.

## Replace ambient escape with exact complementary coordinates

Now choose an isometric coordinate map F one whose range is U perpendicular. The projection onto U perpendicular is F one F one adjoint.

Define X equal to F one adjoint E, the same map as in the complementary Sylvester equation. It sends trial coordinates to coordinates in U perpendicular.

Compute X adjoint X. It equals E adjoint F one F one adjoint E. Replace F one F one adjoint by the identity minus P. We get E adjoint times the identity minus P times E.

That is exactly S adjoint S.

Therefore X and S have the same Gram operator, the same positive modulus, and the same singular values where those are defined. The directed sine operator on F is their common modulus.

There is a subtle point here. S and X have different codomains. They do not have to be equal maps. Their identical Gram operators mean that they encode the same lengths and principal-angle data. For symmetric ideals that are invariant under rectangular isometries and polar factors, that is exactly enough to transfer both membership and gauge bounds.

## Work out the plane

Let U be the horizontal axis in the real plane. Choose a unit trial vector u with coordinates cosine theta and sine theta. The trial-coordinate space is one-dimensional, so E sends a scalar t to t times u.

The complementary projection removes the horizontal coordinate. Therefore S applied to one is sine theta times the vertical basis vector.

If F one identifies the complement with the real line, X applied to one is the scalar sine theta. The maps have different outputs, a plane vector versus a scalar, but they have the same modulus: multiplication by the absolute value of sine theta.

At thirty degrees, that modulus is one half. At ninety degrees, it is one. At zero degrees, it is zero.

This verifies the geometric and algebraic definitions in the simplest setting.

## A two-dimensional trial space can have two different directed angles

Now work in three-dimensional space. Let the exact target U be the plane spanned by the first two coordinate axes. Let the trial space V be the plane spanned by the first and third axes.

Choose E whose columns are the first and third basis vectors. The first trial vector lies entirely in U, so its escape under the complementary projection is zero. The second trial vector lies perpendicular to U, so its escape has length one.

The singular values of S are therefore one and zero, or equivalently the directed principal angles are ninety and zero degrees, in descending sine order.

This example illustrates why an operator or an entire list of sines is often more informative than a single angle. A largest-angle bound controls the worst direction. A Frobenius bound controls the combined squared escapes, and Ky Fan or symmetric-ideal bounds control cumulative singular-value information.

If the trial dimension exceeds the target dimension, there must be a trial direction perpendicular to the target, by a dimension argument. Its directed sine is one. For infinite dimensions, dimensional statements require more care, but the rectangular modulus continues to make sense without enumerating eigenvectors.

## Prove trial-basis independence

Suppose we change the orthonormal trial coordinates by a unitary map W. The new trial map is E W. Its escape map becomes S W. Its complementary-coordinate map becomes X W.

The new Gram operator is W adjoint S adjoint S W. The positive square root transforms in the same way, by the uniqueness of the positive square root or functional calculus. Thus the new sine modulus is W adjoint absolute value of S times W.

Unitary conjugation changes the matrix representation on the trial-coordinate space, but not its spectrum, singular values, or unitarily invariant norm.

Likewise changing the exact complementary frame F one by a unitary coordinate transformation only multiplies X by a unitary on the left. It leaves X adjoint X unchanged.

Our directed sine geometry depends on the two subspaces, not on the particular coordinates used to describe them.

## Distinguish directed from symmetric angles

The construction starts from V and measures its escape from U. Reversing the direction means starting with an isometric frame for U and measuring escape from V. These directional maps can have different numbers of singular values and different zero or right-angle multiplicities when dimensions differ.

For equal finite dimensions the nonzero principal-angle information agrees in the usual paired convention. But the source-indexed rectangular operator retains the correct multiplicities for the direction actually used by a residual theorem.

The ambient projection difference P minus the trial projection is yet another angle representative. Its modulus describes a symmetric subspace gap. It agrees with the largest directed sine in common equal-dimensional acute situations, but we should not identify every list or ideal norm without checking the dimensional and multiplicity conventions.

## The resulting geometric estimate

We now have both ingredients. The complementary Sylvester equation controls X in terms of the compressed residual. The Gram identity identifies the modulus of X with the directed sine operator. Consequently a suitable Sylvester estimate becomes a principal-angle estimate with no further approximation.


<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let `P=F₀F₀*`, `S=(I−P)E`, and `X=F₁*E` with `F₁F₁*=I−P`. Then `S*S=E*(I−P)E=X*X`, hence `|S|=|X|`. Under trial frame change `E↦EW`, the modulus conjugates by `W`. The resulting source-indexed sine operator is rectangular; ideal membership and gauge transport use invariance of complete singular-value/approximation-number data.

### Source declaration excerpts

`DavisKahan/Geometry/Angle/SinAngle.lean` — `spectraSinAngleOperator` (exact declaration header; body omitted):

```lean
noncomputable def spectraSinAngleOperator
    (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : H →L[ℂ] H :=
```

`DavisKahan/Sources/DavisKahan1970/SineTheta/AngleIdentity.lean` — `sourceDirectedAngleC_eq_arcsin_sineModulus` (exact declaration header; body omitted):

```lean
theorem sourceDirectedAngleC_eq_arcsin_sineModulus
    (U V : Submodule ℂ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    directedAngleBlockC U V =
      cfc Real.arcsin (sineBlockModulusC U V) :=
```

**Mapping.** `spectraSinAngleOperator` is an *ambient symmetric* modulus of a projection difference, which is distinct from the directed rectangular `sinThetaEmbedding`/`directedSinThetaOperator`. The `AngleIdentity` results connect a directed angle block to the `arcsin` of its sine modulus. The paired equality of `S*S` and `X*X` explains why the theorem may use the complementary-coordinate representative without asserting the maps themselves equal.
