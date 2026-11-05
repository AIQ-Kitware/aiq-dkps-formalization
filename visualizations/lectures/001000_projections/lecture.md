# Subspaces and projections

Part of the prerequisite series. Basic vectors, inner products, and matrix
multiplication are assumed. The historical anchor is Gale Young,
[Matrix Approximations and Subspace Fitting (1937)](https://doi.org/10.1007/BF02287962).
It supplies context for least-squares fitting, not a priority claim about
orthogonal projections. Source links and prerequisites are in README.md.

## Pr00Question: How do we describe a whole subspace?

Why: We want to compare spaces without confusing them with a chosen basis.
Recall: $K$ is a subspace; $x$ is an ambient vector.

Suppose a vector is close to a line, but does not lie on it. Which point on the
line should represent that vector? The nearest point gives us a useful operation:
keep the part along the line and remove the perpendicular part. This operation
is an orthogonal projection. It also describes an entire subspace without
choosing particular basis vectors. That is why projections appear throughout
the transport proof. Our goals are to understand their geometry, read their
block coordinates, and explain what it means for another map to commute with
one. We will finish by writing the condition that a map carries one subspace
onto another.

## Pr01History: Fitting data gives the geometry a purpose

Why: The closest-point construction is the local geometry of least-squares fitting.
Recall: A least-squares fit minimizes a sum of squared distances.

There is a practical history behind this picture. In 1937, Gale Young studied
least-squares fitting of linear subspaces to sets of points, connecting the
problem to matrix approximation. The fitted space has a chosen dimension.
For a fixed candidate subspace, each data point
is represented by its nearest point in that subspace. Today we can express
that operation with a projection matrix. The data point splits into a fitted
component and an orthogonal error. The same geometry will let us describe
subspaces in the proof, even when our purpose is transporting spaces rather
than fitting data. The historical reference gives context; we will derive the
projection identities directly.

## Pr02Decomposition: Keep one component and remove the other

Why: Orthogonality explains why the projected point is the closest one.
Recall: $x=Px+(I-P)x$, with the two components perpendicular.

Take K to be the horizontal axis. The vector x has an along-the-line component
and a perpendicular component. Call the first one P x. The remainder is
identity minus P applied to x. These two vectors add to x, and they are
perpendicular. The dashed segment is the error left after replacing x by its
projection.

<!-- beat -->

Why is this replacement the nearest point? Take any other point z on K.
The difference between x and z is the perpendicular error plus the along-the-line
vector P x minus z. Pythagoras says their squared lengths add. The perpendicular
term is unavoidable, while the extra term is nonnegative and vanishes only
when z equals P x. This proves both nearest-point optimality and uniqueness.
The same argument works for a higher-dimensional subspace.

## Pr03Projector: The geometry becomes two matrix identities

Why: A projection packages a subspace as a linear operator.
Recall: $P^2=P$ and $P^T=P$ characterize an orthogonal projector over the reals.

The operation is linear. For the horizontal axis, P is the diagonal matrix
with entries one and zero. Applying it keeps the horizontal coordinate and
removes the vertical coordinate. Apply it again: nothing changes, because its
output is already on K. That is the identity P squared equals P.

<!-- beat -->

Orthogonality supplies the second identity: P transpose equals P. Together,
these identities characterize the orthogonal projection onto its range.
Idempotence alone is insufficient; an oblique projection can satisfy P squared
equals P without projecting perpendicularly. Identity minus P is the projection
onto the orthogonal complement. So every ambient vector has a unique split
into the range of P and the kernel of P, and those two spaces are perpendicular.

## Pr04Frames: Changing the basis does not change the space

Why: Frames are coordinates for a subspace; the projector is independent of those coordinates.
Recall: $E$ has orthonormal columns spanning $K$; $P=EE^T$.

A frame E is a matrix whose columns are an orthonormal basis for K. It turns
a coordinate vector into an ambient vector. Its transpose reads the coordinates
of the orthogonal projection. Consequently, E times E transpose is P.
Here K is the fixed horizontal coordinate plane in three-dimensional space.
The two drawn arrows are its basis vectors, viewed inside that plane.

<!-- beat -->

Rotate both basis vectors within the same plane. The new frame is E times an
orthogonal two-by-two matrix C. Its projector is E C times C transpose E
transpose, which equals E E transpose. The basis arrows moved, but the subspace
did not. This is an important distinction: a transporter may change every
chosen basis vector while still mapping the source subspace onto exactly
the same target subspace.

## Pr05Blocks: A block records where a component goes

Why: Block coordinates describe action on subspaces, not an extra assumption about the map.
Recall: Write vectors as $(x_K,x_\perp)$ in $K\oplus K^\perp$.

Choose orthonormal coordinates adapted to K and its complement. A vector now
has two components. Every linear map T can be written using four blocks in
these coordinates. The first column describes inputs from K: the upper block
is the part of their image that remains in K, and the lower block is the part
that goes into its complement. The second column does the same for complementary
inputs. These blocks may themselves be large matrices.

<!-- beat -->

Multiplying this block matrix by the two-component vector gives the displayed
output. The off-diagonal blocks describe transfer between the two spaces.
Writing blocks does not assert that those transfers vanish. It only names
them. We will need a reason, such as a commutation identity, before we can
replace the general matrix by one with zero off-diagonal blocks.

## Pr06Commutation: Commuting means preserving both pieces

Why: The equation $PT=TP$ has a concrete geometric meaning.
Recall: In adapted coordinates, $P=\operatorname{diag}(I,0)$.

We can now read the equation P T equals T P. Multiplying by P on the left keeps
only the source part of the output. Multiplying by P on the right keeps only
the source part of the input. Compare the displayed block products. Their
equality forces the upper-right and lower-left blocks of T to be zero.

<!-- beat -->

Thus T sends K into K and sends its orthogonal complement into that complement.
Conversely, preserving both pieces gives exactly this block-diagonal form,
so T commutes with P. T can still do something complicated inside either block.
It need not be the identity, and the blocks need not be diagonal matrices.
For an orthogonal T, preserving K alone also forces preservation of the
complement. For a general linear T, we need both conditions.

## Pr07Transport: Encode subspace transport as a projection equation

Why: A geometric constraint becomes an equation we can differentiate or preserve.
Recall: $P=P_K$, $Q=P_L$, and $W$ is orthogonal.

Let W be an orthogonal map carrying K onto L. Conjugating P by W means first
applying W transpose, then projecting onto K, then applying W. This operation
keeps precisely the component along L. Hence W P W transpose is Q, the
orthogonal projection onto L. The animation rotates the source line and
its projector together.

<!-- beat -->

Conversely, the range of W P W transpose is W of K. If this operator equals
Q, that range is L, so W really does transport the subspace. Multiplying by
W on the right gives the equivalent equation Q W equals W P. We have turned
a statement about whole spaces into a matrix identity. In the variations
lecture, we will construct curves that keep this identity true for every
value of the curve parameter.

## Pr08Recap: Read the space, its coordinates, and its constraint

Why: These three translations remove much of the block notation in the matching proof.
Recall: $P=EE^T$; $PT=TP$; $Q=WPW^T$.

Remember three translations. A projector represents a subspace without tying
it to a basis. Commutation with that projector means a map preserves the two
parts of the source decomposition. Orthogonal transport is expressed by
conjugating the source projector into the target projector. A block matrix is
just the map written in those adapted coordinates; zero blocks require a reason.

<!-- beat -->

Try this check. In three-dimensional space, let P keep the first coordinate
and let T rotate the second and third coordinates. Does T commute with P?
Yes. It fixes the source line and rotates within its complement, so no component
crosses between them. T can be far from the identity while commuting with P.
Next we will ask a different question: when a map moves vectors, how should
we measure the total amount of movement?
