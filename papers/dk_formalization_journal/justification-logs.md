## Prompt:
11/3/2026, 12:38:34 AM

ok let's walk through the proof again. slowly focusing on what each inference step is and why it is justified.

## Response:
11/3/2026, 12:38:40 AM · gpt-6-thinking

> **Starting the proof slowly**
>
> I’m going to separate definitions from deductions and explain why each step follows. I’ll begin with the reduction to two-dimensional planes, then pause before the harder matching argument so each inference stays clear.
>
> **Setting up the reduction**
>
> I’m defining the principal angles first, then grouping each angle into a two-dimensional geometric block. This is justified because the relevant subspaces decompose orthogonally, so costs can be analyzed block by block.
>
> **Deriving the first bound**
>
> I’m now forming orthogonal principal planes, where each angle becomes a separate two-dimensional block. Any matching assembles these blocks, and blockwise costs add, proving the constructed cost is an upper bound on the true optimum.
>
> **Started the proof, set up the reduction, and derived the first bound**
>
> 
>
> Worked for 24s

Let's work through the proof of **Theorem 5, the real trace-norm matching theorem**, one inference at a time.

I want to separate two things throughout this discussion\:

1. **What we are trying to establish.**
2. **Why each step actually follows from the preceding facts.**

We'll start with the geometry and derive the first half of the theorem. Then we'll tackle the much harder direction, which explains why an arbitrary orthogonal transformation cannot beat the best matching.

## Step 1: State the optimization problem precisely

We have two subspaces of the same dimension\:

$$
K,L\subseteq\mathbb R^N,
\qquad
\dim K=\dim L=d.
$$

For example, you can continue imagining two three-dimensional subspaces of six-dimensional space.

We want an orthogonal transformation $W$ satisfying

$$
W(K)=L.
$$

This is our **feasibility constraint**\.

Notice that we are *not* requiring $W$ to send any particular basis vector of $K$ to a particular basis vector of $L$\.

We only require that the image of the entire subspace be $L$\.

Among all such transformations, we minimize

$$
\boxed{\|I-W\|_1.}
$$

The subscript one means the trace norm: add all singular values of the displacement operator.

That is the problem. We haven't introduced matching yet.

## Step 2: Use the SVD to establish the geometry

From our earlier discussion, you know that the SVD gives us the principal angles

$$
\theta_1,\theta_2,\ldots,\theta_m,
$$

where these are the **strictly positive principal angles, counted with multiplicity**\.

For every principal angle $\theta_i$, the SVD gives corresponding unit vectors

$$
u_i\in K,\qquad v_i\in L.
$$

They satisfy

$$
\langle u_i,v_j\rangle
=
\begin{cases}
\cos\theta_i,&i=j,\\
0,&i\ne j.
\end{cases}
$$

In words, each source principal vector has an aligned target principal vector, and all the cross-pair inner products vanish.

**Why is this justified?**

Because if $X^\top Y=U\Sigma V^\top$, changing the orthonormal bases to $XU$ and $YV$ makes their overlap matrix diagonal.

That's what the SVD accomplished.

Now here's the next inference.

For each positive angle, define a new unit vector

$$
q_i
=
\frac{v_i-\cos\theta_i\,u_i}{\sin\theta_i}.
$$

Let's understand that expression before proceeding.

We take the target direction $v_i$, subtract its component along $u_i$, and normalize what remains.

Consequently,

$$
v_i=\cos\theta_i\,u_i+\sin\theta_i\,q_i.
$$

This is just ordinary two-dimensional trigonometry.

And $u_i$ is orthogonal to $q_i$\.

Furthermore, the SVD orthogonality relations imply that the pairs corresponding to different indices are mutually orthogonal.

Therefore we can construct

$$
\boxed{\Pi_i=\operatorname{span}(u_i,q_i).}
$$

Each $\Pi_i$ is a two-dimensional principal plane, and different principal planes are orthogonal.

### Why this matters

We have just established that the geometry of the two subspaces decomposes into independent, orthogonal two-dimensional pieces.

That conclusion was **derived from the SVD**, not assumed.

For two three-dimensional subspaces with three positive angles, we obtain

$$
\mathbb R^6=\Pi_1\oplus\Pi_2\oplus\Pi_3.
$$

We can now reason about individual principal planes without disturbing the others.

---

## Step 3: Construct a transporter from a matching

Suppose we decide to pair angles one and two, leaving angle three unmatched.

That is a matching containing one edge\:

$$
M=\{\{1,2\}\}.
$$

What does this mean geometrically?

We group the first two principal planes into one four-dimensional space\:

$$
\Pi_1\oplus\Pi_2.
$$

We construct a coupled orthogonal transporter on that four-dimensional space.

For the third principal plane, we construct an independent two-dimensional transporter.

Then we combine the two maps into a single ambient orthogonal transformation.

**Why are we allowed to combine them?**

Because the spaces on which they act are orthogonal.

If $W_{12}$ acts orthogonally on the first four-dimensional block and $W_3$ acts orthogonally on the remaining two-dimensional block, then

$$
W=W_{12}\oplus W_3
$$

is also orthogonal.

It preserves inner products within each block, and the blocks are orthogonal to one another.

This explains why matching edges cannot share vertices.

We are building a decomposition into disjoint blocks. A principal plane cannot belong simultaneously to two of them.

## Step 4: Why do the costs add?

Now comes our first important optimization inference.

The displacement operator of this block-diagonal transporter is

$$
I-W=(I-W_{12})\oplus(I-W_3).
$$

The singular values of a block-diagonal operator are the singular values of its blocks, combined into one list.

Since the trace norm is the **sum** of singular values,

$$
\boxed{
\|I-W\|_1
=
\|I-W_{12}\|_1+\|I-W_3\|_1.
}
$$

This additivity is what makes the graph construction work.

If we were measuring only the largest singular value, for example, the combined cost would instead be the maximum of the block costs.

But for the trace norm, the costs add.

The paper establishes two local cost formulas.

An independently transported principal plane of angle $\theta$ has minimum cost

$$
s(\theta)=\min\left\{4\sin\frac{\theta}{2},\,2\right\}.
$$

The first option comes from the direct planar rotation; the second comes from a reflection.

Two coupled principal planes with angles $\theta$ and $\psi$ have an attainable four-dimensional transport cost

$$
e(\theta,\psi)=4\sin\frac{\theta+\psi}{2}.
$$

For now, we're using the existence of these local transporters. We'll examine the paired construction and its optimality separately.

Our example matching therefore has total cost

$$
C(M)=e(\theta_1,\theta_2)+s(\theta_3).
$$

For an arbitrary matching, we get

$$
C(M)=
\sum_{\{i,j\}\in M}e(\theta_i,\theta_j)
+
\sum_{i\text{ unmatched}}s(\theta_i).
$$

---

## Step 5: The first inequality of the theorem

Now we're ready for a subtle but fundamental logical step.

We have established that **every matching produces a feasible orthogonal transporter with the corresponding matching cost**\.

Let

$$
\mathrm{OPT}
=
\min_{\substack{W\in O(N)\\W(K)=L}}\|I-W\|_1.
$$

Since each matching produces one of the feasible transformations over which we're minimizing,

$$
\mathrm{OPT}\leq C(M)
$$

for every matching $M$\.

Therefore,

$$
\boxed{
\mathrm{OPT}\leq\min_M C(M).
}
$$

**Why does the inequality point in that direction?**

Because minimizing over *all possible orthogonal transporters* cannot give a worse answer than minimizing over the special transporters constructed from matchings.

This is the first half of the theorem.

And notice what we have **not** proved\:

$$
\mathrm{OPT}\geq\min_M C(M).
$$

An arbitrary orthogonal transporter might mix all three principal planes together, rather than using our two-dimensional and four-dimensional blocks.

Perhaps doing that could achieve an even smaller trace norm.

We have not ruled that out.

That possibility is exactly what makes the main proof difficult.

---

## Where we are in the proof

**Construction direction**

$$
\mathrm{OPT}\leq\min_M C(M)
$$

Every matching can be realized by a valid orthogonal transporter.

**Global optimality direction** NEXT

$$
\mathrm{OPT}\geq\min_M C(M)
$$

We must show that unrestricted orthogonal transformations cannot do better.

The second direction is where the manuscript introduces Schatten exponents between one and two, first-order optimality conditions, a spectral gradient, an emergent complex structure, and finally the reduction to small invariant blocks.

**Before proceeding, here's the key distinction I want to make sure is clear\:** the SVD proves that the *two subspaces* admit an orthogonal principal-plane decomposition. It does **not** prove that an *optimal transporter* respects that decomposition.

In fact, our coupled rotation deliberately does not respect the individual principal planes.

The difficult part of the matching theorem is proving that even though arbitrary mixing is permitted, there is always a globally optimal transporter whose mixing can be organized into disjoint pairs of principal planes.

That's the next inference we need to justify.

## Prompt:
11/3/2026, 12:48:18 AM

yes I'm understanding now

## Response:
11/3/2026, 12:48:25 AM · gpt-6-thinking

> **Establishing existence**
>
> I’m taking the next small step: the feasible set is nonempty and compact because orthogonal maps can match equal-dimensional subspaces, while the constraint stays closed. A continuous objective therefore attains a minimizer.
>
> Worked for 5s

Good. Now we're ready for the harder half of the proof.

Recall what we still need to establish\:

$$
\boxed{\mathrm{OPT}\geq \min_M C(M)}
$$

We must prove that **no arbitrary orthogonal transporter can outperform the best matching**\.

## Step 6: Start with a global minimizer

The first inference is that a global minimizer actually exists.

Why?

We are searching over orthogonal matrices satisfying

$$
W(K)=L.
$$

Three facts justify existence.

1\. **The feasible set is nonempty.** Since $K$ and $L$ have equal dimensions, we can choose orthonormal bases for both, extend them to bases of the ambient space, and construct an orthogonal matrix mapping one basis onto the other.

2\. **The feasible set is compact.** The orthogonal group is closed and bounded in finite-dimensional matrix space, and the constraint $W(K)=L$ defines a closed subset.

3\. **Our objective is continuous.** The singular values of $I-W$, and hence their sum, vary continuously with $W$\.

Therefore a minimum is attained.

This matters because we can now select an actual optimal transporter, call it $W_*$, and investigate its properties.

We aren't assuming that $W_*$ has any particular block structure.

---

## Step 7: Introduce a smoother optimization problem

The trace norm sums the singular values of displacement\:

$$
\|I-W\|_1=\sum_j \sigma_j(I-W).
$$

The problem is that the trace norm is not differentiable everywhere.

So the manuscript considers, for $1<p<2$,

$$
\Phi_p(W)=\sum_j \sigma_j(I-W)^p.
$$

This new function is differentiable, including where displacement singular values vanish.

We can repeat the compactness argument to select a global minimizer $W_p$ of this smoother objective.

**Here is the important inference\:** Because $W_p$ is globally optimal, it must also be locally optimal along every smooth path of *feasible* orthogonal transformations.

That gives us permission to use derivatives.

But we cannot perturb $W_p$ arbitrarily, because most perturbations would stop mapping $K$ onto $L$\.

Our next task is therefore to construct perturbations that automatically preserve the transport constraint.

That's where the expression

$$
W_p\exp(tB)
$$

enters the proof.

The question we'll answer next is: **What conditions must $B$ satisfy so that this is an orthogonal transformation carrying $K$ onto $L$, for every $t$?**

Once we understand that, we'll be able to derive the first-order optimality condition rather than simply accepting it.

## Prompt:
11/3/2026, 12:51:00 AM

I'm following

## Response:
11/3/2026, 12:51:12 AM · gpt-6-thinking

Good. Let's derive the next inference carefully, because this is where the proof starts extracting information about an otherwise arbitrary optimal transporter.

## Step 8: Constructing feasible perturbations

We have selected a global minimizer $W_p$ of the smoother objective

$$
\Phi_p(W)=\sum_j \sigma_j(I-W)^p,
\qquad 1<p<2.
$$

It satisfies

$$
W_p(K)=L.
$$

We want to vary $W_p$ slightly, compute how the objective changes, and use the fact that a minimum cannot improve under a small perturbation.

But we must preserve two conditions\:

1. The perturbed transformation must remain orthogonal.
2. It must continue mapping $K$ onto $L$\.

### First: How do we preserve orthogonality?

Take a skew-symmetric matrix $B$, meaning

$$
B^\top=-B.
$$

The matrix exponential

$$
Q(t)=\exp(tB)
$$

is orthogonal for every real $t$\.

**Why?**

Because

$$
Q(t)^\top Q(t)
=\exp(-tB)\exp(tB)
=I.
$$

The two exponentials are inverses.

Therefore,

$$
W(t)=W_p\exp(tB)
$$

is orthogonal, since it is the product of two orthogonal matrices.

So the first constraint is handled.

---

### Second: How do we preserve the subspace mapping?

This is the more interesting constraint.

Imagine $K$ is the ordinary $xy$\-plane in four-dimensional space.

We can rotate vectors **within** the $xy$\-plane without changing the plane itself.

For example, a 30-degree rotation inside $K$ changes its basis vectors but still maps $K$ onto itself.

We can independently rotate its orthogonal complement, too.

Let's call any such transformation $Q$\.

Then

$$
Q(K)=K.
$$

Now compose it with our optimal transporter\:

$$
W_p(Q(K))=W_p(K)=L.
$$

Therefore, $W_pQ$ is still a valid transporter.

This is precisely the freedom we exploited in our coupled-rotation example: **we're allowed to change how individual source vectors are mapped, provided the destination subspace remains the same.**

### Express that condition algebraically

Let $P$ be the orthogonal projection onto $K$\.

We require our perturbation generator $B$ to commute with $P$\:

$$
\boxed{BP=PB.}
$$

Why does that work?

Commuting with $P$ means that $B$ preserves both $K$ and its orthogonal complement.

Its exponential therefore preserves them as well.

Consequently,

$$
\exp(tB)(K)=K.
$$

And hence

$$
\boxed{W_p\exp(tB)(K)=L.}
$$

We have constructed an entire curve of feasible transporters.

Importantly, these variations capture all the local freedom in the constraint: every orthogonal transporter from $K$ onto $L$ differs from $W_p$ by right multiplication with an orthogonal map preserving $K$\.

---

## Step 9: Apply the minimum condition

Define the scalar function

$$
f(t)=\Phi_p(W_p\exp(tB)).
$$

We know three things\:

- $f(0)=\Phi_p(W_p)$\.
- Every point along this curve is feasible.
- $W_p$ is globally optimal.

Therefore,

$$
f(t)\geq f(0)
$$

for all $t$\.

And because the objective is differentiable for our chosen exponent $p$,

$$
\boxed{f'(0)=0.}
$$

**This is our first new necessary condition on the unknown optimal transporter.**

We haven't assumed any special structure for $W_p$\. The condition follows just from optimality.

---

## Step 10: Introduce the spectral gradient

The derivative calculation in the paper's proof can be represented as

$$
\boxed{f'(0)=-\operatorname{tr}(GB),}
$$

where $G$ is a skew-symmetric matrix determined by $W_p$ and the objective.

For now, think of $G$ as encoding the first-order sensitivity of displacement cost to rotations.

The minimum condition tells us

$$
\operatorname{tr}(GB)=0
$$

for **every skew-symmetric $B$ that commutes with $P$**\.

That word *every* is important.

We can choose $B$ to rotate within $K$, within its orthogonal complement, or independently within both.

Let's choose coordinates adapted to the decomposition

$$
\mathbb R^N=K\oplus K^\perp.
$$

Then our permitted generators have block form

$$
B=
\begin{pmatrix}
B_1&0\\
0&B_2
\end{pmatrix},
$$

where $B_1$ and $B_2$ are skew-symmetric.

Write the gradient in the same coordinates\:

$$
G=
\begin{pmatrix}
G_{11}&G_{12}\\
-G_{12}^\top&G_{22}
\end{pmatrix}.
$$

Because the trace of a matrix only sees its diagonal blocks,

$$
\operatorname{tr}(GB)
=
\operatorname{tr}(G_{11}B_1)
+
\operatorname{tr}(G_{22}B_2).
$$

This must vanish for every choice of $B_1$ and $B_2$\.

We can choose $B_1=-G_{11}$ and $B_2=0$\. Since $G_{11}$ is skew-symmetric, this is permitted, and the resulting trace condition forces $G_{11}=0$\.

Similarly, $G_{22}=0$\.

Therefore,

$$
\boxed{
G=
\begin{pmatrix}
0&G_{12}\\
-G_{12}^\top&0
\end{pmatrix}.
}
$$

## What did we just prove?

**The spectral gradient of an optimal transporter has no component acting entirely within the source subspace or entirely within its orthogonal complement.**

It only has off-diagonal blocks coupling those spaces.

That is a substantial restriction, derived entirely from the first-order optimality condition.

And it's exactly what we need for the next step.

Define the reflection

$$
J=2P-I.
$$

It acts as positive one on $K$ and negative one on $K^\perp$\.

In our block coordinates,

$$
J=
\begin{pmatrix}
I&0\\
0&-I
\end{pmatrix}.
$$

Conjugating our off-diagonal gradient by $J$ changes its sign\:

$$
\boxed{JGJ=-G.}
$$

This relation is called **anticommutation**\.

And in the next step, we'll combine it with another fact from the derivative calculation\:

$$
GW_p=W_pG.
$$

One matrix anticommutes with the source reflection, but commutes with the optimal transporter.

Those two relationships are what eventually allow us to decompose the optimal transporter into small invariant blocks.

For now, the inference to retain is\:

**Global optimality implies zero derivative along every feasible rotation. Those zero derivatives force the gradient to be off-diagonal relative to the source subspace.**

## Prompt:
11/3/2026, 12:54:42 AM

ok I'm going to need to study that some more to really understand, but I have the flight level of the motivation and want to see the rest through in this style. it's really helping.

## Response:
11/3/2026, 12:54:49 AM · gpt-6-thinking

> **Planning proof continuation**
>
> I’m continuing the proof from the established flow: identify the skew generator, analyze its spectral structure and phase behavior, justify the pairing cost, and then pass carefully to the limiting case \(p\to1\).
>
> **Refining spectral decomposition**
>
> I’m establishing that \(G^2\) commutes with both \(J\) and \(W\), so each positive spectral level carries a complex structure. The scalar derivative has at most two relevant phases, enabling finite-dimensional pairing blocks.
>
> **Canonical block argument**
>
> I’m noting that phase counting alone isn’t sufficient. I’ll invoke the needed canonical-form step: each spectral level reduces to real two- or four-dimensional blocks, where rotations and reflections can be compared explicitly.
>
> **Constructing paired transport**
>
> I’m checking the four-dimensional pairing carefully: unequal principal angles require an explicit construction, not just phase counting. I’ll state the block result cautiously and verify its cost before extending the argument.
>
> **Continuing the proof**
>
> I’m carrying the argument through the remaining stages: isolate zero-gradient directions, decompose positive levels into small invariant blocks, compare local costs, then pass continuously to \(p=1\).
>
> **Refined spectral decomposition and continued the canonical block proof**
>
> 
>
> Worked for 53s

Good. We'll carry the proof all the way to the matching formula. You don't need to master every algebraic step yet. For this pass, I want you to see **what each inference accomplishes, what justifies it, and why the next step becomes necessary**\.

We have already done the setup and established that\:

1. Every matching produces a feasible orthogonal transporter.
2. Therefore, the global optimum cannot be greater than the best matching cost.
3. To prove the reverse inequality, we select a minimizer of a smoother Schatten power objective, with exponent between one and two.
4. First-order optimality gives us a skew-symmetric spectral gradient $G$\.
5. If $J$ is the reflection across the source subspace, then

$$
\boxed{JGJ=-G.}
$$

That last identity is where we stopped. It says that the gradient couples the source subspace to its orthogonal complement, rather than acting independently within either one.

Now let's see what we can infer from that.

## Step 11: The gradient also commutes with the optimal transporter

Let $W$ be our minimizer for the smooth objective.

The derivative calculation produces another property\:

$$
\boxed{GW=WG.}
$$

Why?

Our objective is the sum of powers of the singular values of $I-W$\.

Because $W$ is orthogonal, its complex eigenvalues lie on the unit circle. We can describe them using rotation angles, sometimes called eigenphases.

The displacement cost depends only on those eigenphases, not on the eigenvectors used to represent $W$\.

When we differentiate this spectral cost, the resulting gradient is a function of $W$ through spectral calculus.

And a function of an operator commutes with that operator.

That's where the commutation relation comes from.

So we now have two relationships\:

$$
JGJ=-G,
\qquad
GW=WG.
$$

Let's interpret them.

The first says the gradient interacts with the source-subspace decomposition in a very particular way.

The second says the gradient is compatible with the optimal transporter's spectral structure.

**We're going to combine these relationships to find smaller spaces that the transporter cannot mix with one another.**

---

## Step 12: Square the gradient

This is a clever algebraic move.

Start with

$$
JGJ=-G.
$$

Multiply the relationship by itself. We get

$$
JG^2J=G^2.
$$

So although $G$ anticommutes with $J$, its square **commutes** with $J$\.

And because $G$ commutes with $W$, its square also commutes with $W$\.

Therefore,

$$
\boxed{G^2J=JG^2,\qquad G^2W=WG^2.}
$$

Why is this helpful?

Because $G$ is skew-symmetric.

That means $G^2$ is symmetric and negative semidefinite.

Consequently, $-G^2$ is a symmetric, positive semidefinite operator.

We know how to decompose a real vector space using the eigenspaces of a symmetric operator.

So consider an eigenspace where

$$
-G^2=g^2I
$$

for some nonnegative number $g$\.

Because $-G^2$ commutes with both $J$ and $W$, **that eigenspace is preserved by both transformations**\.

And remember, $J$ determines the projection onto our source subspace\:

$$
P=\frac{I+J}{2}.
$$

So the eigenspace is also preserved by $P$\.

The target projection is

$$
Q=WPW^\top.
$$

It follows that the eigenspace is preserved by $Q$ as well.

This is our first major structural conclusion\:

**The original optimization problem decomposes into smaller invariant spaces determined by the gradient.**

We haven't established that those spaces have dimension two or four.

But we've found a way to decompose the problem that respects the source subspace, the target subspace, and the transporter simultaneously.

That's progress.

---

## Step 13: A complex structure emerges

Now take one of those invariant spaces where $g$ is strictly positive.

Recall that

$$
G^2=-g^2I
$$

on this space.

Divide $G$ by $g$\. Define

$$
C=\frac{G}{g}.
$$

Then

$$
\boxed{C^2=-I.}
$$

You should recognize this algebraic identity.

It's the defining property of multiplication by the imaginary unit.

In an ordinary real two-dimensional plane, the matrix

$$
C=
\begin{pmatrix}
0&-1\\
1&0
\end{pmatrix}
$$

rotates vectors by ninety degrees.

Apply it twice and you've rotated by 180 degrees, which negates every vector.

That's exactly why its square is negative identity.

So our operator $C$ behaves like multiplication by $i$\.

**We have discovered a complex structure inside our real vector space.**

This is not changing the underlying real optimization problem into a different problem.

Rather, we're discovering that part of the original real space has a natural way to be interpreted using complex coordinates.

### What happens to the reflection $J$?

Since $J$ anticommutes with $G$, it also anticommutes with $C$\:

$$
JC=-CJ.
$$

In complex coordinates, this means $J$ behaves like complex conjugation.

Think of the ordinary complex plane.

Multiplying by $i$ rotates ninety degrees.

Complex conjugation reflects across the real axis.

And if you conjugate a vector before multiplying by $i$, you get the negative of what happens when you multiply by $i$ before conjugating.

That's exactly the relationship we have.

Meanwhile, $W$ commutes with $C$, so it acts as a complex-linear unitary transformation in these coordinates.

### Why was this step necessary?

We started with a real orthogonal matrix that could have complicated behavior across many dimensions.

We now have a complex-coordinate representation in which its spectral phases are easier to analyze.

But we still need to show why those phases force small blocks.

---

## Step 14: The scalar displacement cost restricts the possible rotation angles

Remember why we introduced an exponent between one and two.

We want to differentiate the displacement cost.

For an eigenphase $t$, the corresponding displacement magnitude is

$$
2\left|\sin\frac{t}{2}\right|.
$$

So its contribution to the Schatten power objective is

$$
f_p(t)=\left(2\left|\sin\frac{t}{2}\right|\right)^p.
$$

Let's focus on angles between zero and 180 degrees.

The derivative of this function starts at zero, increases, reaches a maximum, and then decreases back to zero.

Here's the important property.

For a fixed positive value of the derivative, there can be **at most two distinct angles** producing that value.

One angle lies on the increasing side of the curve.

The other lies on the decreasing side.

Why does that matter?

Because on our chosen gradient eigenspace, the gradient has a fixed magnitude $g$\.

The corresponding eigenphases of $W$ must therefore solve the same scalar derivative equation.

And that equation admits at most two solutions.

So we get\:

$$
\boxed{\text{At most two eigenphases on each positive gradient level.}}
$$

This is a major restriction.

An arbitrary orthogonal matrix can have many different rotation angles.

A minimizing matrix, once restricted to one of these gradient levels, can have at most two.

Notice the logical progression\:

- Optimality gave the gradient equations.
- The gradient equations gave invariant subspaces.
- The scalar derivative then restricted the spectral possibilities inside those subspaces.

We are steadily removing degrees of freedom from our unknown minimizer.

---

## Step 15: From two eigenphases to two-dimensional and four-dimensional blocks

This is probably the most technically demanding inference in the proof.

We now know that, on a positive gradient level, $W$ has at most two eigenphases when viewed in the complex coordinates constructed from $G$\.

But that fact alone does **not** prove that the entire invariant space has dimension four.

An eigenphase could have high multiplicity.

We need an additional decomposition argument.

The manuscript uses the Hermitian spectral projections associated with those phases, together with the conjugation structure coming from $J$\.

The relevant projection can be represented in an orthogonal form that separates the space into smaller real invariant components.

Those components have real dimension two or four.

Crucially, the decomposition respects not only $W$, but also the source and target projections.

That's what allows us to interpret the resulting components geometrically.

A two-dimensional component carries one positive principal angle.

A four-dimensional component can carry two positive principal angles.

This is the point where the matching structure begins to emerge.

### Connect this to our visualization

Remember our four-dimensional coupled rotation.

We had two orthogonal principal planes.

The direct rotation acted independently on both.

The competing transporter acted on a different diagonal two-dimensional plane and fixed its orthogonal complement.

That was one example of four-dimensional mixing.

The structural theorem says that, for the smooth optimization problem, we can find an optimal transporter assembled from small blocks of precisely the kind needed for single principal angles or pairs.

We're no longer assuming this because the example looked promising.

We're obtaining it from the optimality equations and the spectral decomposition.

---

## Step 16: What about the zero-gradient space?

We considered eigenspaces where $g$ is positive.

But $-G^2$ might also have a zero eigenspace.

On that space, $G=0$, so we cannot divide by $g$ to obtain a complex structure.

The proof handles this case separately.

The zero-gradient condition constrains the transporter to reflection-type behavior. Applying the two-projection decomposition again gives small invariant blocks.

The proof also rules out certain unnecessary negative-one blocks.

For example, suppose an invariant real line is mapped to itself by multiplication by negative one.

If changing that action to positive one preserves the source-to-target constraint, we should make that change.

Why?

Because negative one moves every vector on that line by twice its length, whereas positive one moves nothing.

That strictly lowers the objective.

A global minimizer cannot contain such an avoidable displacement.

After handling these cases, we have our structural conclusion\:

**There exists an optimal transporter decomposable into two-dimensional and four-dimensional real blocks, together with directions that remain fixed.**

This is the hard structural part of the proof.

---

## Step 17: Each block must itself be optimal

Now we can make a simpler inference.

Suppose our globally optimal transporter decomposes as

$$
W=W_1\oplus W_2\oplus\cdots\oplus W_r.
$$

Every block preserves the relevant source and target pieces.

Imagine that block number two is not the cheapest possible transporter for its local source and target subspaces.

Then we could replace $W_2$ with a cheaper local transporter.

We would leave every other block unchanged.

The resulting ambient map would still be orthogonal and would still map the full source subspace onto the full target.

But its total displacement cost would be lower.

That contradicts global optimality.

Therefore\:

$$
\boxed{\text{Every block of a global minimizer is locally optimal.}}
$$

This is the exact point where we can turn the structural decomposition into a cost calculation.

A two-dimensional block gives us a singleton principal-angle problem.

A four-dimensional block gives us a two-angle problem.

And the local optimization determines the cost of each.

---

## Step 18: The blocks become a matching

Let's return to our example of two three-dimensional subspaces in six-dimensional space.

Suppose their positive principal angles are

$$
30^\circ,\quad45^\circ,\quad75^\circ.
$$

The structural result says we can obtain an optimal transporter using blocks containing at most two principal angles.

So the possibilities are exactly\:

- Three independent singleton blocks.
- Pair thirty and forty-five, leaving seventy-five single.
- Pair thirty and seventy-five, leaving forty-five single.
- Pair forty-five and seventy-five, leaving thirty single.

There is no permissible block containing all three positive principal angles that we still need to consider.

**That's the conclusion that makes matching exhaustive.**

The structural theorem has ruled out the possibility that mixing all three principal planes simultaneously produces a strictly better global optimum.

We now only need to compare costs for disjoint singletons and pairs.

For the nuclear norm, those costs are\:

$$
s(\theta)=\min\left\{4\sin\frac{\theta}{2},2\right\}
$$

for a singleton, and

$$
e(\theta,\psi)=4\sin\frac{\theta+\psi}{2}
$$

for a coupled pair.

One subtlety: the four-dimensional block may be cheaper when implemented as two independent singleton transports. Matching allows that possibility simply by leaving the vertices unmatched.

Therefore, the cost of an optimal block decomposition is at least the minimum over all matchings.

And every matching is achievable by constructing its corresponding blocks.

We now have both directions of the optimization argument-at least for the smoother Schatten power family, using its corresponding local costs.

---

## Step 19: Return to the nuclear norm

There's one final mathematical obstacle.

Everything in our structural argument was developed for exponents strictly between one and two.

But the theorem we want uses exponent one.

So we let the exponent decrease toward one.

We need to justify moving the optimization through this limit.

Here's why that works.

First, our ambient space is finite-dimensional.

Second, the feasible set of orthogonal transporters is compact.

Third, all displacement singular values lie between zero and two.

Therefore, the functions obtained by raising displacement singular values to the power $p$ converge uniformly to the ordinary singular-value sum as $p$ approaches one.

Uniform convergence matters because we are minimizing over an entire set of matrices.

It ensures that the minimum values converge, not merely the cost of some one fixed matrix.

Meanwhile, the local block minima converge to the singleton and paired nuclear costs.

And there are only finitely many matchings for a fixed number of principal-angle occurrences.

So we can pass to the limit in the finite minimum over matchings.

The result is the desired identity\:

$$
\boxed{
\min_{\substack{W\in O(N)\\W(K)=L}}\|I-W\|_1
=
\min_M
\left(
\sum_{\{i,j\}\in M}e(\theta_i,\theta_j)
+
\sum_{i\text{ unmatched}}s(\theta_i)
\right).
}
$$

We have reached the theorem.

The left side searches over all orthogonal transformations satisfying the subspace-mapping constraint.

The right side searches over a finite collection of disjoint angle pairings.

The equality says they have exactly the same minimum.

---

## Step 20: From the theorem to a matching algorithm

Now we can implement the result.

Suppose the principal angles are already known from the SVD.

First, calculate the cost of leaving every positive angle unmatched\:

$$
C_0=\sum_i s(\theta_i).
$$

Next, for every pair of distinct angle occurrences, calculate the savings from coupling them\:

$$
\boxed{
g_{ij}=s(\theta_i)+s(\theta_j)-e(\theta_i,\theta_j).
}
$$

A positive saving means coupling is cheaper.

A negative saving means we should prefer the two independent singleton transports.

We build a complete weighted graph with one vertex for every positive principal-angle occurrence.

Each edge receives its savings as its weight.

Then we find a matching of maximum total savings.

This is a **general-graph maximum-weight matching problem**, for which algorithms such as Edmonds' blossom algorithm are appropriate.

We cannot generally just select the highest-saving edge repeatedly, because selecting an edge prevents using any other edge touching either endpoint.

Finally, subtract the maximum matching savings from $C_0$\.

That gives the exact minimum nuclear displacement.

We can also construct an attaining orthogonal transformation by combining the singleton and paired transport blocks selected by the matching.

---

## The entire proof, seen from above

**SVD of the two subspaces**

Produces principal angles and mutually orthogonal principal planes

**Select a smooth-objective global minimizer**

Compactness guarantees existence

**Differentiate along feasible rotations**

Optimality forces gradient identities

**Spectral-gradient decomposition**

An emergent complex structure and a two-phase restriction

**Small invariant blocks**

The difficult structural result: only one- and two-angle blocks are needed

**Local costs add**

Singletons and disjoint pairs describe the optimum

**Take the limit to the nuclear norm**

Uniform convergence preserves the minimum

**Maximum-weight matching**

Solves the original unrestricted transport optimization

## What I want you to retain

The theorem has three logically distinct achievements.

**First**, principal-angle geometry lets us describe the relative position of the two subspaces using orthogonal two-dimensional planes.

**Second**, and most importantly, the first-order optimality argument proves that an unrestricted optimal transporter can be organized into blocks involving at most two of those principal planes. This is the step that rules out more complicated global mixing.

**Third**, once that structure is established, the nuclear norm becomes additive across the blocks, and the continuous optimization reduces to a discrete matching problem.

The hardest inference is the second one. In particular, the step from the spectral-gradient conditions to the two-dimensional and four-dimensional block decomposition deserves its own careful study. The complex structure and two-phase argument are ingredients in that step, not substitutes for the block-decomposition proof.

But you've now seen the entire route from the original subspace-transport question to the matching algorithm, including why the construction gives an upper bound, why the structural argument gives the reverse bound, and why the passage to exponent one is justified.
