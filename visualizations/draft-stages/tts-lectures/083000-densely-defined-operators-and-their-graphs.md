# 083000 — Densely defined operators and their graphs

**Draft status:** audio-first mathematical lecture. **Prerequisites:** `010000` Hilbert spaces, `082000` spectral cutoffs. **Next:** `084000` adjoints of unbounded operators.

<!-- BEGIN SPOKEN LECTURE -->

# Why an operator needs a domain, and what its graph remembers

Imagine an infinite list of numbers. You want a rule that multiplies the first number by one, the second by two, the third by three, and so on. The rule is easy to describe. But there is a question that would never arise for an ordinary finite matrix: can we apply it to every vector in our space?

The answer is no, and understanding that answer will lead us to three ideas: the domain of an operator, its graph, and the graph norm. Together they give a precise way to work with unbounded operators without losing control of limits.

## One formula, two different questions

Our space is called ell two. Its vectors are infinite sequences of real or complex numbers whose squared magnitudes have a finite sum. The length of a sequence is the square root of that sum.

Take the sequence whose entries are one, one half, one third, one fourth, and so on. This is an allowed vector. Its squared entries add to a finite number.

Now apply our proposed rule. Multiply the first entry by one, the second by two, the third by three, and so on. Every output entry becomes one. The resulting sequence is not in ell two: the sum of its squared magnitudes is infinite.

The formula told us what the output coordinates would be. It did not guarantee that those coordinates would form a vector in the space.

That distinction determines the domain. For our operator A, we allow exactly the input sequences for which the sequence obtained by multiplying the N-th coordinate by N is still square summable. Equivalently, the sum of N squared times the squared magnitude of the N-th input coordinate must be finite.

The operator is therefore a rule from this specified domain into ell two. The domain is part of the operator's definition, just as its action is.

The domain is large. Every sequence with only finitely many nonzero entries belongs to it. Given any ell-two sequence, keeping its first N entries and setting the rest to zero produces a finite sequence that approaches it in length. This proves that the domain is dense: every ell-two vector can be approximated arbitrarily well by allowed input vectors.

But dense does not mean equal to the whole space. Our sequence of reciprocals is an explicit vector outside the domain.

## What unbounded actually means

Consider a sequence that is zero everywhere except for a one in coordinate N. Call it the N-th coordinate vector. Its length is one.

After applying A, its only nonzero coordinate is N, so the output length is N. As N gets larger, the output length grows without limit, although the input length stays one.

A bounded operator would have one fixed constant that bounds the output length by that constant times the input length for every allowed input. Here no such constant exists. A is unbounded.

This does not mean that A takes an allowed vector to something of infinite length. That would violate its definition as an operator into ell two. Each allowed input has a legitimate ell-two output. Unbounded means there is no uniform amplification limit across all those inputs.

We now have two different features. The domain is dense but proper, and the operator is unbounded. Neither fact alone tells us whether its behavior is well controlled under limits.

## A limit can leave the domain

Take the reciprocal sequence again, with entries one over N. Form its first truncation, keeping only the first coordinate. Then keep the first two coordinates, then the first three, and so on.

Every truncated sequence is in the domain, and the truncated inputs converge in ell two to the original reciprocal sequence. But that limit lies outside the domain.

What happens to their outputs? After applying A, the first truncation becomes a single one. The second becomes two ones. The N-th becomes N ones. Its output length is the square root of N. Those output vectors do not converge in ell two.

So ordinary convergence of allowed inputs need not produce another allowed input. Yet our example does not show a failure of the operator itself. It shows that input convergence alone is insufficient. We also need to know what happens to the outputs.

This motivates the graph.

## The graph stores the whole input-output pair

Picture the graph of a function from real numbers to real numbers. Each point records both an input and its output. We do the same for an operator, except that each coordinate of the graph point is now a vector in a Hilbert space.

The graph of A consists of every pair formed by an allowed input and its corresponding output. It lives in the product space ell two times ell two.

We say A is closed if its graph is closed in that product space. In more operational language, suppose allowed inputs approach some vector x, and their outputs also approach some vector y. Closedness guarantees that x is an allowed input and that A applied to x really equals y.

Both convergences are required. The reciprocal-sequence truncations do not contradict closedness, because their outputs fail to converge.

Let's prove that our diagonal operator is closed.

Suppose a sequence of legal inputs approaches x, and the corresponding outputs approach y. Fix a coordinate, say coordinate seven. Convergence in ell two implies convergence of every individual coordinate, because the difference at any one coordinate is no larger than the length of the whole difference.

Every approximating output has its seventh coordinate equal to seven times the seventh input coordinate. Passing to the limit, the seventh coordinate of y equals seven times that of x. The same argument works for every coordinate number.

Thus y is exactly the coordinate sequence prescribed by the formula for A applied to x. And because y is in ell two, that coordinate sequence is square summable. So x satisfies the domain condition, and A applied to x equals y.

That establishes closedness. Even though A is unbounded, its graph cannot lose an input-output pair when both sides converge.

## Measuring convergence in both directions

Ordinary vector length measures only the input. For an operator, we often need to control the input and its output simultaneously.

This leads to the graph norm. Take the squared length of the input, add the squared length of its image under A, and then take the square root.

A sequence approaches another sequence in graph norm exactly when its inputs approach each other in ell two and their outputs under A also approach each other in ell two.

Our reciprocal truncations are Cauchy in ordinary ell-two length, but not in graph norm, because the output lengths keep growing. So the graph norm detects the missing domain condition that the ordinary norm overlooks.

Here is a major theorem: an operator between Hilbert spaces is closed precisely when its domain, equipped with the graph norm, is complete.

To understand why, suppose first that A is closed. A graph-norm Cauchy sequence has inputs that are Cauchy and outputs that are Cauchy. The ambient Hilbert space is complete, so both converge. Closedness tells us that the two limits form a legal input-output pair. Therefore the original sequence converges in graph norm.

For the converse, suppose the graph-norm domain is complete. If legal inputs converge to x and their outputs converge to y, then those inputs are Cauchy in graph norm. Their graph-norm limit must be an allowed vector. Uniqueness of the two ordinary limits identifies that vector with x and its image with y. Hence the graph is closed.

Closedness is exactly the completeness needed to pass to limits while keeping the equation intact.

## A dense operator that is not closed

To see what closedness excludes, take the simplest possible formula: send every input to zero. But define this zero operator only on finite-support sequences.

The domain is dense. However, the finite truncations of our reciprocal sequence have a limit outside that domain, while all their outputs converge to zero. The limiting input-output pair is missing from the graph. So this operator is not closed.

It can be repaired by enlarging its domain to all of ell two, keeping the zero formula. That larger operator is the closure of the original one.

Not every operator permits such a repair. Consider another rule on finite-support sequences: add all the coordinates and put the sum in the first output coordinate, leaving every other output coordinate zero.

Take a vector whose first N entries are all one over N, and whose remaining entries are zero. Its input length is one divided by the square root of N, so it approaches zero. But the sum of its entries is always one, so every output is the first coordinate vector.

If we tried to close this graph, the limit would insist that the zero input have a nonzero output, even though linearity also requires zero to map to zero. No single-valued closed extension is possible. This operator is not closable.

The examples separate three properties: having a dense domain, being closed, and being closable. They are different questions.

## What we gain from the graph viewpoint

For a self-adjoint operator, closedness comes automatically. We can also approximate domain vectors by bounded spectral cutoffs. If A is self-adjoint and we keep only spectral values between negative R and positive R, the truncated vector approaches the original domain vector, and its image under A approaches the original output. That is graph-norm convergence.

So an unbounded operator is not an uncontrolled infinite matrix. It is a rule with a domain, and its graph determines which limits preserve the rule.

The model to retain is simple. Ordinary convergence watches the input. Graph convergence watches the input and output together. Closedness tells us that when both converge, the limiting equation remains legal.

<!-- END SPOKEN LECTURE -->

---

## Companion: mathematics and Lean correspondence (display only)

Let \(A:D(A)\subseteq H\to H\). Its graph is \(G(A)=\{(x,Ax):x\in D(A)\}\). The graph norm is \(\|x\|_A=(\|x\|^2+\|Ax\|^2)^{1/2}\). In a Hilbert space, \(A\) is closed if and only if \((D(A),\|\cdot\|_A)\) is complete. For \(A:\ell^2\supset D(A)\to\ell^2\) with \((Ax)_n=nx_n\), \(D(A)=\{x:\sum n^2|x_n|^2<\infty\}\). The map is densely defined, unbounded, and closed. Conversely, zero on \(c_{00}\) is densely defined but not closed.

### Worked distinction: dense, closed, and closable

On \(c_{00}\subset\ell^2\), define
\(Tx=(\sum_{n\ge1}x_n)e_1\), where the sum is finite. For
\(x^{(N)}=N^{-1}\sum_{n=1}^Ne_n\), one has
\(\|x^{(N)}\|=N^{-1/2}\to0\) but \(Tx^{(N)}=e_1\).
Thus \(T\) is densely defined and not closable. By contrast, the zero map
on \(c_{00}\) is densely defined and closable, but not closed; its closure
is the everywhere-defined zero operator.

### Actual source declarations

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `isClosed_iff_range_isClosed`:

```lean
theorem isClosed_iff_range_isClosed
    (f : E →ₗ.[𝕜] F) :
    f.IsClosed ↔ IsClosed (Set.range fun x : f.domain => ((x : E), f x)) := by
```

Its graph-based closedness predicate coincides with the closed-range formulation used in domain restrictions.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `graphNorm`:

```lean
noncomputable def graphNorm (A : E →ₗ.[𝕜] E) (x : A.domain) : ℝ :=
  Real.sqrt (‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2)
```

The graph norm is defined directly on the subtype `A.domain`, not on all of the ambient space.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `graphNorm_sq`:

```lean
theorem graphNorm_sq (A : E →ₗ.[𝕜] E) (x : A.domain) :
    graphNorm A x ^ 2 = ‖(x : E)‖ ^ 2 + ‖A x‖ ^ 2 := by
```

The source makes the sum-of-squares identity exact.

`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` — `norm_apply_le_graphNorm`:

```lean
theorem norm_apply_le_graphNorm (A : E →ₗ.[𝕜] E) (x : A.domain) :
    ‖A x‖ ≤ graphNorm A x := by
```

A graph-norm estimate controls the operator output for vectors in the domain.

**Scope:** The equivalence with graph-norm completeness is derived in the narration; the quoted Lean lemmas formalize its graph and norm components, not an asserted single Lean equivalence theorem. These excerpts are from the supplied source snapshot and are not new compiled Lean code. Reusable `ForTauCeti` constructions have explicit DKPS donor/origin notes; the current file namespace does not imply an external origin.
