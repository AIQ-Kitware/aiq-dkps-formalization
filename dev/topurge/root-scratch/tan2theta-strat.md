The correct route is **not** to repair `exists_unboundedApproximateLeadingSingularFamily`. The distilled literature supports a split proof architecture:

```text
GKMV sign/polar argument
        │
        ├── canonical branch and sharp operator norm
        │
        └── contractive angular operator X
                    │
          ordered Sylvester theorem
                    │
      compact B₀₁ ──┴──► compact X
                    │
       domain-compatible exact singular pairs
                    │
          Davis–Kahan §7 Ky Fan summation
                    │
          sharp compact-ideal theorem
```

The fully noncompact maximal-ideal extension is a separate Davis–Kahan Appendix problem. It is not justified by the current approximate-family construction.

## 1. Prove the canonical branch by the GKMV sign/polar argument

For

[
L=
\begin{pmatrix}
A_0&B_{01}\
B_{10}&A_1
\end{pmatrix},
\qquad
A_0\le \alpha<\beta\le A_1,
\qquad d=\beta-\alpha,
]

take the grading involution

[
J=\begin{pmatrix}-I&0\0&I\end{pmatrix}
]

and a shift (\mu\in(\alpha,\beta)). The form associated to (J(L-\mu)) is strictly accretive and sectorial because the perturbation is off-diagonal:

[
JV=-VJ.
]

The GKMV polar-factor argument identifies the polar unitary with

[
J,\operatorname{sign}(L-\mu).
]

That compares the unperturbed grading projection with the **canonical spectral projection** of (L). The sectorial angle gives

[
|P-Q|
\le
\sin!\left(\frac12
\arctan\frac{2|B_{01}|}{d}\right)
<\frac1{\sqrt2}.
]

Consequently the canonical spectral subspace is a graph with angular operator (X), (|X|<1), and

[
\left|2X(I-X^*X)^{-1}\right|
\le \frac{2|B_{01}|}{d}.
]

This proves both:

* the correct quarter-turn branch;
* the sharp operator-norm tan-(2\Theta) theorem.

It never selects spectral-band vectors of (X^*X), so the fat-Cantor domain obstruction is irrelevant.

### Necessary theorem-statement correction

GKMV proves this for the **canonical spectral subspace**, not for an arbitrary contractive reducing graph. The public structure therefore needs either:

* an equality with the relevant spectral projection of (L); or
* a sign-projection/canonical-branch field.

`ContractiveReducingGraphSelection` by itself is too weak to identify the GKMV-selected branch.

## 2. For compact perturbations, make (X) compact using the Riccati equation

Once the canonical graph exists, its angular operator satisfies

[
A_1X-XA_0=XB_{01}X-B_{10}.
]

Suppose (B_{01}) is compact, or belongs to a symmetric ideal whose members are compact. Then:

* (B_{10}=B_{01}^*) is compact;
* (XB_{01}X) is compact;
* hence
  [
  C:=XB_{01}X-B_{10}
  ]
  is compact.

Now invoke the ordered-gap unbounded Sylvester theorem from the Davis–Kahan distillation. The solution operator

[
C\longmapsto X,\qquad A_1X-XA_0=C
]

preserves compactness—and, in the stronger version, the relevant symmetric ideal. Therefore (X) is compact.

This is much cleaner than trying to infer compactness from the nonsharp tan-(2\Theta) companion operator. It uses the genuine Riccati equation and the already-distilled ordered Sylvester machinery.

## 3. Compactness repairs the domain problem

Let

[
T=X^*X.
]

Since (X) is compact, (T) is compact, positive, and self-adjoint. Every nonzero spectral value (\lambda=s^2) is isolated and has finite multiplicity.

The unbounded Riccati development already supplies the ingredients needed to show that (T) preserves (\operatorname{dom}A_0), with a controlled commutator. Therefore its resolvents preserve the graph domain:

[
(z-T)^{-1}\operatorname{dom}A_0
\subseteq \operatorname{dom}A_0.
]

For an isolated nonzero eigenvalue, the Riesz projection

[
P_\lambda
=========

\frac{1}{2\pi i}\oint_\Gamma (z-T)^{-1},dz
]

also preserves (\operatorname{dom}A_0).

Because (\operatorname{dom}A_0) is dense and (P_\lambda) is bounded,

[
P_\lambda(\operatorname{dom}A_0)
]

is dense in (\operatorname{ran}P_\lambda). But the latter is finite-dimensional, so this dense linear subspace is the whole eigenspace. Thus

[
\operatorname{ran}P_\lambda\subseteq\operatorname{dom}A_0.
]

This is the crucial replacement for the false spectral-band density lemma.

The counterexample used a continuous spectral band (L^2(K)). Compactness replaces that band by isolated finite-dimensional Riesz eigenspaces, where the domain argument really works.

## 4. Use exact singular pairs, not approximate graph-domain pairs

Choose an orthonormal eigenbasis (x_j) for the nonzero spectrum of (X^*X):

[
X^*Xx_j=s_j^2x_j,
\qquad x_j\in\operatorname{dom}A_0.
]

Define

[
y_j=\frac{1}{s_j}Xx_j.
]

Domain preservation gives (y_j\in\operatorname{dom}A_1), and now

[
Xx_j=s_jy_j,
\qquad
X^*y_j=s_jx_j.
]

These are the exact domain-compatible singular pairs needed by the original Davis–Kahan §7 argument.

The scalar Riccati calculation gives

[
d,\frac{2s_j}{1-s_j^2}
\le
-2\operatorname{Re}\langle x_j,B_{01}y_j\rangle.
]

Summing the first (k) inequalities and applying the Ky Fan trace-pairing estimate yields

[
d\sum_{j<k}\frac{2s_j}{1-s_j^2}
\le
2\sum_{j<k}s_j(B_{01}).
]

The numbers on the left are precisely the singular values of

[
2X(I-X^*X)^{-1}.
]

Therefore

[
d,\operatorname{KyFan}_k(\tan 2\Theta)
\le
2,\operatorname{KyFan}*k(B*{01})
]

for every (k).

Fan dominance then gives the sharp result for every standard symmetric ideal for which membership implies compactness.

This should cover:

* Schatten (p)-classes, (1\le p<\infty);
* trace class;
* minimal standard completions;
* maximal completions whose sequence space is contained in (c_0);
* other compact symmetric ideals.

The operator norm is already handled independently by GKMV.

## 5. The genuinely remaining case: noncompact maximal ideals

The only unsupported part is the maximal/Fatou setting in which ideal members need not be compact—for example the full operator-norm completion.

The distilled Davis–Kahan literature points to Appendix §6, not to approximate singular families. The likely source-faithful route is:

1. choose finite-rank near-maximizers for the relevant Ky Fan prefixes;
2. control off-block leakage using the distilled Appendix Lemma 6.3;
3. apply the finite-dimensional §7 tan-(2\Theta) theorem to the compressed problem;
4. pass to the limit through the Appendix’s Fan/Fatou argument.

But the repository’s own source census says that this arbitrary-ideal cutoff passage has **not yet been completely audited**. We should reconstruct equations (6.7)–(6.11) from the source before claiming a theorem.

Until that audit is done, the honest general result is:

* sharp operator norm via GKMV;
* sharp compact-ideal theorem via exact singular systems;
* genuine Sylvester theorem with the commutator defect in unrestricted generality.

## Lean restructuring

I would replace the current lane with these modules.

### `TanTwoTheta/UnboundedSignPolar.lean`

Formalize the GKMV argument:

* grading involution;
* off-diagonal anticommutation;
* shifted signed form positivity;
* sectorial representation;
* polar unitary/sign identity;
* canonical spectral projection bound;
* quarter-acuteness;
* sharp operator-norm tan-(2\Theta).

### `TanTwoTheta/CompactExactSingular.lean`

Prove:

```lean
riccatiAngularOperator_compact
rieszProjection_preserves_domain
nonzeroEigenspace_le_domain
exists_exactDomainSingularFamily_of_compact
```

The compactness proof should go through the ordered Sylvester theorem applied to

```lean
X ∘ B01 ∘ X - B10
```

rather than through the approximate-family machinery.

### `DavisKahan/SharpKyFanCompact.lean`

Reuse the existing exact singular-pair scalar estimate and finite Ky Fan summation to prove the compact version.

### `Sources/DavisKahan1970/Section6AppendixTangent.lean`

Treat the full noncompact maximal-ideal result as a separate source-reconstruction lane. Do not let `SharpIdeal.lean` export it before that module exists.

## What remains useful

Keep:

* the bounded `doubleAngleTangentOperator` functional calculus;
* the exact singular-pair scalar inequality;
* the exact-family Ky Fan theorem in `InfiniteTanTwoThetaCore.lean`;
* the domain and adjoint-Riccati work;
* the ordered Sylvester ideal theorem;
* standard Fan dominance;
* the newly proved genuine Sylvester equation with its defect term.

Retire from the unbounded sharp proof:

* `exists_unboundedApproximateLeadingSingularFamily`;
* graph-norm spectral-band selection;
* finite Gram–Schmidt repair of domain vectors;
* the defect-free tan-(2\Theta) Sylvester equation;
* the current unrestricted `SharpIdeal` conclusion.

So the immediate correct target is:

> **GKMV for the canonical branch and operator norm, followed by compactness-through-Riccati-Sylvester and exact singular-pair Ky Fan summation for compact ideals.**

That route is supported by the distilled literature and avoids both counterexamples. The all-maximal-ideal theorem should remain explicitly open until the Davis–Kahan Appendix passage is reconstructed.
