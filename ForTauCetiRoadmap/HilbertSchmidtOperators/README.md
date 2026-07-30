# Roadmap: Hilbert–Schmidt operators as an `ℓ²` space of columns

**Topic T11 of the candidate design.** Four modules. Depends on T10 (symmetric
operator ideals), and is depended on by T16 (Sylvester equations and the
Rosenblum theorem), which is the only consumer that matters — everything below
is shaped by what T16 needs.

## The theorem this topic exists for

Fix a Hilbert basis `b` of `F`. A bounded operator `T : F →L[𝕜] E` is
Hilbert–Schmidt exactly when its family of columns `i ↦ T (b i)` is
square-summable, and that correspondence is a bijection onto `ℓ²`:

```lean
theorem ofLp_columns (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E)
    (hT : Memℓp (columns b T) 2) :
    ofLp b ⟨columns b T, hT⟩ = T

theorem columns_ofLp (b : HilbertBasis ι 𝕜 F)
    (f : lp (fun _ : ι => E) 2) : columns b (ofLp b f) = f
```

with the `ℓ²` norm being the Hilbert–Schmidt norm:

```lean
theorem norm_sq_eq_tsum_norm_column_sq (b : HilbertBasis ι 𝕜 F)
    (f : lp (fun _ : ι => E) 2) :
    ‖f‖ ^ 2 = ∑' i, ‖ofLp b f (b i)‖ ^ 2
```

So `lp (fun _ : ι => E) 2` *is* the Hilbert–Schmidt space, and it arrives with
Mathlib's completeness, inner product and norm already proved.

## The design decision this topic is really about

**The representation is the substance here, not the theorems.** Hilbert–Schmidt
operators can be realised as a Hilbert *tensor product* `F* ⊗ E` or as `ℓ²` of
columns in a fixed basis. Both are correct. They are not equally cheap.

The donor development (Spectra) took the tensor route and built the tensor
product from scratch: the measured closure was **21,581 lines**. This topic
takes the `ℓ²` route, where `lp` is already in Mathlib with its Hilbert-space
structure, and the whole topic is **four modules**.

That is a roughly three-orders-of-magnitude difference in what has to be
reviewed, and it is worth being explicit that it costs nothing mathematically:
the two models are isomorphic, and the isomorphism is the pair of theorems
quoted above.

**This claim has been tested, not just asserted.** On 2026-07-30, lane HS-PORT
(`eb684f4a`) took a 250-line DKPS module written against the tensor model —
`Spectra.HilbertSchmidtTensor.{Space, toOperator, toOperator_add, toOperator_sub,
toOperator_zero, toOperator_injective, norm_toOperator_le}` — and rewrote it
against this one. Every tensor-model identifier had a one-line counterpart
(`ofLp`, `ofLp_add`, `ofLp_sub`, `ofLp_zero`, `ofLp_injective`, `norm_ofLp_le`),
and the port was a substitution rather than new mathematics. Nothing was lost in
the change of model.

The one place the substitution needed thought is worth recording, because a
reader of the API will hit it too: the model is indexed by the operator's
**domain**, so `T : F →L[𝕜] E` corresponds to `lp (fun _ : ι => E) 2` where `ι`
indexes a basis of `F`. Transposing the operator transposes the index and the
value type together.

## Statement of the objects

```lean
def columns (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) : ι → E := fun i => T (b i)

theorem memLp_columns_iff (b : HilbertBasis ι 𝕜 F) (T : F →L[𝕜] E) :
    Memℓp (columns b T) 2 ↔ T.hilbertSchmidtEnergy b ≠ ⊤

def ofLp (b : HilbertBasis ι 𝕜 F) (f : lp (fun _ : ι => E) 2) : F →L[𝕜] E
```

`columns` and `ofLp` are the two directions; `memLp_columns_iff` is what makes
`columns` land in `lp` at all, and it is stated against Mathlib's existing
`hilbertSchmidtEnergy` so that the topic connects to the ideal theory of T10
rather than redefining "Hilbert–Schmidt".

## The four modules, and why each exists

| Module | What it is for |
|---|---|
| `HilbertSchmidtLp` | The bijection itself: `columns`, `ofLp`, and the two round trips. |
| `HilbertSchmidtSpace` | The three facts a *consumer* uses — injectivity, uniqueness of the representative, and that the `ℓ²` norm is the HS norm. Separated so downstream files need not read the construction. |
| `HilbertSchmidtConjugation` | `‖U ∘ Z ∘ V‖` is unchanged when `U`, `V` are isometries. |
| `HilbertSchmidtPythagoras` | The energy splits along an orthogonal family, on either side, and jointly: `∑_{i,j} ‖P i ∘ Z ∘ Q j‖² = ‖Z‖²`. |

The last two are not general-interest lemmas; they are exactly the two facts
T16 needs, and they are worth stating in this topic rather than that one
because both are statements about the Hilbert–Schmidt norm alone.

`HilbertSchmidtConjugation` is the load-bearing one:

```lean
theorem norm_conj_eq (b : HilbertBasis ι 𝕜 F) (f : lp (fun _ : ι => E) 2)
    (U : E →L[𝕜] E) (hU : ∀ x : E, ‖U x‖ = ‖x‖)
    (V : F →L[𝕜] F) (hV : ∀ x : F, ‖V.adjoint x‖ = ‖x‖)
    (g : lp (fun _ : ι => E) 2) : ...
```

It is what makes the Sylvester flow `W t Z = U_A t ∘ Z ∘ (U_B t)⋆` a *unitary*
group on the Hilbert–Schmidt space, which is the hypothesis Stone's theorem
(T13) is applied under in T16. Without it there is no generator and no
Rosenblum argument.

Its proof is also the clearest evidence for the `ℓ²` choice: the left-hand case
is termwise trivial, since composing with an isometry on the outside changes no
column's norm, and the right-hand case is the same statement about the adjoint.
**No basis-independence argument is needed anywhere**, which in the tensor model
is precisely the part that costs.

## What a reviewer should check

1. **That `memLp_columns_iff` really is Mathlib's notion.** The topic would be
   circular if it defined "Hilbert–Schmidt" as "square-summable columns" and
   then proved the two agree. It does not: the right-hand side is
   `ContinuousLinearMap.hilbertSchmidtEnergy`, which is Mathlib's.

2. **That the basis is a parameter, not a choice.** Every statement carries `b`
   explicitly. Nothing here asserts basis-independence, because nothing here
   needs it — and asserting it would be the one genuinely non-trivial theorem
   in the topic.

3. **That `ofLp` is continuous with `‖ofLp b f‖ ≤ ‖f‖`**, which is what the
   `LinearMap.mkContinuous` in its definition establishes.

## A defect this document surfaced, and its fix

Writing this roadmap found that the elementary facts about `ofLp` were **not all
in this topic**. Of the six identifiers the HS-PORT substitution needed, three
were stated in T16 — in `Sylvester/{Group, SpectralGap, Generator}.lean` —
because that is the topic that first needed them:

| Lemma | Was | Now |
|---|---|---|
| `ofLp_sub` | `Sylvester/Group.lean` (T16) | `HilbertSchmidtConjugation`, beside `ofLp_add` |
| `ofLp_zero` | `Sylvester/SpectralGap.lean` (T16) | `HilbertSchmidtLp`, beside `ofLp` |
| `norm_ofLp_le` | `Sylvester/Generator.lean` (T16) | `HilbertSchmidtLp`, beside `ofLp` |

This was invisible while both topics shipped together, but **T11 is meant to be
submittable before T16**, and as it stood a reviewer reading T11 alone would have
found the Hilbert–Schmidt space defined without the statement that its
representation map is bounded.

All three have been moved (`ofLp_zero` was stated only over `ℂ` and is now
generic in `𝕜`, since the module it moved into is). Nothing else changed: no
proof was touched and the build is unaffected.

## Prerequisites

T10 (symmetric operator ideals and Schatten norms), for `hilbertSchmidtEnergy`
and the ideal framing. Nothing else: `lp` and `HilbertBasis` are Mathlib's.
