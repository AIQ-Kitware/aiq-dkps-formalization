/-
Assumption 2 of Acharyya et al. (2024): the growing-model setting.

The printed assumption reads:

  Let M be a compact Riemannian manifold.  For every model f_i there exists a vector
  phi_i in M subset of R^q such that for all pairs (i,i'), (1/m)||mu_i - mu_i'|| ->
  ||phi_i - phi_i'|| as r -> infinity.

and the dissimilarity function it induces is `Delta^(infinity)(phi_i, phi_i') = ||phi_i -
phi_i'||`.

Two observations about what the assumption actually says.  The distance on both sides of the
limit is the **ambient** norm of `R^q`, not the geodesic distance of `M`; and the conclusion the
assumption is used for -- that the population dissimilarities approach `Delta^(infinity)` -- does
not consume compactness at all.  The Riemannian structure and the compactness are carried for
the cited continuous-MDS theory downstream, not for this step.  Both are recorded in
`AmbientModelLimit` so the assumption is represented at its printed scope, and
`tendsto_frobSub_responseDist_of_ambientLimit` shows exactly which part does the work.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
import Acharyya2024.Common

open scoped BigOperators Topology
open Filter

namespace Acharyya2024.GrowingModels

open Acharyya2024

/--
**Assumption 2**, at its printed scope: latent vectors in a compact subset of an ambient
Euclidean space whose pairwise ambient distances are the limits of the normalized population
dissimilarities.
-/
structure AmbientModelLimit (n q : Nat) {p : Nat} (m : Nat → Nat)
    (μ : ∀ r, Fin n → Mat (m r) p) where
  /-- The model space, a compact subset of the ambient `R^q`. -/
  space : Set (EuclideanSpace Real (Fin q))
  /-- Compactness of the model space (carried for the continuous-MDS theory downstream). -/
  isCompact : IsCompact space
  /-- The latent vector attached to each model. -/
  latent : Fin n → EuclideanSpace Real (Fin q)
  /-- Each latent vector lies in the model space. -/
  latent_mem : ∀ i, latent i ∈ space
  /-- The normalized population dissimilarities converge to the ambient distances. -/
  tendsto : ∀ i j, Tendsto (fun r => ((m r : Real))⁻¹ * ‖μ r i - μ r j‖) atTop
    (𝓝 ‖latent i - latent j‖)

/-- The limiting dissimilarity matrix the assumption induces: `Delta^(infinity)(phi_i, phi_i')
= ||phi_i - phi_i'||`. -/
noncomputable def limitDissimilarity {n q : Nat} (φ : Fin n → EuclideanSpace Real (Fin q)) :
    DisMat n :=
  fun i j => ‖φ i - φ j‖

/--
**What Assumption 2 delivers.**

The population dissimilarity matrices converge in Frobenius norm to the limiting one.  This is
the hypothesis the growing-model consistency chain consumes, and it is exactly the entrywise
convergence the assumption states, assembled over the finitely many pairs.  Compactness of the
model space is not used.
-/
theorem tendsto_frobSub_responseDist_of_ambientLimit
    {n q p : Nat} (m : Nat → Nat) (μ : ∀ r, Fin n → Mat (m r) p)
    (φ : Fin n → EuclideanSpace Real (Fin q))
    (hconv : ∀ i j, Tendsto (fun r => ((m r : Real))⁻¹ * ‖μ r i - μ r j‖) atTop
      (𝓝 ‖φ i - φ j‖)) :
    Tendsto (fun r => frobSub (responseDist (μ r)) (limitDissimilarity φ)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun r => frobSq
      (fun i j => responseDist (μ r) i j - limitDissimilarity φ i j)) atTop (𝓝 0) := by
    have hterm : ∀ i j : Fin n, Tendsto
        (fun r => (responseDist (μ r) i j - limitDissimilarity φ i j) ^ 2) atTop (𝓝 0) := by
      intro i j
      have h := (hconv i j).sub (tendsto_const_nhds (x := ‖φ i - φ j‖))
      have h0 : Tendsto (fun r => responseDist (μ r) i j - limitDissimilarity φ i j)
          atTop (𝓝 0) := by
        simpa [responseDist, responseDistEntry, limitDissimilarity] using h
      simpa using h0.pow 2
    have := tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (fun i _ => tendsto_finset_sum (Finset.univ : Finset (Fin n))
        (fun j _ => hterm i j))
    simpa [frobSq] using this
  have hcomp := (Real.continuous_sqrt.continuousAt (x := (0 : Real))).tendsto.comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hcomp
  simpa [frobSub, frob] using hcomp

/-- The same, packaged from the assumption structure. -/
theorem AmbientModelLimit.tendsto_frobSub {n q p : Nat} {m : Nat → Nat}
    {μ : ∀ r, Fin n → Mat (m r) p} (H : AmbientModelLimit n q m μ) :
    Tendsto (fun r => frobSub (responseDist (μ r)) (limitDissimilarity H.latent)) atTop (𝓝 0) :=
  tendsto_frobSub_responseDist_of_ambientLimit m μ H.latent H.tendsto

end Acharyya2024.GrowingModels
