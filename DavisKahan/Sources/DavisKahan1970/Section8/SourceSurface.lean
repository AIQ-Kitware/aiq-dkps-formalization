/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Sources.DavisKahan1970.Section8.Smallness
import DavisKahan.Sources.DavisKahan1970.Section8.CompressionRepulsion
import DavisKahan.Sources.DavisKahan1970.Section8.SourceTheorem81
import DavisKahan.InfiniteDimensional.TanTheta.ContinuationWitnessAPriori

/-!
# Davis--Kahan 1970 Section 8 source surface

This leaf gives stable source-facing names to the Section 8 results.

**Theorem 8.1 is now promoted** (2026-08-07).  `SourceTheorem81.lean` proves it
from the printed hypotheses alone -- self-adjoint `A` reduced by `P`, the
ordered form gap, and a fully off-diagonal self-adjoint `H` -- with no contour,
no continuation witness, no smallness constant, and no caller-supplied
orientation.  It delivers full spectral repulsion (continuous spectrum
included), the canonical branch as a genuine spectral subspace, the strict
quarter-angle bound, uniqueness of the branch under the printed *closed*
condition, and the printed `iff` between that condition and the spectral
orientation.

What is still *not* promoted:

* the Theorem 8.1 compression / ordered-eigenvalue / symmetric-gauge
  refinements (i)--(iii) instantiated at the canonical branch: the algebraic
  cores are proved (see the `..._of_rotatedBlockData` aliases below and
  `DavisKahan/Frontier/Section8.lean`), but they are not yet fed the canonical
  branch;
* Theorem 8.2, which still needs proofs that either printed half-gap condition
  builds the required common-contour witness; the residual alternative
  additionally needs the Krein replacement theorem.

The aliases below keep the older names working and make the remaining
boundaries visible.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open Set
open scoped InnerProductSpace
open DavisKahanExt

universe v

section SourceAliases

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {A V : H →L[ℂ] H} {s : Set ℝ}

/-- **Source-facing Theorem 8.1: existence of the canonical branch.**

Takes only the printed hypotheses.  Superseded name for
`theorem8_1_canonicalBranch`. -/
alias theorem8_1_source :=
  theorem8_1_canonicalBranch

/-- **Source-facing Theorem 8.1: the printed characterization.** -/
alias theorem8_1_source_characterization :=
  theorem8_1_maximalAngle_le_iff_spectrumIn

/-- **Source-facing Theorem 8.1: uniqueness of the branch.** -/
alias theorem8_1_source_uniqueness :=
  theorem8_1_eq_canonicalBranch_of_maximalAngle_le

/-- Continuation-witness core of Section 8.1.  This is *not* the source
theorem: it takes the branch selection, the contour smallness and the spectral
orientation as caller-supplied data.  Kept because Section 9's continuation
layer consumes it. -/
alias theorem8_1_selectedBranch_and_spectralRepulsion :=
  theorem81CoreConclusion

/-- Source-facing Section 8.2 strict-branch wrapper under an explicit
perturbation half-gap continuation bridge. -/
alias theorem8_2_perturbationHalfGap_selectedBranch :=
  theorem82_branch_of_perturbationHalfGapBridge


/-- Source-facing algebraic core of Theorem 8.1(i), before instantiating the
abstract quadratic data with the concrete direct-rotation sine/cosine blocks. -/
alias theorem8_1_upperCompressionRepulsion_of_rotatedBlockData :=
  upperCompressionRepulsion_of_data

/-- Lower-block companion of the source compression-repulsion inequality. -/
alias theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData :=
  lowerCompressionRepulsion_of_data

/-- The continuation-selected endpoint has a unique contractive graph
coordinate.  This is the graph-theoretic form of selecting the side below the
quarter-turn pole. -/
alias theorem8_selectedEndpoint_existsUnique_contractiveAngularOperator :=
  SpectralContinuationWitness.existsUnique_selectedEndpointAngularOperator

/-- The selected branch satisfies the witness-level a priori tangent bound
once off-diagonality and the ordered form gap are supplied.  This is useful to
Section 9 after the canonical spectral branch has been identified. -/
alias theorem8_selectedBranch_tan_maximalAngle_le_div :=
  SpectralContinuationWitness.tan_maximalAngle_selectedSpectralSubspaces_le_div

end SourceAliases

end Section8
end DavisKahan1970
end TauCeti