/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Sources.DavisKahan1970.Section8.Smallness
import DavisKahan.Experimental.Sources.DavisKahan1970.Section8.CompressionRepulsion
import DavisKahan.Experimental.InfiniteDimensional.TanTheta.ContinuationWitnessAPriori

/-!
# Davis--Kahan 1970 Section 8 source surface

This leaf gives stable source-facing names to the Section 8 results that are
currently proved.  It intentionally does not promote the complete historical
Theorem 8.1 or 8.2:

* Theorem 8.1 still needs construction of the canonical branch directly from
  the unrestricted off-diagonal hypotheses, the converse branch
  characterization, and the compression/eigenvalue/symmetric-gauge repulsion
  refinements.
* Theorem 8.2 still needs proofs that either printed half-gap condition builds
  the required common-contour witness; the residual alternative additionally
  needs the Krein replacement theorem.

The declarations below make those boundaries visible while exposing all
admission-free downstream conclusions to the Section 9 application layer.
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

/-- Source-facing Section 8.1 branch and spectral-exclusion wrapper. -/
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