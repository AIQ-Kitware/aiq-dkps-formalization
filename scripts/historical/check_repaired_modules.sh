#!/usr/bin/env bash
# Historical regression check for compiler-repaired modules.
#
# Drops from the mathematics agent arrive as overlays produced against an older
# snapshot, so a later overlay can silently revert an earlier compile repair.
# This script rebuilds every module that has been repaired to zero errors and
# reports any that regressed, together with the commit that fixed it, so the
# repair can be recovered with `git show <commit> -- <path>`.
#
# Retained for archaeology; this is not a current repository gate.
# Usage:  bash scripts/historical/check_repaired_modules.sh
# Exit:   0 if every listed module builds, 1 otherwise.
#
# When a module is repaired to zero errors, add it here with its fixing commit.

set -uo pipefail
cd "$(dirname "$0")/../.."

# "<lean module name>|<fixing commit>|<short note>"
REPAIRED=(
  "DavisKahan.Experimental.InfiniteDimensional.Core.ReducingRestriction|8091633|orientation of the orthogonal splitting"
  "DavisKahan.Experimental.InfiniteDimensional.Core.ClosedOperatorComplexification|493a847|coordinate continuity and resolvent transport"
  "DavisKahan.Experimental.InfiniteDimensional.Ideals.ComplexificationApproximation|d1da075|basis index binder and span induction"
  "DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.RealSpectralRestriction|35db5c2|conjugation descent of spectral projections"
  "DavisKahan.Sources.DavisKahan1970.FullPartIII|35db5c2|restored the bounded generalized import"
  "DavisKahan.Experimental.InfiniteDimensional.Core.ReducingRestrictionExtras|cb18fff|completeness instance reinstalled"
  "DavisKahan.Experimental.InfiniteDimensional.SinTheta.NaturalReducing|cb18fff|completeness instance and splitting orientation"
  "DavisKahan.Experimental.InfiniteDimensional.SinTheta.NaturalBounded|1e16b6c|obligations addressed by name"
  "DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.RealSpectrumBridge|1e16b6c|shadowing namespace removed"
  "DavisKahan.Experimental.InfiniteDimensional.SinTheta.NaturalExamples|db1bfbe|bounded operator reductions forced"
  "DavisKahan.Sources.DavisKahan1970.FullPartIIIExtensions|db1bfbe|extension root"
  "Spectra.Modular.KMS.Condition|f15350b|vendored, had never compiled"
  "DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperSingularValueTransport|4c4e929|congruence applied to inequalities"
  "DavisKahan.Experimental.InfiniteDimensional.Core.PaperOperatorAngle|00028fd|four defects behind elaboration failures"
  "DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperSubspaceSingularTransport|3966a84|heterogeneous singular sequence"
  "DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNorm|3966a84|prefix rewrites and finiteness"
  "DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationBlockSum|d307141|direct sum majorization, proof written"
  "DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperTheorem61Universal|73872e1|trivial branch and projection unfolding"
  "DavisKahan.Experimental.InfiniteDimensional.Ideals.OperatorModulusApproximation|74c563c|rectangular Gram positivity"
  "DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperProjectionBlocks|8b88b93|rewrite directions and over-rewrite"
  "DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNormLaws|8b88b93|Ky Fan triangle capability, heterogeneous estimate"
  "Spectra.Spaces.Tensor.Hilbert|454ff8b|pure tensor notation pinned the scalar by a named argument"
  "Spectra.Spaces.Tensor.HilbertSchmidt|b1b66a0|conjugate foundation, transport, column expansion"
  "Spectra.YosidaHille.RectangularIntertwining|6dbaf5a|generator domain density import, orbit derivative"
  "Spectra.SpectralTheory.SeparatedIntertwiner|2b37194|spectral and Born measure namespaces"
  "DavisKahan.Experimental.InfiniteDimensional.Sylvester.PairwiseSpectrumGap|879aa7d|lambda token used as a spectral variable"
  "DavisKahan.Experimental.InfiniteDimensional.Sylvester.PairwiseHomogeneousUniqueness|b1b66a0|generator namespace, split qualified name"
  "DavisKahan.Experimental.InfiniteDimensional.Sylvester.HomogeneousUniqueness|dbd7b76|norm of zero and a nonlinear product"
  "Spectra.OneParameterUnitaryGroup.Product|4ee5e89|pipeline operator binds looser than equality"
  "Spectra.SpectralTheory.Calculus.SpectralGapInverse|4ee5e89|spectral measure namespace, antitone inverse"
  "DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidtBasis|6eeb643|span image closed by reflexivity"
  "Spectra.Spaces.Tensor.HilbertSchmidtFlow|1e3e924|dense inductions applied, invented closedness lemma"
  "Spectra.Spaces.Tensor.HilbertSchmidtGeneratorBridge|13e3357|unbundled linearity absent from the restricted simp set"
  "Spectra.Spaces.Tensor.HilbertSchmidtSpectralGap|801a470|notation and measure namespaces, higher order factorisation"
  "DavisKahan.Experimental.InfiniteDimensional.Sylvester.PaperHilbertSchmidtDefectFirst|11ed50a|qualified names split after their dot"
  "DavisKahan.Experimental.InfiniteDimensional.Sylvester.PaperHilbertSchmidtPairwise|11ed50a|obligation order, complexified spectrum orientation"
  "DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperTheorem62|2cb8239|identity norm needs a nontrivial space"
)

fail=0
for entry in "${REPAIRED[@]}"; do
  IFS='|' read -r mod commit note <<< "$entry"
  errs=$(lake build "$mod" 2>&1 | grep -c "error:")
  if [ "$errs" -eq 0 ]; then
    printf 'ok       %s\n' "$mod"
  else
    fail=1
    path="$(echo "$mod" | tr '.' '/').lean"
    printf 'REGRESSED %s (%s errors)\n' "$mod" "$errs"
    printf '          fixed in %s -- %s\n' "$commit" "$note"
    printf '          recover: git show %s -- %s\n' "$commit" "$path"
  fi
done

if [ "$fail" -eq 0 ]; then
  echo "All repaired modules still build."
else
  echo "Some repaired modules regressed; see above." >&2
fi
exit "$fail"
