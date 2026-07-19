/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.FullSineTheta

/-!
# Trusted-dependency audit for the literal paper sine-theta surface

This file is intentionally excluded from ordinary aggregates because its print
commands produce audit output.  Compile it directly after every successful
build of the exact-paper modules and require only Lean's standard foundational
dependencies in every result.
-/

#print axioms ForMathlib.DavisKahan1970.unitaryInvariantNorm_equiv_symmetricNormingFunction
#print axioms ForMathlib.DavisKahan1970.directedCosAngle_eq_modulus
#print axioms ForMathlib.DavisKahan1970.directedSinAngle_eq_modulus
#print axioms ForMathlib.DavisKahan1970.directedSinAngle_singularValues
#print axioms ForMathlib.DavisKahan1970.fullSinAngle_singularValues_projectionDifference
#print axioms ForMathlib.DavisKahan1970.fullSinAngle_norm_projectionDifference
#print axioms ForMathlib.DavisKahan1970.directedCosAngle_real
#print axioms ForMathlib.DavisKahan1970.directedSinAngle_real
#print axioms ForMathlib.DavisKahan1970.lemma6_1
#print axioms ForMathlib.DavisKahan1970.lemma6_2
#print axioms ForMathlib.DavisKahan1970.sinTheta_exactPaper
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_exactPaper
#print axioms ForMathlib.DavisKahan1970.sinTheta_real_exactPaper
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_real_exactPaper
#print axioms ForMathlib.DavisKahan1970.Theorem6_1
#print axioms ForMathlib.DavisKahan1970.Theorem6_1_real
#print axioms ForMathlib.DavisKahan1970.Proposition6_1
#print axioms ForMathlib.DavisKahan1970.Theorem6_2
#print axioms ForMathlib.DavisKahan1970.Theorem6_2_real
#print axioms ForMathlib.DavisKahan1970.Theorem6_2_boundNorm_of_finiteRank
#print axioms ForMathlib.DavisKahan1970.Theorem6_2_real_boundNorm_of_finiteRank
#print axioms ForMathlib.DavisKahan1970.Theorem6_1_commonDomain
#print axioms ForMathlib.DavisKahan1970.Theorem6_2_commonDomain
#print axioms ForMathlib.DavisKahan1970.Theorem6_1_real_commonDomain
#print axioms ForMathlib.DavisKahan1970.Theorem6_2_real_commonDomain
#print axioms ForMathlib.DavisKahan1970.Theorem6_1_equality_every_norm
#print axioms ForMathlib.DavisKahan1970.sineTheta_constant_one_optimal
#print axioms ForMathlib.DavisKahan1970.oneGap_does_not_imply_Proposition6_1
