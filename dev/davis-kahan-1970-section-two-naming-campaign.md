# Section 2 declaration-naming campaign, 2026-08-30

The four Section 2 theorem families carried names that recorded how a proof was
once obtained rather than what the theorem says.  `sinTheta_headline_generic`
did not say it was the interval/exterior branch; `tanTheta_headline_generic_directed`
did not say it was finite-dimensional; `wholeSpace` meant *ambient*; a bare
`_exact` could mean either "spectral separation" or "the packaged endpoint"; and
`TauCeti.DavisKahan1970.SectionTwo.sinTheta` read as the canonical sine theorem
while naming the complex one.

This was a **rename campaign only**.  No statement, hypothesis, proof or
dependency changed.  The measured evidence is that the comparator signature
pre-flight reports exactly the same eight findings before and after, one-to-one
under the rename, on real builds of both trees.

## Rules

* `TauCeti.DavisKahan1970.SectionTwo` is reserved for the four paper-facing families.
* The short names `sinTheta`, `tanTheta`, `sinTwoTheta`, `tanTwoTheta` are reserved
  for the full-source-scope statement that is also generic over `RCLike 𝕜`.  **They
  are bound to nothing**: no such declaration exists for any of the four.  Do not
  bind one of them to a fixed-field statement.
* Fixed-field forms always say `_complex` or `_real`; scalar-generic forms say `_rclike`.
* The tokens `headline`, `wholeSpace`, bare `generic` and bare `exact` are banned.
  `wholeSpace` became `ambient`; `exact` became whichever of `spectralGap`,
  `orderedForm` or the packaging distinction it actually meant.
* `directed` versus `ambient` is used only where it is a real distinction.
* Restrictions are exposed: `finiteDimensional`, `finiteSubspace`, `bounded`,
  `unbounded`, `boundedRitz`, `unboundedRitz`.
* The norm layer is exposed outside the canonical interface: `paperUINorm`,
  `idealFamily`, `symmetricIdealFamily`, `kyFan`, `opNorm`, `uiNorm`.
* `of_transversality` means the caller supplies `‖sin Θ‖ < 1`; `of_crossedDefects`
  means the caller supplies the standing condition (3.5); `of_poleExclusion` means
  the caller supplies `cos 2θ ≠ 0` on the angle spectrum.
* A conclusion stated on a proof representative rather than on the paper's angle
  operator says `blockRepresentative`, or `arbitraryRepresentative` when the
  representative is quantified over.

Names are **differential**: a token may be omitted where it does not discriminate,
but a token that is present must be true of the declaration.  That is the property
`dev/davis-kahan-1970-section-two-naming-classification.json` records and that the
`token_commitments` map in it makes checkable.

## Classification table

`dev/davis-kahan-1970-section-two-naming-classification.json` has one row per
renamed declaration with the columns `old_name`, `new_name`, `trig_family`,
`paper_role`, `scalar_scope`, `dimension_scope`, `operator_scope`, `ritz_scope`,
`angle_scope`, `norm_scope`, `gap_scope`, `conclusion_representation` and
`canonical_status`, plus the controlled vocabulary for each column.

Six rows were corrected against the proposed names during the audit, in every case
because the conclusion is a proof representative and the proposed name hid it:
the ideal-gauge and unitary-invariant unbounded `sin 2Θ`/`tan 2Θ` surfaces conclude
on `sinTwoThetaIdealBlock` / `tanTwoThetaIdealBlock`, not on the angle operator, so
they carry `blockRepresentative`.  Two further rows separated
`SymmetricOperatorIdealFamily` (`symmetricIdealFamily`, `gaugeReal`) from
`KyFanDominantIdealFamily` (`idealFamily`), which the old `_gauge` / `_uiNorm`
suffixes did not distinguish.

## Declarations removed

Two declarations were duplicates and are gone rather than renamed.

* `TauCeti.DavisKahan1970.sinTheta_complex` aliased exactly what
  `sinTheta_bundled_complex` aliases.
* `TauCeti.DavisKahan1970.tanTwoTheta_headline_generic` restated
  `tanTwoTheta_branchFree_bounded_finiteSubspace_paperUINorm_rclike` with a
  literally identical type and a forwarding proof.

Three `canonical_*` aliases in `FullPartIII.lean` were also removed:
`canonical_sinTheta`, `canonical_generalizedSinTheta` and
`canonical_generalizedSinTheta_complementaryBlock` claimed canonical status for
complex-only bundled entry points, which is the claim this campaign reserves for
the scalar-generic form.  Their consumers now name the declarations directly.

## Not done

Module *paths* still carry the banned words -- `SineTheta/HeadlineGeneric.lean`,
`HeadlineGeneric.lean`, `TanThetaWholeSpace.lean`, `SinTwoThetaWholeSpace.lean`,
`WholeSpaceReal.lean`, `TanTwoThetaWholeSpace.lean`.  Renaming modules moves
imports, generated aggregates, staging registries and census module paths, and is
a separate change from renaming declarations.
