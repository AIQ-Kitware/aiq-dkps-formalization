# Full-source notation census (lexical inventory)

**Scope:** This is a source-wide *lexical* listing of TeX math-mode tokens in the active manuscript input graph, discovered recursively from `paper.tex`, including generated PGF figure labels. It is not an assertion that every mathematical object is semantically registered. Local proof variables and the meanings of unregistered expressions require editorial classification. The generated figures are inspected as rendered-source inputs; their Python generators remain the source of truth for rebuilding them.

The companion `NOTATION_OCCURRENCES.csv` records every detected occurrence with its source file, line, column, and containing line. It includes standard math operators, digits, punctuation, and scripts so there is an evidence trail for *all* math-mode source tokens, not just proposed symbols. Neither report changes the typeset notation.

## Coverage and status

- Semantic registry: **229 typed entries** (71 glossary, 158 local).
- Documented source alternatives: **23** (21 from DK 1970), across 23 semantic keys.
- Scoped Lean sine-theta binder correspondences: **13** semantic keys.
- Math regions scanned: **1191** (appendices.tex: 268, counterexample.tex: 137, figures/Fig1.pgf: 14, figures/Fig2.pgf: 54, figures/Fig3.pgf: 19, formalization_enabled_extension.tex: 295, paper.tex: 404).
- Occurrence records: **8059**; category counts: registered-key=2487, standard-operator=1929, syntax=1384, raw-symbol=705, number=677, semantic-variant=330, registered-glyph=270, layout=197, registered-wrapper=80.
- Registered references in math: **2757**, spanning **179 keys**.
- Raw mathematical atoms: **705 occurrences**, **84 distinct printed TeX forms** (including indices/superscripts).
- Derived semantic variants (`\like` or scripted `\sym`/`\symglyph`): **330 occurrences**, **117 distinct source forms**; these may still contain raw indices.
- Raw commands needing classification: **0 occurrences**, **0 distinct commands**.
- Raw forms exactly matching a registered glyph: **31** distinct forms; **53** have no exact match; all raw occurrences still bypass `\sym`.
- Scan errors: **0** (zero is necessary for lexical coverage).

### Source checksums (SHA-256)

- `math_symbol_colors.tex`: `d71bc03ddc82da3763a847d0bad9a9dc954d61613ad9bb48edc62e568795985c`
- `paper.tex`: `93760cbcbe74d7069f08c0710d55576a6fd03f2120863a9bc6ea42249d3299ac`
- `figures/Fig1.pgf`: `6b343d6c4eb7d2b85df2e7f4de52d430a500dddfb66bf5a59e58b1f6c6294904`
- `counterexample.tex`: `b354bcfb6e1ac690ca5503a6e1ff187ce138cbc418abde548ba3101750d91839`
- `formalization_enabled_extension.tex`: `eca9ae2205b42607205ee5fdca91a85d363b7647051c090ee8faeb5968eb6f13`
- `appendices.tex`: `33f6e9a14363c87bc0bfa9562fa630953b47dabe050e95024e0d126c14857ece`
- `figures/Fig2.pgf`: `e5d4ad6c9af0caaf788b8c9844d224375f9590c5975104069bc80209f32beb7d`
- `figures/Fig3.pgf`: `7c368d9051a90d623c11232ff0511f5826db805c3baef2b8c17c301aa52de097`

The scanner encountered no unmatched math delimiters or malformed semantic wrappers.

### Census by source file

| Source file | Math regions | Semantic uses | Raw atoms |
|---|---:|---:|---:|
| `appendices.tex` | 268 | 576 | 149 |
| `counterexample.tex` | 137 | 416 | 62 |
| `figures/Fig1.pgf` | 14 | 21 | 4 |
| `figures/Fig2.pgf` | 54 | 81 | 30 |
| `figures/Fig3.pgf` | 19 | 26 | 1 |
| `formalization_enabled_extension.tex` | 295 | 755 | 305 |
| `paper.tex` | 404 | 882 | 154 |

## Unified printed-glyph index: registered meanings and raw uses together

This is the primary holistic table. Every glyph known to the central registry and every raw math atom observed in the manuscript/PGF labels appears here. Multiple registry keys for the same glyph are shown together; these **are not assumed semantically equivalent**. A raw count above zero means the glyph still appears outside central control at those locations. The `glossary` and `local` designations are declarations, not inferred.

| Exact TeX glyph | Registered meanings (`key`: glossary status; definition) | Raw occurrences | Sample raw locations |
|---|---|---:|---|
| `(I-T)q` | `DisplacementVector` (local): Difference between a unit input and its image under the displayed orthogonal map. | 0 | — |
| `0_2` | `ZeroMatrixTwo` (local): Two-by-two zero matrix. | 0 | — |
| `A` | `A` (glossary): Reference self-adjoint operator before perturbation.<br>`Ablock` (local): Positive cosine-related block in the two-subspace decomposition.<br>`HistoricalSylvesterRight` (local): Right-hand coefficient A in the historical Sylvester equation. | 0 | — |
| `A_0` | `ReferenceBlock0` (glossary): Reference operator restricted to the source subspace in Section 8. | 2 | `paper.tex:1020`, `appendices.tex:508` |
| `A_1` | `A1` (local): Complementary block of the reference operator.<br>`ReferenceBlock1` (glossary): Reference operator restricted to the source complement in Section 8. | 0 | — |
| `A_{\mathrm{trial}}` | `TrialOperator` (glossary): Self-adjoint operator on trial coordinates; its eigenvalues are the trial spectral values. | 0 | — |
| `B` | `B` (local): Off-diagonal perturbation or coupling block.<br>`SylvesterLeft` (glossary): Left coefficient of the Sylvester equation; corresponds to the unwanted spectral block.<br>`Bblock` (local): Off-diagonal block in the two-subspace decomposition.<br>`SkewDirection` (local): Skew-symmetric direction for a first variation of an orthogonal transporter. | 22 | `paper.tex:747`, `paper.tex:891`, `paper.tex:1157`, `appendices.tex:270` |
| `B^*` | **UNREGISTERED** | 1 | `paper.tex:747` |
| `B^{-1}` | **UNREGISTERED** | 1 | `appendices.tex:413` |
| `C` | `SylvesterRight` (glossary): Right coefficient of the Sylvester equation; corresponds to the trial operator.<br>`Cblock` (local): Complementary or Sylvester block in the two-subspace decomposition.<br>`Cturn` (glossary): Planar rotation through twice the principal angle in the counterexample.<br>`PairCosineBlock` (local): Diagonal principal-cosine block.<br>`TraceCost` (glossary): Trace-norm displacement cost of the indicated orthogonal transporter or matching.<br>`HalmosCosineBlock` (local): Cosine block in the Halmos two-projection representation. | 18 | `paper.tex:891`, `appendices.tex:270`, `appendices.tex:272`, `appendices.tex:274` |
| `C_0` | `SingletonBaseline` (local): Trace displacement when every angle uses its singleton transporter. | 1 | `appendices.tex:246` |
| `C_0^2` | **UNREGISTERED** | 1 | `appendices.tex:350` |
| `C_1` | `ComplementCosineBlock` (local): Cosine of the complementary angle block in the spectral-repulsion inequality. | 1 | `appendices.tex:246` |
| `C_j` | **UNREGISTERED** | 1 | `appendices.tex:247` |
| `C_p` | `MatchingPowerCost` (local): Total paired and singleton power cost of a matching. | 0 | — |
| `D` | `Rrotation` (glossary): Canonical direct rotation carrying the source subspace onto the target.<br>`SourceDirectRotation` (local): Direct rotation, including the nonacute case in the source-result table.<br>`Dblock` (local): Auxiliary diagonal or block matrix in the counterexample.<br>`Dplanar` (local): Planar direct-rotation block.<br>`PairDirectRotation` (local): Direct rotation on the two principal planes. | 2 | `figures/Fig2.pgf:216`, `figures/Fig2.pgf:489` |
| `D_0` | `CrossedSourceDefect` (glossary): Source directions perpendicular to the target subspace. | 0 | — |
| `D_1` | `CrossedTargetDefect` (glossary): Target directions perpendicular to the source subspace. | 0 | — |
| `E` | `SpectralMeasure` (glossary): Projection-valued spectral measure of a self-adjoint operator.<br>`GradientPhaseProjection` (local): Projection onto the first phase space in a gradient-level space. | 0 | — |
| `E_0` | `E0` (glossary): Isometric embedding of the trial subspace; its adjoint returns trial coordinates. | 0 | — |
| `E_1` | `E1` (local): Isometric coordinates for the complementary trial subspace. | 0 | — |
| `F^2` | **UNREGISTERED** | 1 | `formalization_enabled_extension.tex:266` |
| `F_0` | `F0` (glossary): Isometric coordinates for the desired exact spectral subspace; star denotes the adjoint. | 0 | — |
| `F_1` | `F1` (glossary): Isometric coordinates for the exact complementary subspace; star denotes the adjoint. | 0 | — |
| `G` | `SpectralGradient` (local): Skew-symmetric spectral gradient of the displacement power sum in the matching proof. | 0 | — |
| `G_{01}` | `GradientOffDiagonal` (local): Complement-to-source block of the skew-symmetric gradient. | 0 | — |
| `H` | `H` (glossary): Additive self-adjoint perturbation of the reference operator.<br>`Hreflection` (local): Planar reflection carrying the source line to the target. | 0 | — |
| `H_0` | `H0` (local): Wanted diagonal block of the perturbation. | 0 | — |
| `H_1` | `H1` (local): Unwanted diagonal block of the perturbation. | 0 | — |
| `H_{\mathrm{mix}}` | `Hmix` (glossary): Orthogonal mixing matrix in the counterexample. | 0 | — |
| `I` | `Identity` (local): Identity operator on the space in context. | 10 | `paper.tex:1109`, `paper.tex:1111`, `paper.tex:1114`, `formalization_enabled_extension.tex:505` |
| `I_2` | `IdentityTwo` (local): Two-by-two identity matrix. | 1 | `counterexample.tex:59` |
| `I_4` | `IdentityFour` (local): Four-by-four identity matrix. | 0 | — |
| `J_0` | `Jturn` (glossary): Planar rotation through $\pi/2$, with square minus the identity. | 0 | — |
| `J_2` | `PairPlanarReflection` (local): Fixed planar reflection used to parametrize determinant -1 factors. | 0 | — |
| `J_{\mathrm{ang}}` | `AngleGenerator` (glossary): Skew angle generator in the direct-rotation result summaries. | 0 | — |
| `J_{\mathrm{src}}` | `Jreflect` (glossary): Reflection equal to twice the source projection minus the identity. | 0 | — |
| `K` | `MatchingSourceSubspace` (local): Source subspace K in the matching proof. | 36 | `formalization_enabled_extension.tex:127`, `formalization_enabled_extension.tex:135`, `formalization_enabled_extension.tex:144`, `formalization_enabled_extension.tex:155` |
| `L` | `MatchingTargetSubspace` (local): Target subspace L in the matching proof. | 2 | `appendices.tex:430`, `appendices.tex:433` |
| `M` | `NormM` (local): Auxiliary unitarily invariant norm used to define a Q-norm through the squared modulus.<br>`Matching` (glossary): Matching of positive principal-angle labels: each label is used in at most one pair.<br>`CounterMovingPlane` (glossary): Moving plane of the competing transporter: the range of W minus the identity. | 10 | `paper.tex:278`, `paper.tex:279`, `paper.tex:1352`, `paper.tex:1353` |
| `M^\perp` | **UNREGISTERED** | 2 | `paper.tex:1353`, `paper.tex:1365` |
| `N` | `NormN` (glossary): Unitarily invariant norm on its domain of finiteness; in the sine theorem, normalized by $N(uv^*)=\\|u\\|\\|v\\|$. | 1 | `paper.tex:278` |
| `O(2)` | `PlanarOrthogonalGroup` (local): Orthogonal matrices of size two. | 0 | — |
| `O(n)` | `OrthogonalGroup` (local): Group of real orthogonal matrices. | 0 | — |
| `P` | `Psource` (glossary): Orthogonal projection onto the source subspace in the transport problem.<br>`P` (local): Orthogonal projection; its source or exact-target role is specified locally. | 0 | — |
| `P_L` | `MatchingTargetProjection` (local): Orthogonal projection onto the matching target L. | 0 | — |
| `P_U` | `ProjSource` (local): Orthogonal projection onto the source subspace in the transport problem. | 0 | — |
| `P_V` | `ProjTarget` (local): Orthogonal projection onto the target subspace in the transport problem. | 0 | — |
| `P_{\Gamma}` | `RieszProjection` (local): Spectral projection associated with a contour Gamma. | 0 | — |
| `P_{\mathrm{ex}}` | `Pexact` (glossary): Orthogonal projection onto the desired exact subspace in the sine-theta theorem. | 0 | — |
| `P_{\mathrm{ex}}^\perp` | `PexactPerp` (local): Orthogonal projection onto the exact complementary subspace. | 0 | — |
| `Q` | `Qtarget` (glossary): Orthogonal projection onto the target subspace in the transport problem.<br>`Q` (local): Orthogonal projection; its role is specified locally.<br>`NormQ` (glossary): Q-norm: its square is a unitarily invariant norm of the squared modulus. | 0 | — |
| `Q_-` | **UNREGISTERED** | 2 | `appendices.tex:351`, `appendices.tex:353` |
| `R` | `R` (glossary): Bounded residual of the trial eigenproblem, agreeing with the operator difference on the trial domain.<br>`PlanarRotationBase` (local): Base letter for planar rotations. | 0 | — |
| `R_t` | `MatchingPlanarRotation` (local): Planar rotation through the indicated angle. | 0 | — |
| `R_{\gamma}` | `MatchingPlanarRotationGamma` (local): Planar rotation through phase gamma. | 0 | — |
| `R_{r+s}` | `MatchingPlanarRotationSum` (local): Planar rotation through phase r+s. | 0 | — |
| `S` | `SpectralSet` (glossary): Borel spectral set used to select a spectral subspace.<br>`S` (glossary): Rectangular complementary error: the trial frame projected onto the unwanted exact subspace.<br>`PairSineBlock` (local): Diagonal principal-sine block.<br>`HalmosSineBlock` (local): Sine block in the Halmos two-projection representation. | 0 | — |
| `S_0` | **UNREGISTERED** | 1 | `appendices.tex:246` |
| `S_0^*` | **UNREGISTERED** | 1 | `appendices.tex:246` |
| `S_1` | **UNREGISTERED** | 1 | `paper.tex:814` |
| `S_2` | **UNREGISTERED** | 2 | `paper.tex:816`, `paper.tex:828` |
| `S_p` | **UNREGISTERED** | 1 | `paper.tex:812` |
| `T` | `IntertwinerT` (glossary): Two-projection intertwiner; its unitary polar factor is the acute direct rotation. | 46 | `paper.tex:278`, `paper.tex:1157`, `paper.tex:1476`, `paper.tex:1477` |
| `T^*` | **UNREGISTERED** | 3 | `paper.tex:278`, `appendices.tex:68`, `appendices.tex:75` |
| `Tq` | `FigureImage` (local): Image of the unit input under the orthogonal map shown in this panel. | 0 | — |
| `U` | `U` (local): Desired exact subspace in the local geometric notation.<br>`Usource` (glossary): Source subspace to be transported onto the target subspace.<br>`PairFreeOrthogonal` (local): Free source or complementary planar orthogonal factor. | 1 | `paper.tex:840` |
| `U^{\perp}` | `Uperp` (local): Orthogonal complement of the desired exact subspace in the local notation. | 0 | — |
| `V` | `V` (local): Trial subspace in the local geometric notation.<br>`Vtarget` (glossary): Target subspace in the transport problem.<br>`YWSV` (local): Orthonormal coordinates for the population eigenspace in the statistical application. | 0 | — |
| `V^{\perp}` | `Vperp` (local): Orthogonal complement of the trial subspace in the local notation. | 0 | — |
| `V_a` | `MatchingBlock` (local): Simultaneous invariant block in the matching proof. | 0 | — |
| `V_g` | `GradientLevelSpace` (local): Positive gradient-level eigenspace. | 0 | — |
| `V_{\mathrm{pol}}` | `PolarU` (glossary): Partial isometry in the polar decomposition; unitary when the operator is invertible. | 0 | — |
| `W` | `Wcompetitor` (glossary): Orthogonal or unitary competitor carrying the source subspace onto the target. | 5 | `appendices.tex:399`, `figures/Fig2.pgf:762`, `figures/Fig2.pgf:930` |
| `X` | `Xframe` (glossary): Orthonormal coordinate matrix for the source subspace in the counterexample.<br>`X` (glossary): Solution of the Sylvester equation; for the sine bound, the trial frame in unwanted exact coordinates.<br>`ProjectionRealPart` (local): Real symmetric part of the phase projection. | 9 | `appendices.tex:411`, `appendices.tex:416`, `appendices.tex:420`, `appendices.tex:421` |
| `Y` | `Yframe` (glossary): Orthonormal coordinate matrix for the target subspace in the counterexample.<br>`SylvesterRHS` (glossary): Right-hand side of the Sylvester equation, obtained by projecting the residual.<br>`ProjectionImaginaryPart` (local): Real skew-symmetric imaginary part of the phase projection. | 6 | `appendices.tex:411`, `appendices.tex:416`, `appendices.tex:420`, `appendices.tex:421` |
| `Z` | `CounterFixedPlane` (glossary): Fixed plane of the competing transporter: the kernel of W minus the identity. | 20 | `paper.tex:808`, `paper.tex:809`, `paper.tex:810`, `paper.tex:812` |
| `Z^*` | **UNREGISTERED** | 4 | `paper.tex:809`, `counterexample.tex:238`, `counterexample.tex:243`, `counterexample.tex:244` |
| `\Delta` | `Delta` (local): Population or statistical spectral gap. | 0 | — |
| `\Delta_W` | `Kdisplacement` (glossary): Full displacement of a transporter from the identity. | 0 | — |
| `\Gamma` | `RieszContour` (local): Contour used in the Riesz spectral-projection formula.<br>`CompressionProjectionImage` (local): Range projection in the finite-rank compression lemma. | 0 | — |
| `\Lambda_0` | `Lambda0` (local): Self-adjoint block on the desired exact spectral subspace. | 0 | — |
| `\Lambda_1` | `Lambda1` (glossary): Self-adjoint operator on exact complementary coordinates: the unwanted spectral block. | 0 | — |
| `\Omega` | `PrincipalPlaneProjectionBase` (local): Projection onto the indicated principal plane.<br>`PinchingProjectionOne` (local): First projection in the pinching inequality. | 0 | — |
| `\Omega_1` | `OmegaOne` (glossary): First principal-plane projection in the failed Ky Fan comparison. | 0 | — |
| `\Omega_2` | `OmegaTwo` (glossary): Second principal-plane projection in the failed Ky Fan comparison. | 0 | — |
| `\Omega_t` | `StrongApproxProjection` (local): Orthogonal projection converging strongly to the identity. | 0 | — |
| `\Phi` | `PowerCost` (local): Sum of the p-th powers of displacement singular values. | 0 | — |
| `\Pi_1` | `CounterPrincipalOne` (glossary): First principal plane in the real counterexample: the span of e0 and e3. | 1 | `counterexample.tex:166` |
| `\Pi_2` | `CounterPrincipalTwo` (glossary): Second principal plane in the real counterexample: the span of e1 and e2. | 1 | `counterexample.tex:166` |
| `\Psi` | `CompressionProjectionInput` (local): Domain projection in the finite-rank compression lemma. | 0 | — |
| `\Sigma` | `ReflectionSigma` (local): Reflection associated with the desired exact spectral projection.<br>`Sigma` (local): Population covariance matrix. | 0 | — |
| `\Theta` | `Theta` (glossary): Full angle operator, the diagonal sum of the source and complementary angle blocks. | 0 | — |
| `\Theta_0` | `Theta0` (glossary): Directed principal-angle operator acting on source or trial coordinates. | 0 | — |
| `\Theta_1` | `Theta1` (glossary): Directed angle operator comparing the orthogonal complements. | 0 | — |
| `\Upsilon` | `PinchingProjectionTwo` (local): Second projection in the pinching inequality. | 0 | — |
| `\alpha` | `alphaAngle` (local): Largest principal angle.<br>`alphaEndpoint` (glossary): Upper endpoint of the central band, or lower-block cut in the ordered gap. | 0 | — |
| `\beta` | `betaEndpoint` (glossary): Lower endpoint of the finite interval in the interval/exterior gap hypothesis. | 0 | — |
| `\delta` | `delta` (glossary): Positive spectral separation in the stated gap configuration.<br>`KroneckerDelta` (local): Kronecker delta: equals 1 for equal indices and 0 otherwise. | 0 | — |
| `\dim` | `DimensionOperator` (local): Dimension of a vector space. | 0 | — |
| `\ell^2` | **UNREGISTERED** | 1 | `paper.tex:1127` |
| `\epsilon` | `PhaseSignChoice` (local): Sign variable taking values minus one and plus one. | 0 | — |
| `\eta` | `ProjectionCoupling` (local): Normalization used to construct an invariant real plane.<br>`CompressionTolerance` (local): Tolerance controlling the off-diagonal compression norm. | 0 | — |
| `\gamma` | `PairAttainingAngle` (local): Rotation angle realizing a chosen scalar pair parameter.<br>`SylvesterGapThreshold` (local): Spectral separation threshold in a Sylvester estimate.<br>`MatchingPhaseGamma` (local): Rotation phase gamma in the matching calculation. | 0 | — |
| `\infty` | **UNREGISTERED** | 11 | `paper.tex:256`, `paper.tex:810`, `paper.tex:1105`, `paper.tex:1117` |
| `\lambda` | `ProjectionEigenvalue` (local): Eigenvalue of the real part of the phase projection.<br>`SpectralValue` (local): Real spectral parameter or individual eigenvalue of a self-adjoint operator. | 0 | — |
| `\lambda_0` | `lambda0` (local): Wanted exact eigenvalue or wanted spectral value. | 0 | — |
| `\lambda_1` | `lambda1` (local): Unwanted exact eigenvalue or complementary spectral value. | 0 | — |
| `\lambda_u` | `lambdau` (local): Eigenvalue associated with a desired exact vector. | 0 | — |
| `\lambda_w` | `lambdaw` (local): Eigenvalue associated with an unwanted exact vector. | 0 | — |
| `\mathbbC` | `ComplexField` (local): The complex numbers. | 0 | — |
| `\mathbbN_{\geq1}` | **UNREGISTERED** | 1 | `paper.tex:1127` |
| `\mathbbR` | `RealField` (local): The real numbers. | 0 | — |
| `\mathbf{0}` | `ZeroVector` (glossary): Zero vector; the additive identity of the ambient vector space. | 0 | — |
| `\mathbf{1}` | `OnesVector` (local): All-ones vector in a chosen finite-dimensional coordinate space. | 0 | — |
| `\mathcalD` | `SquaredDisplacement` (local): Squared full displacement as a function of the transporter. | 0 | — |
| `\mathcalF` | `TrialCoordinateSpace` (glossary): Hilbert space of trial coordinates. | 0 | — |
| `\mathcalF_{\mathrm{ex}}` | `ExactCoordinateSpace` (glossary): Hilbert space of coordinates for the desired exact spectral subspace. | 0 | — |
| `\mathcalG` | `ComplementaryCoordinateSpace` (glossary): Hilbert space of exact complementary coordinates. | 0 | — |
| `\mathcalG_\delta` | `SineGap` (local): Interval/exterior separation or either ordered separation, as in the sine-theta theorem. | 0 | — |
| `\mathcalH` | `AmbientHilbertSpace` (glossary): Ambient Hilbert space containing the trial and exact subspaces.<br>`GeneralHilbertSpace` (local): Generic Hilbert space in a local discussion. | 0 | — |
| `\mathcalI` | `IntervalSeparation` (local): Interval/exterior separation predicate. | 0 | — |
| `\mathcalI_g` | `GradientComplexStructure` (local): Complex multiplication constructed from a positive gradient level. | 0 | — |
| `\mathcalO` | `OrderedSeparation` (local): Ordered spectral separation predicate. | 0 | — |
| `\mathcalW` | `FeasibleTransport` (local): Orthogonal maps carrying the source subspace onto the target. | 0 | — |
| `\mathrm{HS}` | **UNREGISTERED** | 2 | `appendices.tex:456`, `appendices.tex:457` |
| `\mathrm{gen}` | **UNREGISTERED** | 2 | `paper.tex:559`, `paper.tex:561` |
| `\mathrm{ker}` | **UNREGISTERED** | 1 | `figures/Fig2.pgf:1748` |
| `\mathrm{plane}` | **UNREGISTERED** | 2 | `formalization_enabled_extension.tex:204`, `formalization_enabled_extension.tex:207` |
| `\mathrm{range}` | **UNREGISTERED** | 5 | `figures/Fig1.pgf:206`, `figures/Fig1.pgf:212`, `figures/Fig1.pgf:409`, `figures/Fig1.pgf:415` |
| `\mathrm{span}` | **UNREGISTERED** | 3 | `figures/Fig2.pgf:1700`, `figures/Fig2.pgf:1730`, `figures/Fig2.pgf:1736` |
| `\mathtt{A_0}` | **UNREGISTERED** | 2 | `appendices.tex:115`, `appendices.tex:117` |
| `\mathtt{H}` | **UNREGISTERED** | 1 | `appendices.tex:120` |
| `\mu` | `mu` (local): Trial spectral value. | 0 | — |
| `\nu` | `KyFanEvenIndex` (local): Even integer in the principal-plane Ky Fan comparison. | 0 | — |
| `\operatorname{Re}` | **UNREGISTERED** | 1 | `formalization_enabled_extension.tex:355` |
| `\operatorname{diag}` | `DiagonalOperator` (local): Diagonal or block-diagonal operator. | 0 | — |
| `\operatorname{dist}` | `SpectralDistanceOperator` (local): Distance between two spectral sets. | 0 | — |
| `\operatorname{dom}` | `DomainOperator` (local): Domain of an operator. | 0 | — |
| `\operatorname{ker}` | `KernelOperator` (local): Kernel (null space) of an operator. | 0 | — |
| `\operatorname{rank}` | `RankOperator` (local): Rank of a linear map or matrix. | 0 | — |
| `\operatorname{ran}` | `RangeOperator` (local): Range (image) of an operator. | 0 | — |
| `\operatorname{span}` | `SpanOperator` (local): Linear span of vectors. | 0 | — |
| `\operatorname{tr}` | `TraceOperator` (local): Trace of an operator. | 0 | — |
| `\pi` | `PiConstant` (local): The constant pi (angles are in radians). | 0 | — |
| `\rho` | `rho` (local): Trial eigenvalue or scalar trial operator. | 0 | — |
| `\sigma` | `SpectrumSymbol` (local): Spectrum of an operator.<br>`SingularValueBase` (local): Base letter for singular values. | 0 | — |
| `\sigma_j` | `TransportSingularValues` (local): A displacement singular value in the matching proof.<br>`DisplacementSingular` (local): An individual singular value of the full displacement from the identity.<br>`SingularValue` (glossary): The j-th singular value under the sigma_j convention. | 0 | — |
| `\sin\Theta_0` | `sinTheta0` (glossary): Positive sine operator on trial coordinates; the modulus of the rectangular complementary error. | 0 | — |
| `\sin\theta` | `sintheta` (local): Sine of an individual principal angle: the length of the complementary component of a unit principal trial vector. | 0 | — |
| `\tau` | `PairPhaseParameter` (local): Scalar parameter in the two-angle power-cost minimum. | 0 | — |
| `\theta` | `theta` (glossary): Principal angle between the subspaces under comparison. | 0 | — |
| `\varepsilon` | `EpsilonAngle` (local): Angle parameter controlling the maximum subspace deviation.<br>`EigenvalueExampleEpsilon` (local): Small positive parameter in the eigenvalue-example matrices.<br>`FrameLowerBoundEpsilon` (local): Lower-bound parameter for the trial-coordinate embedding. | 4 | `paper.tex:492`, `paper.tex:494`, `paper.tex:498` |
| `\varphi` | `PhiAngle` (local): Auxiliary angle or angle operator in the two-subspace comparison.<br>`GradientEigenphase` (local): One of the at most two phases at a positive gradient level.<br>`PlaneRotationAngle` (local): Signed rotation angle of the orthogonal map on the displayed invariant plane. | 0 | — |
| `\vartheta` | `MatchingPlanarAngle` (local): Planar rotation angle in the matching-proof calculation. | 0 | — |
| `\widehatA` | `Ahat` (local): Operator under study; in the perturbation setting, the reference operator plus its perturbation.<br>`Acurrent` (glossary): Operator under study; in the perturbation setting, the reference operator plus its perturbation. | 0 | — |
| `\widehatV` | `YWSVhat` (local): Estimated eigenspace frame in the statistical application. | 0 | — |
| `\widehat\Sigma` | `SigmaHat` (local): Estimated or perturbed covariance matrix. | 0 | — |
| `\\|\cdot\\|_1` | `TraceNormNotation` (glossary): Trace (nuclear) norm. | 0 | — |
| `\\|\cdot\\|_F` | `FrobeniusNormNotation` (glossary): Frobenius norm. | 0 | — |
| `\\|\cdot\\|_{(j)}` | `KyFanNormNotation` (glossary): Ky Fan j-norm. | 0 | — |
| `\\|\cdot\\|_{S_p}` | `SchattenNormNotation` (local): Schatten p-norm. | 0 | — |
| `\\|\cdot\\|_{\mathrm{HS}}` | `HilbertSchmidtNormNotation` (local): Hilbert--Schmidt norm. | 0 | — |
| `\\|\cdot\\|_{\mathrm{op}}` | `OperatorNormNotation` (glossary): Operator norm. | 0 | — |
| `a` | `SingletonPowerCost` (local): Minimum displacement power cost for one angle.<br>`PairPhaseCosineX` (local): Cosine of the first phase parameter in the trace calculation.<br>`CounterChordA` (glossary): Direct-rotation displacement singular value in the counterexample: sqrt(2 - sqrt(2)).<br>`SylvesterScalarRight` (local): Scalar right coefficient a in a Sylvester equation. | 12 | `paper.tex:256`, `paper.tex:1114`, `paper.tex:1115`, `formalization_enabled_extension.tex:143` |
| `a_0` | `a0` (local): Wanted trial eigenvalue or trial spectral value. | 0 | — |
| `a_1` | `a1` (local): Reference eigenvalue or complementary spectral value. | 0 | — |
| `b` | `b` (local): Scalar perturbation or coupling coefficient.<br>`PairPowerCost` (local): Positive-determinant displacement power cost for a pair of angles.<br>`PairPhaseCosineY` (local): Cosine of the second phase parameter in the trace calculation.<br>`CounterChordB` (glossary): Competing-transporter displacement singular value in the counterexample: square root of 2.<br>`SylvesterScalarLeft` (local): Scalar left coefficient b in a Sylvester equation. | 20 | `paper.tex:1107`, `paper.tex:1109`, `paper.tex:1111`, `paper.tex:1117` |
| `c` | `CosAngle` (local): Cosine of a principal angle or the corresponding positive cosine block.<br>`SingletonCost` (glossary): Minimum trace displacement for one real principal plane: choose a rotation or a reflection.<br>`PairCost` (glossary): Trace displacement cost of coupling two principal planes in a four-dimensional block. | 7 | `paper.tex:536`, `paper.tex:537`, `formalization_enabled_extension.tex:459` |
| `d` | `PairHalfDifference` (local): Half the difference of the two ordered principal angles. | 4 | `paper.tex:669`, `paper.tex:693`, `formalization_enabled_extension.tex:223` |
| `e^{\pmi(\sym{PairPhaseX}+\sym{PairPhaseY})}` | **UNREGISTERED** | 1 | `formalization_enabled_extension.tex:513` |
| `e^{\pmi(\sym{PairPhaseX}-\sym{PairPhaseY})}` | **UNREGISTERED** | 1 | `formalization_enabled_extension.tex:514` |
| `e^{\pmit}` | **UNREGISTERED** | 1 | `formalization_enabled_extension.tex:553` |
| `e^{\sym{AngleGenerator}\sym{Theta}}` | **UNREGISTERED** | 1 | `appendices.tex:248` |
| `e^{i\like{GradientEigenphase}{\symglyph{GradientEigenphase}_1}}` | **UNREGISTERED** | 1 | `formalization_enabled_extension.tex:339` |
| `e^{i\like{GradientEigenphase}{\symglyph{GradientEigenphase}_2}}` | **UNREGISTERED** | 1 | `formalization_enabled_extension.tex:339` |
| `e^{i\sym{theta}}` | **UNREGISTERED** | 1 | `counterexample.tex:287` |
| `e_0` | **UNREGISTERED** | 7 | `counterexample.tex:168`, `counterexample.tex:169`, `counterexample.tex:205`, `counterexample.tex:224` |
| `e_1` | **UNREGISTERED** | 5 | `counterexample.tex:168`, `counterexample.tex:206`, `counterexample.tex:224`, `figures/Fig2.pgf:1700` |
| `e_2` | **UNREGISTERED** | 5 | `counterexample.tex:169`, `counterexample.tex:206`, `counterexample.tex:224`, `figures/Fig2.pgf:1736` |
| `e_3` | **UNREGISTERED** | 3 | `counterexample.tex:205`, `counterexample.tex:224`, `figures/Fig2.pgf:1730` |
| `e_n` | **UNREGISTERED** | 4 | `paper.tex:1128` |
| `f_0` | `f0` (local): Component or coordinate vector in the desired exact subspace. | 0 | — |
| `f_1` | `f1` (local): Component or coordinate vector in the unwanted exact subspace. | 0 | — |
| `f_p` | `MatchingPhaseCost` (local): Displacement power cost for one scalar phase. | 0 | — |
| `g` | `GradientLevel` (local): Positive gradient level; the gradient squared is minus this level squared times the identity.<br>`g` (local): Original spectral gap of the reference operator; distinct from the certified sine-theta separation. | 2 | `paper.tex:1184` |
| `h` | `PairMeanAngle` (local): Mean of the two ordered principal angles. | 2 | `paper.tex:1184` |
| `i` | **UNREGISTERED** | 71 | `paper.tex:422`, `paper.tex:693`, `counterexample.tex:282`, `counterexample.tex:286` |
| `j` | **UNREGISTERED** | 75 | `paper.tex:416`, `paper.tex:417`, `paper.tex:421`, `paper.tex:422` |
| `k` | **UNREGISTERED** | 4 | `counterexample.tex:199`, `counterexample.tex:202`, `counterexample.tex:203` |
| `m` | **UNREGISTERED** | 2 | `formalization_enabled_extension.tex:13`, `formalization_enabled_extension.tex:15` |
| `n` | **UNREGISTERED** | 20 | `paper.tex:400`, `paper.tex:480`, `paper.tex:1128`, `formalization_enabled_extension.tex:12` |
| `p` | **UNREGISTERED** | 50 | `paper.tex:810`, `paper.tex:812`, `paper.tex:822`, `paper.tex:823` |
| `q` | `FigureInput` (local): Unit input to the orthogonal map shown in this invariant-plane panel. | 3 | `counterexample.tex:171` |
| `r` | `r` (local): Residual vector of an approximate eigenpair.<br>`PairRotationR` (local): Half the sum of the two free planar rotation angles. | 0 | — |
| `s` | `SinAngle` (local): Sine of a principal angle or the corresponding positive sine block.<br>`DisplacementSize` (local): Scalar displacement singular-value magnitude in the uniform limit.<br>`PairRotationS` (local): Half the difference of the two free planar rotation angles. | 0 | — |
| `t` | **UNREGISTERED** | 36 | `formalization_enabled_extension.tex:162`, `formalization_enabled_extension.tex:172`, `formalization_enabled_extension.tex:174`, `formalization_enabled_extension.tex:175` |
| `u` | `u` (local): Vector in the desired exact subspace. | 27 | `paper.tex:1147`, `paper.tex:1150`, `paper.tex:1152`, `formalization_enabled_extension.tex:357` |
| `u_1` | **UNREGISTERED** | 3 | `counterexample.tex:168`, `figures/Fig2.pgf:210`, `figures/Fig2.pgf:216` |
| `u_2` | **UNREGISTERED** | 3 | `counterexample.tex:168`, `figures/Fig2.pgf:483`, `figures/Fig2.pgf:489` |
| `v` | `v` (local): Trial vector or vector in the trial subspace. | 12 | `paper.tex:1147`, `paper.tex:1150`, `paper.tex:1152`, `formalization_enabled_extension.tex:363` |
| `v^*` | **UNREGISTERED** | 2 | `paper.tex:1147`, `paper.tex:1150` |
| `v_j` | **UNREGISTERED** | 6 | `appendices.tex:384`, `appendices.tex:385`, `appendices.tex:393`, `appendices.tex:395` |
| `w` | `w` (local): Vector in an unwanted or complementary spectral subspace. | 0 | — |
| `w_{ij}` | `MatchingEdgeWeight` (glossary): Edge weight: the cost of two singletons minus their paired cost. | 0 | — |
| `x` | `SourceVector` (local): Vector in the source subspace.<br>`PairPhaseX` (local): First phase parameter of a four-dimensional transporter.<br>`RayleighTestVector` (local): Test vector in the Rayleigh quotient.<br>`SylvesterScalarUnknown` (local): Scalar unknown x in a Sylvester equation. | 42 | `paper.tex:683`, `paper.tex:684`, `paper.tex:1115`, `paper.tex:1116` |
| `y` | `TargetVector` (local): Vector in the target subspace.<br>`PairPhaseY` (local): Second phase parameter of a four-dimensional transporter.<br>`SylvesterScalarRHS` (local): Scalar right side y in a Sylvester equation. | 0 | — |
| `z` | **UNREGISTERED** | 13 | `paper.tex:687`, `paper.tex:688`, `paper.tex:689`, `paper.tex:693` |
| `z^2` | **UNREGISTERED** | 3 | `formalization_enabled_extension.tex:500`, `formalization_enabled_extension.tex:507`, `formalization_enabled_extension.tex:510` |
| `z^3` | **UNREGISTERED** | 1 | `formalization_enabled_extension.tex:506` |
| `z^4` | **UNREGISTERED** | 1 | `formalization_enabled_extension.tex:506` |
| `\|\cdot\|` | `OperatorModulusNotation` (glossary): Positive modulus of an operator. | 0 | — |

## Registered semantics, including glossary status

The `glossary` column is directly declared in `math_symbol_colors.tex`. Occurrences here count only direct `\sym`/`\like`/`\symglyph` use in math; the older audit separately counts prose and Python figure sources.

| Key | Glyph | Mathematical type | Glossary | Color | In-math uses | Description |
|---|---|---|---|---|---:|---|
| `A` | `A` | self-adjoint-operator | glossary | old | 45 | Reference self-adjoint operator before perturbation. |
| `A1` | `A_1` | self-adjoint-operator | local | old | 2 | Complementary block of the reference operator. |
| `a1` | `a_1` | scalar | local | old | 0 | Reference eigenvalue or complementary spectral value. |
| `ReferenceBlock0` | `A_0` | self-adjoint-operator | glossary | old | 11 | Reference operator restricted to the source subspace in Section 8. |
| `ReferenceBlock1` | `A_1` | self-adjoint-operator | glossary | old | 8 | Reference operator restricted to the source complement in Section 8. |
| `Ahat` | `\widehat A` | self-adjoint-operator | local | current | 0 | Operator under study; in the perturbation setting, the reference operator plus its perturbation. |
| `Acurrent` | `\widehat A` | self-adjoint-operator | glossary | current | 52 | Operator under study; in the perturbation setting, the reference operator plus its perturbation. |
| `H` | `H` | self-adjoint-operator | glossary | perturb | 27 | Additive self-adjoint perturbation of the reference operator. |
| `H0` | `H_0` | self-adjoint-operator | local | perturb | 4 | Wanted diagonal block of the perturbation. |
| `H1` | `H_1` | self-adjoint-operator | local | perturb | 3 | Unwanted diagonal block of the perturbation. |
| `B` | `B` | linear-operator | local | perturb | 0 | Off-diagonal perturbation or coupling block. |
| `b` | `b` | scalar | local | perturb | 0 | Scalar perturbation or coupling coefficient. |
| `U` | `U` | linear-subspace | local | wanted | 0 | Desired exact subspace in the local geometric notation. |
| `V` | `V` | linear-subspace | local | trial | 0 | Trial subspace in the local geometric notation. |
| `Usource` | `U` | linear-subspace | glossary | trial | 24 | Source subspace to be transported onto the target subspace. |
| `E0` | `E_0` | isometric-embedding | glossary | trialframe | 66 | Isometric embedding of the trial subspace; its adjoint returns trial coordinates. |
| `TrialOperator` | `A_{\mathrm{trial}}` | self-adjoint-operator | glossary | trialspectrum | 49 | Self-adjoint operator on trial coordinates; its eigenvalues are the trial spectral values. |
| `v` | `v` | vector | local | trialvector | 33 | Trial vector or vector in the trial subspace. |
| `rho` | `\rho` | scalar | local | trialspectrum | 9 | Trial eigenvalue or scalar trial operator. |
| `mu` | `\mu` | scalar | local | trialspectrum | 6 | Trial spectral value. |
| `a0` | `a_0` | scalar | local | trialspectrum | 0 | Wanted trial eigenvalue or trial spectral value. |
| `Wcompetitor` | `W` | unitary-operator | glossary | trialcompetitor | 113 | Orthogonal or unitary competitor carrying the source subspace onto the target. |
| `Psource` | `P` | orthogonal-projection | glossary | trialprojection | 124 | Orthogonal projection onto the source subspace in the transport problem. |
| `ProjSource` | `P_U` | orthogonal-projection | local | trialprojection | 0 | Orthogonal projection onto the source subspace in the transport problem. |
| `SourceVector` | `x` | vector | local | trialvector | 6 | Vector in the source subspace. |
| `Xframe` | `X` | isometric-embedding | glossary | trialframe | 6 | Orthonormal coordinate matrix for the source subspace in the counterexample. |
| `TrialCoordinateSpace` | `\mathcal F` | hilbert-space | glossary | trialframe | 6 | Hilbert space of trial coordinates. |
| `AmbientHilbertSpace` | `\mathcal H` | hilbert-space | glossary | ambient | 11 | Ambient Hilbert space containing the trial and exact subspaces. |
| `ZeroVector` | `\mathbf{0}` | vector | glossary | fg | 6 | Zero vector; the additive identity of the ambient vector space. |
| `OnesVector` | `\mathbf{1}` | vector | local | fg | 0 | All-ones vector in a chosen finite-dimensional coordinate space. |
| `Vtarget` | `V` | linear-subspace | glossary | wanted | 24 | Target subspace in the transport problem. |
| `F0` | `F_0` | isometric-embedding | glossary | wantedframe | 21 | Isometric coordinates for the desired exact spectral subspace; star denotes the adjoint. |
| `Lambda0` | `\Lambda_0` | self-adjoint-operator | local | wantedspectrum | 7 | Self-adjoint block on the desired exact spectral subspace. |
| `u` | `u` | vector | local | wantedvector | 0 | Vector in the desired exact subspace. |
| `f0` | `f_0` | vector | local | wantedvector | 0 | Component or coordinate vector in the desired exact subspace. |
| `lambda0` | `\lambda_0` | scalar | local | wantedspectrum | 0 | Wanted exact eigenvalue or wanted spectral value. |
| `lambdau` | `\lambda_u` | scalar | local | wantedspectrum | 0 | Eigenvalue associated with a desired exact vector. |
| `Pexact` | `P_{\mathrm{ex}}` | orthogonal-projection | glossary | wantedprojection | 20 | Orthogonal projection onto the desired exact subspace in the sine-theta theorem. |
| `PexactPerp` | `P_{\mathrm{ex}}^\perp` | orthogonal-projection | local | unwantedprojection | 4 | Orthogonal projection onto the exact complementary subspace. |
| `ReflectionSigma` | `\Sigma` | unitary-operator | local | wantedprojection | 0 | Reflection associated with the desired exact spectral projection. |
| `Qtarget` | `Q` | orthogonal-projection | glossary | wantedprojection | 54 | Orthogonal projection onto the target subspace in the transport problem. |
| `ProjTarget` | `P_V` | orthogonal-projection | local | wantedprojection | 0 | Orthogonal projection onto the target subspace in the transport problem. |
| `Rrotation` | `D` | unitary-operator | glossary | wantedrotation | 54 | Canonical direct rotation carrying the source subspace onto the target. |
| `SourceDirectRotation` | `D` | unitary-operator | local | wantedrotation | 15 | Direct rotation, including the nonacute case in the source-result table. |
| `Yframe` | `Y` | isometric-embedding | glossary | wantedframe | 7 | Orthonormal coordinate matrix for the target subspace in the counterexample. |
| `TargetVector` | `y` | vector | local | wantedvector | 4 | Vector in the target subspace. |
| `ExactCoordinateSpace` | `\mathcal F_{\mathrm{ex}}` | hilbert-space | glossary | wantedframe | 3 | Hilbert space of coordinates for the desired exact spectral subspace. |
| `Uperp` | `U^{\perp}` | linear-subspace | local | unwanted | 0 | Orthogonal complement of the desired exact subspace in the local notation. |
| `F1` | `F_1` | isometric-embedding | glossary | unwantedframe | 45 | Isometric coordinates for the exact complementary subspace; star denotes the adjoint. |
| `Lambda1` | `\Lambda_1` | self-adjoint-operator | glossary | unwantedspectrum | 33 | Self-adjoint operator on exact complementary coordinates: the unwanted spectral block. |
| `SpectralMeasure` | `E` | projection-valued-measure | glossary | wantedprojection | 5 | Projection-valued spectral measure of a self-adjoint operator. |
| `SpectralSet` | `S` | set | glossary | wantedspectrum | 4 | Borel spectral set used to select a spectral subspace. |
| `SylvesterLeft` | `B` | self-adjoint-operator | glossary | unwantedspectrum | 12 | Left coefficient of the Sylvester equation; corresponds to the unwanted spectral block. |
| `SylvesterRight` | `C` | self-adjoint-operator | glossary | trialspectrum | 9 | Right coefficient of the Sylvester equation; corresponds to the trial operator. |
| `SylvesterRHS` | `Y` | linear-operator | glossary | resid | 3 | Right-hand side of the Sylvester equation, obtained by projecting the residual. |
| `w` | `w` | vector | local | unwantedvector | 0 | Vector in an unwanted or complementary spectral subspace. |
| `f1` | `f_1` | vector | local | unwantedvector | 0 | Component or coordinate vector in the unwanted exact subspace. |
| `lambda1` | `\lambda_1` | scalar | local | unwantedspectrum | 0 | Unwanted exact eigenvalue or complementary spectral value. |
| `lambdaw` | `\lambda_w` | scalar | local | unwantedspectrum | 0 | Eigenvalue associated with an unwanted exact vector. |
| `ComplementaryCoordinateSpace` | `\mathcal G` | hilbert-space | glossary | unwantedframe | 4 | Hilbert space of exact complementary coordinates. |
| `E1` | `E_1` | isometric-embedding | local | unwantedframe | 0 | Isometric coordinates for the complementary trial subspace. |
| `Vperp` | `V^{\perp}` | linear-subspace | local | unwanted | 0 | Orthogonal complement of the trial subspace in the local notation. |
| `theta` | `\theta` | angle | glossary | sine | 186 | Principal angle between the subspaces under comparison. |
| `Theta` | `\Theta` | angle-operator | glossary | angleoperator | 25 | Full angle operator, the diagonal sum of the source and complementary angle blocks. |
| `Theta0` | `\Theta_0` | angle-operator | glossary | angleoperator | 18 | Directed principal-angle operator acting on source or trial coordinates. |
| `Theta1` | `\Theta_1` | angle-operator | glossary | angleoperator | 7 | Directed angle operator comparing the orthogonal complements. |
| `CrossedSourceDefect` | `D_0` | linear-subspace | glossary | fg | 13 | Source directions perpendicular to the target subspace. |
| `CrossedTargetDefect` | `D_1` | linear-subspace | glossary | fg | 13 | Target directions perpendicular to the source subspace. |
| `ComplementCosineBlock` | `C_1` | self-adjoint-operator | local | anglecos | 5 | Cosine of the complementary angle block in the spectral-repulsion inequality. |
| `sintheta` | `\sin\theta` | scalar | local | sine | 1 | Sine of an individual principal angle: the length of the complementary component of a unit principal trial vector. |
| `sinTheta0` | `\sin\Theta_0` | angle-operator | glossary | sineoperator | 14 | Positive sine operator on trial coordinates; the modulus of the rectangular complementary error. |
| `S` | `S` | linear-operator | glossary | sineblock | 27 | Rectangular complementary error: the trial frame projected onto the unwanted exact subspace. |
| `X` | `X` | linear-operator | glossary | sylvester | 39 | Solution of the Sylvester equation; for the sine bound, the trial frame in unwanted exact coordinates. |
| `alphaAngle` | `\alpha` | angle | local | anglemax | 0 | Largest principal angle. |
| `CosAngle` | `c` | scalar-or-operator | local | anglecos | 35 | Cosine of a principal angle or the corresponding positive cosine block. |
| `SinAngle` | `s` | scalar-or-operator | local | sineoperator | 31 | Sine of a principal angle or the corresponding positive sine block. |
| `EpsilonAngle` | `\varepsilon` | angle | local | anglemax | 3 | Angle parameter controlling the maximum subspace deviation. |
| `PhiAngle` | `\varphi` | angle | local | angleoperator | 0 | Auxiliary angle or angle operator in the two-subspace comparison. |
| `Bblock` | `B` | linear-operator | local | sineblock | 0 | Off-diagonal block in the two-subspace decomposition. |
| `Cblock` | `C` | linear-operator | local | sylvester | 0 | Complementary or Sylvester block in the two-subspace decomposition. |
| `Ablock` | `A` | linear-operator | local | anglecos | 0 | Positive cosine-related block in the two-subspace decomposition. |
| `r` | `r` | vector | local | residvector | 8 | Residual vector of an approximate eigenpair. |
| `R` | `R` | linear-operator | glossary | resid | 42 | Bounded residual of the trial eigenproblem, agreeing with the operator difference on the trial domain. |
| `Kdisplacement` | `\Delta_W` | operator-valued-function | glossary | displacement | 12 | Full displacement of a transporter from the identity. |
| `SquaredDisplacement` | `\mathcal D` | operator-valued-function | local | displacement | 3 | Squared full displacement as a function of the transporter. |
| `SpectralGradient` | `G` | linear-operator | local | displacement | 19 | Skew-symmetric spectral gradient of the displacement power sum in the matching proof. |
| `GradientLevel` | `g` | scalar | local | displacement | 4 | Positive gradient level; the gradient squared is minus this level squared times the identity. |
| `GradientComplexStructure` | `\mathcal I_g` | linear-operator | local | displacement | 8 | Complex multiplication constructed from a positive gradient level. |
| `SkewDirection` | `B` | linear-operator | local | ambient | 17 | Skew-symmetric direction for a first variation of an orthogonal transporter. |
| `delta` | `\delta` | scalar | glossary | gap | 78 | Positive spectral separation in the stated gap configuration. |
| `g` | `g` | scalar | local | gaporiginal | 0 | Original spectral gap of the reference operator; distinct from the certified sine-theta separation. |
| `Delta` | `\Delta` | scalar | local | gapstat | 0 | Population or statistical spectral gap. |
| `alphaEndpoint` | `\alpha` | scalar | glossary | gapinterval | 32 | Upper endpoint of the central band, or lower-block cut in the ordered gap. |
| `betaEndpoint` | `\beta` | scalar | glossary | gapinterval | 14 | Lower endpoint of the finite interval in the interval/exterior gap hypothesis. |
| `P` | `P` | orthogonal-projection | local | fg | 0 | Orthogonal projection; its source or exact-target role is specified locally. |
| `Q` | `Q` | orthogonal-projection | local | fg | 0 | Orthogonal projection; its role is specified locally. |
| `IntertwinerT` | `T` | linear-operator | glossary | intertwiner | 30 | Two-projection intertwiner; its unitary polar factor is the acute direct rotation. |
| `Jturn` | `J_0` | matrix | glossary | turn | 29 | Planar rotation through $\pi/2$, with square minus the identity. |
| `PolarU` | `V_{\mathrm{pol}}` | partial-isometry | glossary | intertwiner | 3 | Partial isometry in the polar decomposition; unitary when the operator is invertible. |
| `Cturn` | `C` | matrix | glossary | turn | 7 | Planar rotation through twice the principal angle in the counterexample. |
| `Hmix` | `H_{\mathrm{mix}}` | matrix | glossary | mix | 5 | Orthogonal mixing matrix in the counterexample. |
| `Jreflect` | `J_{\mathrm{src}}` | linear-operator | glossary | trialprojection | 16 | Reflection equal to twice the source projection minus the identity. |
| `AngleGenerator` | `J_{\mathrm{ang}}` | linear-operator | glossary | turn | 6 | Skew angle generator in the direct-rotation result summaries. |
| `Dblock` | `D` | matrix | local | mix | 0 | Auxiliary diagonal or block matrix in the counterexample. |
| `OmegaOne` | `\Omega_1` | orthogonal-projection | glossary | turn | 5 | First principal-plane projection in the failed Ky Fan comparison. |
| `OmegaTwo` | `\Omega_2` | orthogonal-projection | glossary | intertwiner | 5 | Second principal-plane projection in the failed Ky Fan comparison. |
| `Dplanar` | `D` | unitary-operator | local | wantedrotation | 0 | Planar direct-rotation block. |
| `Hreflection` | `H` | linear-operator | local | trialcompetitor | 0 | Planar reflection carrying the source line to the target. |
| `NormN` | `N` | norm | glossary | norm | 85 | Unitarily invariant norm on its domain of finiteness; in the sine theorem, normalized by $N(uv^*)=\\|u\\|\\|v\\|$. |
| `SineGap` | `\mathcal G_\delta` | predicate | local | gap | 7 | Interval/exterior separation or either ordered separation, as in the sine-theta theorem. |
| `NormM` | `M` | norm | local | normaux | 7 | Auxiliary unitarily invariant norm used to define a Q-norm through the squared modulus. |
| `NormQ` | `Q` | norm | glossary | normaux | 7 | Q-norm: its square is a unitarily invariant norm of the squared modulus. |
| `SingletonCost` | `c` | scalar-cost | glossary | norm | 32 | Minimum trace displacement for one real principal plane: choose a rotation or a reflection. |
| `PairCost` | `c` | scalar-cost | glossary | norm | 16 | Trace displacement cost of coupling two principal planes in a four-dimensional block. |
| `MatchingPhaseCost` | `f_p` | scalar-cost | local | norm | 24 | Displacement power cost for one scalar phase. |
| `SingletonPowerCost` | `a` | scalar-cost | local | norm | 10 | Minimum displacement power cost for one angle. |
| `PairPowerCost` | `b` | scalar-cost | local | norm | 6 | Positive-determinant displacement power cost for a pair of angles. |
| `Matching` | `M` | matching | glossary | normaux | 20 | Matching of positive principal-angle labels: each label is used in at most one pair. |
| `PowerCost` | `\Phi` | scalar-cost | local | norm | 16 | Sum of the p-th powers of displacement singular values. |
| `GradientOffDiagonal` | `G_{01}` | linear-operator | local | fg | 3 | Complement-to-source block of the skew-symmetric gradient. |
| `OrthogonalGroup` | `O(n)` | group | local | fg | 4 | Group of real orthogonal matrices. |
| `FeasibleTransport` | `\mathcal W` | set | local | fg | 11 | Orthogonal maps carrying the source subspace onto the target. |
| `TransportSingularValues` | `\sigma_j` | scalar | local | fg | 2 | A displacement singular value in the matching proof. |
| `DisplacementSize` | `s` | scalar | local | fg | 5 | Scalar displacement singular-value magnitude in the uniform limit. |
| `SingletonBaseline` | `C_0` | scalar-cost | local | fg | 2 | Trace displacement when every angle uses its singleton transporter. |
| `MatchingPowerCost` | `C_p` | scalar-cost | local | fg | 4 | Total paired and singleton power cost of a matching. |
| `MatchingBlock` | `V_a` | linear-subspace | local | fg | 4 | Simultaneous invariant block in the matching proof. |
| `GradientLevelSpace` | `V_g` | linear-subspace | local | fg | 3 | Positive gradient-level eigenspace. |
| `GradientEigenphase` | `\varphi` | angle | local | fg | 8 | One of the at most two phases at a positive gradient level. |
| `GradientPhaseProjection` | `E` | orthogonal-projection | local | fg | 11 | Projection onto the first phase space in a gradient-level space. |
| `ProjectionRealPart` | `X` | linear-operator | local | fg | 17 | Real symmetric part of the phase projection. |
| `ProjectionImaginaryPart` | `Y` | linear-operator | local | fg | 21 | Real skew-symmetric imaginary part of the phase projection. |
| `ProjectionEigenvalue` | `\lambda` | scalar | local | fg | 13 | Eigenvalue of the real part of the phase projection. |
| `ProjectionCoupling` | `\eta` | scalar | local | fg | 5 | Normalization used to construct an invariant real plane. |
| `PairMeanAngle` | `h` | angle | local | fg | 36 | Mean of the two ordered principal angles. |
| `PairHalfDifference` | `d` | angle | local | fg | 22 | Half the difference of the two ordered principal angles. |
| `PairPhaseParameter` | `\tau` | scalar | local | fg | 22 | Scalar parameter in the two-angle power-cost minimum. |
| `PairAttainingAngle` | `\gamma` | angle | local | fg | 1 | Rotation angle realizing a chosen scalar pair parameter. |
| `PairDirectRotation` | `D` | unitary-operator | local | fg | 3 | Direct rotation on the two principal planes. |
| `PairCosineBlock` | `C` | matrix | local | fg | 7 | Diagonal principal-cosine block. |
| `PairSineBlock` | `S` | matrix | local | fg | 5 | Diagonal principal-sine block. |
| `PairFreeOrthogonal` | `U` | unitary-operator | local | fg | 26 | Free source or complementary planar orthogonal factor. |
| `PairPhaseX` | `x` | angle | local | fg | 25 | First phase parameter of a four-dimensional transporter. |
| `PairPhaseY` | `y` | angle | local | fg | 25 | Second phase parameter of a four-dimensional transporter. |
| `PairPhaseCosineX` | `a` | scalar | local | fg | 7 | Cosine of the first phase parameter in the trace calculation. |
| `PairPhaseCosineY` | `b` | scalar | local | fg | 7 | Cosine of the second phase parameter in the trace calculation. |
| `PairRotationR` | `r` | angle | local | fg | 5 | Half the sum of the two free planar rotation angles. |
| `PairRotationS` | `s` | angle | local | fg | 5 | Half the difference of the two free planar rotation angles. |
| `PairPlanarReflection` | `J_2` | unitary-operator | local | fg | 2 | Fixed planar reflection used to parametrize determinant -1 factors. |
| `MatchingPlanarRotation` | `R_t` | unitary-operator | local | fg | 5 | Planar rotation through the indicated angle. |
| `Sigma` | `\Sigma` | matrix | local | old | 0 | Population covariance matrix. |
| `SigmaHat` | `\widehat\Sigma` | matrix | local | current | 0 | Estimated or perturbed covariance matrix. |
| `YWSV` | `V` | isometric-embedding | local | wanted | 0 | Orthonormal coordinates for the population eigenspace in the statistical application. |
| `YWSVhat` | `\widehat V` | isometric-embedding | local | trialframe | 0 | Estimated eigenspace frame in the statistical application. |
| `PlaneRotationAngle` | `\varphi` | angle | local | sine | 4 | Signed rotation angle of the orthogonal map on the displayed invariant plane. |
| `FigureInput` | `q` | vector | local | ambient | 4 | Unit input to the orthogonal map shown in this invariant-plane panel. |
| `FigureImage` | `Tq` | vector | local | wantedvector | 5 | Image of the unit input under the orthogonal map shown in this panel. |
| `DisplacementVector` | `(I-T)q` | vector | local | displacement | 1 | Difference between a unit input and its image under the displayed orthogonal map. |
| `CounterPrincipalOne` | `\Pi_1` | linear-subspace | glossary | fg | 4 | First principal plane in the real counterexample: the span of e0 and e3. |
| `CounterPrincipalTwo` | `\Pi_2` | linear-subspace | glossary | fg | 4 | Second principal plane in the real counterexample: the span of e1 and e2. |
| `CounterMovingPlane` | `M` | linear-subspace | glossary | ambient | 5 | Moving plane of the competing transporter: the range of W minus the identity. |
| `CounterFixedPlane` | `Z` | linear-subspace | glossary | ambient | 4 | Fixed plane of the competing transporter: the kernel of W minus the identity. |
| `CounterChordA` | `a` | scalar | glossary | displacement | 9 | Direct-rotation displacement singular value in the counterexample: sqrt(2 - sqrt(2)). |
| `CounterChordB` | `b` | scalar | glossary | displacement | 6 | Competing-transporter displacement singular value in the counterexample: square root of 2. |
| `DisplacementSingular` | `\sigma_j` | scalar | local | displacement | 10 | An individual singular value of the full displacement from the identity. |
| `MatchingEdgeWeight` | `w_{ij}` | scalar-weight | glossary | current | 7 | Edge weight: the cost of two singletons minus their paired cost. |
| `TraceCost` | `C` | scalar-cost | glossary | norm | 10 | Trace-norm displacement cost of the indicated orthogonal transporter or matching. |
| `SpectralValue` | `\lambda` | scalar | local | wantedspectrum | 6 | Real spectral parameter or individual eigenvalue of a self-adjoint operator. |
| `Identity` | `I` | identity-operator | local | plain | 123 | Identity operator on the space in context. |
| `IdentityTwo` | `I_2` | identity-operator | local | plain | 32 | Two-by-two identity matrix. |
| `IdentityFour` | `I_4` | identity-operator | local | plain | 3 | Four-by-four identity matrix. |
| `ZeroMatrixTwo` | `0_2` | matrix | local | plain | 0 | Two-by-two zero matrix. |
| `PiConstant` | `\pi` | constant | local | plain | 57 | The constant pi (angles are in radians). |
| `RealField` | `\mathbb R` | field | local | plain | 15 | The real numbers. |
| `ComplexField` | `\mathbb C` | field | local | plain | 7 | The complex numbers. |
| `GeneralHilbertSpace` | `\mathcal H` | hilbert-space | local | plain | 1 | Generic Hilbert space in a local discussion. |
| `SpectrumSymbol` | `\sigma` | operator-notation | local | plain | 9 | Spectrum of an operator. |
| `SingularValueBase` | `\sigma` | notation-base | local | plain | 8 | Base letter for singular values. |
| `SingularValue` | `\sigma_j` | scalar | glossary | plain | 13 | The j-th singular value under the sigma_j convention. |
| `OperatorNormNotation` | `\\|\cdot\\|_{\mathrm{op}}` | norm | glossary | plain | 0 | Operator norm. |
| `FrobeniusNormNotation` | `\\|\cdot\\|_F` | norm | glossary | plain | 0 | Frobenius norm. |
| `TraceNormNotation` | `\\|\cdot\\|_1` | norm | glossary | plain | 0 | Trace (nuclear) norm. |
| `HilbertSchmidtNormNotation` | `\\|\cdot\\|_{\mathrm{HS}}` | norm | local | plain | 0 | Hilbert--Schmidt norm. |
| `KyFanNormNotation` | `\\|\cdot\\|_{(j)}` | norm | glossary | plain | 1 | Ky Fan j-norm. |
| `IntervalSeparation` | `\mathcal I` | predicate | local | plain | 2 | Interval/exterior separation predicate. |
| `OrderedSeparation` | `\mathcal O` | predicate | local | plain | 8 | Ordered spectral separation predicate. |
| `EigenvalueExampleEpsilon` | `\varepsilon` | scalar | local | plain | 5 | Small positive parameter in the eigenvalue-example matrices. |
| `FrameLowerBoundEpsilon` | `\varepsilon` | scalar | local | plain | 5 | Lower-bound parameter for the trial-coordinate embedding. |
| `MatchingPlanarAngle` | `\vartheta` | angle | local | plain | 10 | Planar rotation angle in the matching-proof calculation. |
| `RangeOperator` | `\operatorname{ran}` | operator-notation | local | plain | 0 | Range (image) of an operator. |
| `KernelOperator` | `\operatorname{ker}` | operator-notation | local | plain | 0 | Kernel (null space) of an operator. |
| `DomainOperator` | `\operatorname{dom}` | operator-notation | local | plain | 0 | Domain of an operator. |
| `SchattenNormNotation` | `\\|\cdot\\|_{S_p}` | norm | local | plain | 0 | Schatten p-norm. |
| `OperatorModulusNotation` | `\|\cdot\|` | operator-notation | glossary | plain | 0 | Positive modulus of an operator. |
| `SpanOperator` | `\operatorname{span}` | operator-notation | local | plain | 5 | Linear span of vectors. |
| `DiagonalOperator` | `\operatorname{diag}` | linear-operator | local | plain | 8 | Diagonal or block-diagonal operator. |
| `TraceOperator` | `\operatorname{tr}` | operator-notation | local | plain | 14 | Trace of an operator. |
| `DimensionOperator` | `\dim` | operator-notation | local | plain | 12 | Dimension of a vector space. |
| `RankOperator` | `\operatorname{rank}` | operator-notation | local | plain | 1 | Rank of a linear map or matrix. |
| `SpectralDistanceOperator` | `\operatorname{dist}` | operator-notation | local | plain | 1 | Distance between two spectral sets. |
| `RayleighTestVector` | `x` | vector | local | trialvector | 4 | Test vector in the Rayleigh quotient. |
| `HalmosCosineBlock` | `C` | linear-operator | local | anglecos | 9 | Cosine block in the Halmos two-projection representation. |
| `HalmosSineBlock` | `S` | linear-operator | local | sineoperator | 9 | Sine block in the Halmos two-projection representation. |
| `RieszProjection` | `P_{\Gamma}` | orthogonal-projection | local | wantedprojection | 1 | Spectral projection associated with a contour Gamma. |
| `HistoricalSylvesterRight` | `A` | self-adjoint-operator | local | trialspectrum | 4 | Right-hand coefficient A in the historical Sylvester equation. |
| `SylvesterScalarLeft` | `b` | scalar | local | unwantedspectrum | 2 | Scalar left coefficient b in a Sylvester equation. |
| `SylvesterScalarRight` | `a` | scalar | local | trialspectrum | 2 | Scalar right coefficient a in a Sylvester equation. |
| `SylvesterScalarUnknown` | `x` | scalar | local | sylvester | 2 | Scalar unknown x in a Sylvester equation. |
| `SylvesterScalarRHS` | `y` | scalar | local | resid | 2 | Scalar right side y in a Sylvester equation. |
| `MatchingSourceSubspace` | `K` | linear-subspace | local | trial | 8 | Source subspace K in the matching proof. |
| `MatchingTargetSubspace` | `L` | linear-subspace | local | wanted | 5 | Target subspace L in the matching proof. |
| `MatchingTargetProjection` | `P_L` | orthogonal-projection | local | wantedprojection | 5 | Orthogonal projection onto the matching target L. |
| `PlanarOrthogonalGroup` | `O(2)` | group | local | fg | 1 | Orthogonal matrices of size two. |
| `PlanarRotationBase` | `R` | notation-base | local | fg | 0 | Base letter for planar rotations. |
| `MatchingPlanarRotationSum` | `R_{r+s}` | unitary-operator | local | fg | 1 | Planar rotation through phase r+s. |
| `MatchingPlanarRotationGamma` | `R_{\gamma}` | unitary-operator | local | fg | 1 | Planar rotation through phase gamma. |
| `RieszContour` | `\Gamma` | contour | local | plain | 3 | Contour used in the Riesz spectral-projection formula. |
| `KyFanEvenIndex` | `\nu` | scalar | local | plain | 4 | Even integer in the principal-plane Ky Fan comparison. |
| `PrincipalPlaneProjectionBase` | `\Omega` | notation-base | local | plain | 4 | Projection onto the indicated principal plane. |
| `SylvesterGapThreshold` | `\gamma` | scalar | local | plain | 2 | Spectral separation threshold in a Sylvester estimate. |
| `StrongApproxProjection` | `\Omega_t` | orthogonal-projection | local | plain | 2 | Orthogonal projection converging strongly to the identity. |
| `PinchingProjectionOne` | `\Omega` | orthogonal-projection | local | plain | 3 | First projection in the pinching inequality. |
| `PinchingProjectionTwo` | `\Upsilon` | orthogonal-projection | local | plain | 3 | Second projection in the pinching inequality. |
| `CompressionProjectionImage` | `\Gamma` | orthogonal-projection | local | plain | 3 | Range projection in the finite-rank compression lemma. |
| `CompressionProjectionInput` | `\Psi` | orthogonal-projection | local | plain | 5 | Domain projection in the finite-rank compression lemma. |
| `CompressionTolerance` | `\eta` | scalar | local | plain | 4 | Tolerance controlling the off-diagonal compression norm. |
| `MatchingPhaseGamma` | `\gamma` | scalar | local | plain | 0 | Rotation phase gamma in the matching calculation. |
| `KroneckerDelta` | `\delta` | scalar | local | plain | 2 | Kronecker delta: equals 1 for equal indices and 0 otherwise. |
| `PhaseSignChoice` | `\epsilon` | scalar | local | plain | 2 | Sign variable taking values minus one and plus one. |

## Source-attested notation alternatives

These rows are explicitly registered in `math_symbol_colors.tex`; they are not inferred by glyph matching. The table at the end of the paper uses the DK1970 rows from the same records.

| Semantic key | Our glyph | Type | Cited source | Source glyph | Exact location | Qualification |
|---|---|---|---|---|---|---|
| `A` | `A` | self-adjoint-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `A` | \S1, (1.2) | Reference self-adjoint operator. |
| `H` | `H` | self-adjoint-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `H` | \S1, (1.2) | Additive perturbation. |
| `Acurrent` | `\widehat A` | self-adjoint-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `A+H` | \S1 | Perturbed operator. |
| `E0` | `E_0` | isometric-embedding | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `E_0` | \S1, (1.1) | Source isometric frame. |
| `E1` | `E_1` | isometric-embedding | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `E_1` | \S1, (1.1) | Reference complement frame. |
| `F0` | `F_0` | isometric-embedding | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `F_0` | \S1 | Exact-target frame. |
| `F1` | `F_1` | isometric-embedding | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `F_1` | \S1 | Exact-target complement frame. |
| `ReferenceBlock0` | `A_0` | self-adjoint-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `A_0` | \S1, (1.2) | Reference source block. |
| `ReferenceBlock1` | `A_1` | self-adjoint-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `A_1` | \S1, (1.2) | Reference complement block. |
| `TrialOperator` | `A_{\mathrm{trial}}` | self-adjoint-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `A_0` | \S1, residual discussion | Residual comparison operator (the reference block in DK). |
| `Psource` | `P` | orthogonal-projection | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `P` | \S1 | Reference/source projection. |
| `Qtarget` | `Q` | orthogonal-projection | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `Q` | \S1 | Target projection. |
| `Pexact` | `P_{\mathrm{ex}}` | orthogonal-projection | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `Q` | \S1 | Exact-target projection. |
| `B` | `B` | linear-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `B` | \S1, (1.2) | Off-diagonal coupling block. |
| `Theta0` | `\Theta_0` | angle-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `\Theta_0` | \S1 | Source-side angle operator. |
| `Theta1` | `\Theta_1` | angle-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `\Theta_1` | \S1 | Complementary angle operator. |
| `Theta` | `\Theta` | angle-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `\Theta` | \S1 | Full angle operator. |
| `R` | `R` | linear-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `R` | \S1, residual discussion | Trial residual. |
| `Rrotation` | `D` | unitary-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `U` | \S1, (1.18) | Canonical direct rotation. |
| `Wcompetitor` | `W` | unitary-operator | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `V` | \S4 | Competing unitary transporter. |
| `delta` | `\delta` | scalar | [Davis and Kahan (1970), The Rotation of Eigenvectors by a Perturbation. III](https://doi.org/10.1137/0707001) | `\delta` | \S2 | Spectral separation parameter. |
| `AmbientHilbertSpace` | `\mathcal H` | hilbert-space | [Seelmann (2019), Semidefinite Perturbations in the Subspace Perturbation Problem](https://arxiv.org/abs/1708.02463) | `\mathcal H` | p.~1 | Ambient Hilbert space. |
| `SingularValue` | `\sigma_j` | scalar | [Blechta (2020), Stability of Linear GMRES Convergence with Respect to Compact Perturbations](https://arxiv.org/abs/2005.12960) | `\sigma_j` | Thm.~1.1 | Ordered singular values of a compact operator. |

## Lean sine-theta correspondence (one theorem, not global aliases)

Recorded at the semantic declarations in `math_symbol_colors.tex`. The printed correspondence table in the paper uses the same records. Lean binder spellings below are TeX renderings of the source identifiers, including subscript and Greek characters; they are scoped to `sinTheta_unbounded_formGap_whereDefinedUIN_rclike` in `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`.

| Semantic key | Paper glyph | Type | Lean binder (TeX rendering) | Mathematical role |
|---|---|---|---|---|
| `AmbientHilbertSpace` | `\mathcal H` | hilbert-space | `E` | Ambient Hilbert-space carrier. |
| `TrialCoordinateSpace` | `\mathcal F` | hilbert-space | `F` | Trial-coordinate Hilbert-space carrier. |
| `ExactCoordinateSpace` | `\mathcal F_{\mathrm{ex}}` | hilbert-space | `H` | Wanted exact-coordinate Hilbert-space carrier. |
| `ComplementaryCoordinateSpace` | `\mathcal G` | hilbert-space | `G` | Complementary exact-coordinate Hilbert-space carrier. |
| `Acurrent` | `\widehat A` | self-adjoint-operator | `A` | Self-adjoint operator under study. |
| `TrialOperator` | `A_{\mathrm{trial}}` | self-adjoint-operator | `A_0` | General trial operator, not the reference block. |
| `Lambda1` | `\Lambda_1` | self-adjoint-operator | `\Lambda_1` | Exact complementary spectral block. |
| `E0` | `E_0` | isometric-embedding | `E_0` | Isometric trial-coordinate embedding. |
| `F0` | `F_0` | isometric-embedding | `F_0` | Wanted exact-coordinate embedding. |
| `F1` | `F_1` | isometric-embedding | `F_1` | Complementary exact-coordinate embedding. |
| `R` | `R` | linear-operator | `R` | Bounded residual from trial coordinates. |
| `delta` | `\delta` | scalar | `\delta` | Positive spectral-gap parameter. |
| `NormN` | `N` | norm | `N` | Normalized symmetric operator-ideal norm. |

## Types and glyph collisions

Every registered object has a declared mathematical type. Reused printed glyphs with different registered types deserve particular attention; this is a report, not an automatic rename.

| Printed glyph | Keys and types |
|---|---|
| `A` | `A` (self-adjoint-operator); `Ablock` (linear-operator); `HistoricalSylvesterRight` (self-adjoint-operator) |
| `A_1` | `A1` (self-adjoint-operator); `ReferenceBlock1` (self-adjoint-operator) |
| `B` | `B` (linear-operator); `SylvesterLeft` (self-adjoint-operator); `Bblock` (linear-operator); `SkewDirection` (linear-operator) |
| `C` | `SylvesterRight` (self-adjoint-operator); `Cblock` (linear-operator); `Cturn` (matrix); `PairCosineBlock` (matrix); `TraceCost` (scalar-cost); `HalmosCosineBlock` (linear-operator) |
| `D` | `Rrotation` (unitary-operator); `SourceDirectRotation` (unitary-operator); `Dblock` (matrix); `Dplanar` (unitary-operator); `PairDirectRotation` (unitary-operator) |
| `E` | `SpectralMeasure` (projection-valued-measure); `GradientPhaseProjection` (orthogonal-projection) |
| `H` | `H` (self-adjoint-operator); `Hreflection` (linear-operator) |
| `M` | `NormM` (norm); `Matching` (matching); `CounterMovingPlane` (linear-subspace) |
| `P` | `Psource` (orthogonal-projection); `P` (orthogonal-projection) |
| `Q` | `Qtarget` (orthogonal-projection); `Q` (orthogonal-projection); `NormQ` (norm) |
| `R` | `R` (linear-operator); `PlanarRotationBase` (notation-base) |
| `S` | `SpectralSet` (set); `S` (linear-operator); `PairSineBlock` (matrix); `HalmosSineBlock` (linear-operator) |
| `U` | `U` (linear-subspace); `Usource` (linear-subspace); `PairFreeOrthogonal` (unitary-operator) |
| `V` | `V` (linear-subspace); `Vtarget` (linear-subspace); `YWSV` (isometric-embedding) |
| `X` | `Xframe` (isometric-embedding); `X` (linear-operator); `ProjectionRealPart` (linear-operator) |
| `Y` | `Yframe` (isometric-embedding); `SylvesterRHS` (linear-operator); `ProjectionImaginaryPart` (linear-operator) |
| `\Gamma` | `RieszContour` (contour); `CompressionProjectionImage` (orthogonal-projection) |
| `\Omega` | `PrincipalPlaneProjectionBase` (notation-base); `PinchingProjectionOne` (orthogonal-projection) |
| `\Sigma` | `ReflectionSigma` (unitary-operator); `Sigma` (matrix) |
| `\alpha` | `alphaAngle` (angle); `alphaEndpoint` (scalar) |
| `\delta` | `delta` (scalar); `KroneckerDelta` (scalar) |
| `\eta` | `ProjectionCoupling` (scalar); `CompressionTolerance` (scalar) |
| `\gamma` | `PairAttainingAngle` (angle); `SylvesterGapThreshold` (scalar); `MatchingPhaseGamma` (scalar) |
| `\lambda` | `ProjectionEigenvalue` (scalar); `SpectralValue` (scalar) |
| `\mathcalH` | `AmbientHilbertSpace` (hilbert-space); `GeneralHilbertSpace` (hilbert-space) |
| `\sigma` | `SpectrumSymbol` (operator-notation); `SingularValueBase` (notation-base) |
| `\sigma_j` | `TransportSingularValues` (scalar); `DisplacementSingular` (scalar); `SingularValue` (scalar) |
| `\varepsilon` | `EpsilonAngle` (angle); `EigenvalueExampleEpsilon` (scalar); `FrameLowerBoundEpsilon` (scalar) |
| `\varphi` | `PhiAngle` (angle); `GradientEigenphase` (angle); `PlaneRotationAngle` (angle) |
| `\widehatA` | `Ahat` (self-adjoint-operator); `Acurrent` (self-adjoint-operator) |
| `a` | `SingletonPowerCost` (scalar-cost); `PairPhaseCosineX` (scalar); `CounterChordA` (scalar); `SylvesterScalarRight` (scalar) |
| `b` | `b` (scalar); `PairPowerCost` (scalar-cost); `PairPhaseCosineY` (scalar); `CounterChordB` (scalar); `SylvesterScalarLeft` (scalar) |
| `c` | `CosAngle` (scalar-or-operator); `SingletonCost` (scalar-cost); `PairCost` (scalar-cost) |
| `g` | `GradientLevel` (scalar); `g` (scalar) |
| `r` | `r` (vector); `PairRotationR` (angle) |
| `s` | `SinAngle` (scalar-or-operator); `DisplacementSize` (scalar); `PairRotationS` (angle) |
| `x` | `SourceVector` (vector); `PairPhaseX` (angle); `RayleighTestVector` (vector); `SylvesterScalarUnknown` (scalar) |
| `y` | `TargetVector` (vector); `PairPhaseY` (angle); `SylvesterScalarRHS` (scalar) |

## Semantic variants and their handwritten suffixes

Even when a base key is registered, `\like{Key}{...}` may manually spell a different glyph, and `\sym{Key}_j` may create a new indexed form. These variants are listed separately so the registry owner can decide whether any merit their own declarations. No names are changed here.

| Registry key and printed source expression | Occurrences | Sample locations |
|---|---:|---|
| `theta :: \symglyph{theta}_j` | 25 | `paper.tex:416`, `paper.tex:417`, `paper.tex:422`, `paper.tex:524` |
| `Psource :: \symglyph{Psource}_K` | 21 | `formalization_enabled_extension.tex:127`, `formalization_enabled_extension.tex:135`, `formalization_enabled_extension.tex:144`, `formalization_enabled_extension.tex:155` |
| `theta :: \symglyph{theta}_i` | 20 | `formalization_enabled_extension.tex:23`, `formalization_enabled_extension.tex:24`, `formalization_enabled_extension.tex:31`, `formalization_enabled_extension.tex:32` |
| `F1 :: \symglyph{F1}^*` | 12 | `paper.tex:769`, `paper.tex:771`, `paper.tex:781`, `paper.tex:874` |
| `Rrotation :: \symglyph{Rrotation}_{\symglyph{theta}}` | 12 | `counterexample.tex:46`, `counterexample.tex:49`, `counterexample.tex:94`, `counterexample.tex:97` |
| `Wcompetitor :: \symglyph{Wcompetitor}_{\symglyph{theta}}` | 11 | `counterexample.tex:44`, `counterexample.tex:45`, `counterexample.tex:48`, `counterexample.tex:63` |
| `SingletonCost :: \symglyph{SingletonCost}_i` | 10 | `formalization_enabled_extension.tex:29`, `formalization_enabled_extension.tex:32`, `formalization_enabled_extension.tex:62`, `formalization_enabled_extension.tex:71` |
| `E0 :: \symglyph{E0}^*` | 8 | `paper.tex:741`, `paper.tex:1017`, `paper.tex:1063`, `paper.tex:1065` |
| `OrderedSeparation :: _{\sym{delta}}` | 8 | `appendices.tex:274`, `appendices.tex:278`, `appendices.tex:285`, `appendices.tex:286` |
| `PairCost :: \symglyph{PairCost}_{ij}` | 8 | `formalization_enabled_extension.tex:28`, `formalization_enabled_extension.tex:31`, `formalization_enabled_extension.tex:60`, `formalization_enabled_extension.tex:73` |
| `PowerCost :: \symglyph{PowerCost}_p` | 8 | `formalization_enabled_extension.tex:120`, `formalization_enabled_extension.tex:137`, `formalization_enabled_extension.tex:149`, `formalization_enabled_extension.tex:150` |
| `PairFreeOrthogonal :: \symglyph{PairFreeOrthogonal}_0` | 7 | `formalization_enabled_extension.tex:447`, `formalization_enabled_extension.tex:471`, `formalization_enabled_extension.tex:489`, `formalization_enabled_extension.tex:493` |
| `PairFreeOrthogonal :: \symglyph{PairFreeOrthogonal}_1` | 6 | `formalization_enabled_extension.tex:447`, `formalization_enabled_extension.tex:490`, `formalization_enabled_extension.tex:494`, `formalization_enabled_extension.tex:495` |
| `F0 :: \symglyph{F0}^*` | 5 | `paper.tex:1052`, `paper.tex:1053`, `paper.tex:1061`, `paper.tex:1185` |
| `SinAngle :: \symglyph{SinAngle}^2` | 5 | `counterexample.tex:64`, `counterexample.tex:65`, `counterexample.tex:72`, `counterexample.tex:84` |
| `CosAngle :: \symglyph{CosAngle}^2` | 4 | `counterexample.tex:64`, `counterexample.tex:65`, `counterexample.tex:72`, `counterexample.tex:84` |
| `RealField :: ^2` | 4 | `paper.tex:1176`, `counterexample.tex:69`, `counterexample.tex:282` |
| `RealField :: ^4` | 4 | `counterexample.tex:44`, `counterexample.tex:120`, `figures/Fig2.pgf:1718`, `figures/Fig2.pgf:1724` |
| `Vtarget :: \symglyph{Vtarget}_{\symglyph{theta}}` | 4 | `counterexample.tex:44`, `counterexample.tex:45`, `counterexample.tex:69`, `counterexample.tex:76` |
| `theta :: \symglyph{theta}_1` | 4 | `formalization_enabled_extension.tex:13`, `formalization_enabled_extension.tex:676`, `figures/Fig2.pgf:1700`, `figures/Fig3.pgf:122` |
| `IntertwinerT :: \symglyph{IntertwinerT}^*` | 3 | `paper.tex:623`, `paper.tex:626`, `paper.tex:634` |
| `PairPhaseCosineX :: ^2` | 3 | `formalization_enabled_extension.tex:497`, `formalization_enabled_extension.tex:498`, `formalization_enabled_extension.tex:507` |
| `PairPhaseCosineY :: ^2` | 3 | `formalization_enabled_extension.tex:497`, `formalization_enabled_extension.tex:498`, `formalization_enabled_extension.tex:507` |
| `PairPowerCost :: \symglyph{PairPowerCost}_{ij}(p)` | 3 | `formalization_enabled_extension.tex:545`, `formalization_enabled_extension.tex:575`, `formalization_enabled_extension.tex:591` |
| `ProjectionImaginaryPart :: ^2` | 3 | `formalization_enabled_extension.tex:352`, `formalization_enabled_extension.tex:360`, `formalization_enabled_extension.tex:368` |
| `SingletonCost :: \symglyph{SingletonCost}_j` | 3 | `formalization_enabled_extension.tex:73`, `formalization_enabled_extension.tex:94`, `appendices.tex:77` |
| `SingletonPowerCost :: \symglyph{SingletonPowerCost}_i(p)` | 3 | `formalization_enabled_extension.tex:426`, `formalization_enabled_extension.tex:576`, `formalization_enabled_extension.tex:592` |
| `SourceDirectRotation :: ^2` | 3 | `appendices.tex:340`, `appendices.tex:346`, `appendices.tex:352` |
| `TraceCost :: \symglyph{TraceCost}(M)` | 3 | `formalization_enabled_extension.tex:78`, `appendices.tex:77`, `figures/Fig3.pgf:301` |
| `Wcompetitor :: \symglyph{Wcompetitor}_{\symglyph{PiConstant}/4}` | 3 | `counterexample.tex:183`, `counterexample.tex:190`, `counterexample.tex:194` |
| `Wcompetitor :: ^T` | 3 | `formalization_enabled_extension.tex:40`, `formalization_enabled_extension.tex:135`, `formalization_enabled_extension.tex:391` |
| `theta :: \symglyph{theta}_2` | 3 | `formalization_enabled_extension.tex:676`, `figures/Fig2.pgf:1700`, `figures/Fig3.pgf:158` |
| `A :: \symglyph{A}_\varepsilon` | 2 | `paper.tex:492`, `paper.tex:498` |
| `Acurrent :: \symglyph{Acurrent}_\varepsilon` | 2 | `paper.tex:494`, `paper.tex:498` |
| `DisplacementSingular :: 0` | 2 | `figures/Fig2.pgf:1508`, `figures/Fig2.pgf:1514` |
| `DisplacementSingular :: \symglyph{SingularValueBase}_1` | 2 | `figures/Fig2.pgf:1052`, `figures/Fig2.pgf:1301` |
| `DisplacementSingular :: \symglyph{SingularValueBase}_2` | 2 | `figures/Fig2.pgf:1058`, `figures/Fig2.pgf:1307` |
| `DisplacementSingular :: \symglyph{SingularValueBase}_3` | 2 | `figures/Fig2.pgf:1064`, `figures/Fig2.pgf:1313` |
| `DisplacementSingular :: \symglyph{SingularValueBase}_4` | 2 | `figures/Fig2.pgf:1070`, `figures/Fig2.pgf:1319` |
| `DisplacementSize :: ^p` | 2 | `formalization_enabled_extension.tex:633`, `formalization_enabled_extension.tex:638` |
| `FigureInput :: z` | 2 | `figures/Fig2.pgf:930`, `figures/Fig2.pgf:936` |
| `GradientEigenphase :: \symglyph{GradientEigenphase}_1` | 2 | `formalization_enabled_extension.tex:335`, `formalization_enabled_extension.tex:339` |
| `GradientEigenphase :: \symglyph{GradientEigenphase}_2` | 2 | `formalization_enabled_extension.tex:335`, `formalization_enabled_extension.tex:339` |
| `HalmosCosineBlock :: \symglyph{HalmosCosineBlock}^2` | 2 | `paper.tex:561`, `paper.tex:562` |
| `HalmosSineBlock :: \symglyph{HalmosSineBlock}^2` | 2 | `paper.tex:561`, `paper.tex:562` |
| `IntervalSeparation :: _{\sym{delta}}` | 2 | `appendices.tex:270`, `appendices.tex:284` |
| `PrincipalPlaneProjectionBase :: \symglyph{PrincipalPlaneProjectionBase}_k` | 2 | `counterexample.tex:199`, `counterexample.tex:202` |
| `RealField :: ^6` | 2 | `formalization_enabled_extension.tex:90`, `formalization_enabled_extension.tex:99` |
| `RealField :: ^n` | 2 | `formalization_enabled_extension.tex:12`, `formalization_enabled_extension.tex:143` |
| `S :: ^*` | 2 | `paper.tex:1075`, `paper.tex:1081` |
| `SpectralGradient :: \symglyph{SpectralGradient}^2` | 2 | `formalization_enabled_extension.tex:294`, `formalization_enabled_extension.tex:296` |
| `SpectralValue :: \symglyph{SpectralValue}_j` | 2 | `paper.tex:483` |
| `TargetVector :: \symglyph{TargetVector}_j` | 2 | `paper.tex:421`, `paper.tex:422` |
| `Wcompetitor :: ^*` | 2 | `paper.tex:640`, `appendices.tex:230` |
| `Wcompetitor :: ^2` | 2 | `formalization_enabled_extension.tex:492`, `formalization_enabled_extension.tex:502` |
| `ComplexField :: ^2` | 1 | `counterexample.tex:281` |
| `CompressionTolerance :: ^2` | 1 | `appendices.tex:471` |
| `E0 :: ^*` | 1 | `appendices.tex:445` |
| `FigureImage :: Du_1` | 1 | `figures/Fig2.pgf:216` |
| `FigureImage :: Du_2` | 1 | `figures/Fig2.pgf:489` |
| `FigureImage :: Wx` | 1 | `figures/Fig2.pgf:762` |
| `FigureImage :: Wz` | 1 | `figures/Fig2.pgf:930` |
| `FigureInput :: x` | 1 | `figures/Fig2.pgf:756` |
| `FrameLowerBoundEpsilon :: ^2` | 1 | `appendices.tex:445` |
| `GradientComplexStructure :: ^2` | 1 | `formalization_enabled_extension.tex:302` |
| `GradientLevel :: \symglyph{GradientLevel}^2` | 1 | `formalization_enabled_extension.tex:300` |
| `GradientOffDiagonal :: \symglyph{GradientOffDiagonal}^T` | 1 | `formalization_enabled_extension.tex:275` |
| `GradientPhaseProjection :: ^*` | 1 | `formalization_enabled_extension.tex:349` |
| `GradientPhaseProjection :: ^2` | 1 | `formalization_enabled_extension.tex:349` |
| `Hmix :: ^T` | 1 | `counterexample.tex:63` |
| `Jreflect :: ^2` | 1 | `formalization_enabled_extension.tex:317` |
| `KroneckerDelta :: \symglyph{KroneckerDelta}_{ij}` | 1 | `paper.tex:422` |
| `Matching :: \varnothing` | 1 | `figures/Fig3.pgf:307` |
| `Matching :: \{\{1,2\}\}` | 1 | `figures/Fig3.pgf:319` |
| `Matching :: \{\{1,3\}\}` | 1 | `figures/Fig3.pgf:331` |
| `Matching :: \{\{2,3\}\}` | 1 | `figures/Fig3.pgf:343` |
| `MatchingEdgeWeight :: +0.0666` | 1 | `figures/Fig3.pgf:272` |
| `MatchingEdgeWeight :: +0.1310` | 1 | `figures/Fig3.pgf:224` |
| `MatchingEdgeWeight :: -0.1381` | 1 | `figures/Fig3.pgf:248` |
| `MatchingPlanarRotation :: ^T` | 1 | `formalization_enabled_extension.tex:195` |
| `MatchingSourceSubspace :: ^{\perp}` | 1 | `formalization_enabled_extension.tex:271` |
| `PairDirectRotation :: ^T` | 1 | `formalization_enabled_extension.tex:448` |
| `PlaneRotationAngle :: +45^\circ` | 1 | `figures/Fig2.pgf:1754` |
| `PlaneRotationAngle :: +90^\circ` | 1 | `figures/Fig2.pgf:1766` |
| `PlaneRotationAngle :: -45^\circ` | 1 | `figures/Fig2.pgf:1760` |
| `PlaneRotationAngle :: 0^\circ` | 1 | `figures/Fig2.pgf:1772` |
| `ProjectionCoupling :: ^2` | 1 | `formalization_enabled_extension.tex:370` |
| `ProjectionImaginaryPart :: ^T` | 1 | `formalization_enabled_extension.tex:351` |
| `ProjectionRealPart :: ^2` | 1 | `formalization_enabled_extension.tex:352` |
| `ProjectionRealPart :: ^T` | 1 | `formalization_enabled_extension.tex:351` |
| `Psource :: \symglyph{Psource}_U` | 1 | `paper.tex:840` |
| `Psource :: \symglyph{Psource}_{\mathrm{gen}}` | 1 | `paper.tex:559` |
| `Qtarget :: \symglyph{Qtarget}_{\mathrm{gen}}` | 1 | `paper.tex:561` |
| `RealField :: ^{n\times n}` | 1 | `formalization_enabled_extension.tex:133` |
| `Rrotation :: \symglyph{Rrotation}^*` | 1 | `paper.tex:630` |
| `Rrotation :: \symglyph{Rrotation}_{\symglyph{PiConstant}/4}` | 1 | `counterexample.tex:191` |
| `SingletonCost :: \symglyph{SingletonCost}_1` | 1 | `figures/Fig3.pgf:128` |
| `SingletonCost :: \symglyph{SingletonCost}_2` | 1 | `figures/Fig3.pgf:164` |
| `SingletonCost :: \symglyph{SingletonCost}_3` | 1 | `figures/Fig3.pgf:200` |
| `SingletonPowerCost :: \symglyph{SingletonPowerCost}_i(1)` | 1 | `formalization_enabled_extension.tex:649` |
| `SingletonPowerCost :: \symglyph{SingletonPowerCost}_j(p)` | 1 | `formalization_enabled_extension.tex:577` |
| `SkewDirection :: ^T` | 1 | `formalization_enabled_extension.tex:171` |
| `SourceDirectRotation :: ^*` | 1 | `appendices.tex:379` |
| `SourceVector :: \symglyph{SourceVector}_i` | 1 | `paper.tex:422` |
| `SourceVector :: \symglyph{SourceVector}_j` | 1 | `paper.tex:421` |
| `SourceVector :: u_1` | 1 | `figures/Fig2.pgf:210` |
| `SourceVector :: u_2` | 1 | `figures/Fig2.pgf:483` |
| `TraceCost :: 4.4350` | 1 | `figures/Fig3.pgf:325` |
| `TraceCost :: 4.4994` | 1 | `figures/Fig3.pgf:349` |
| `TraceCost :: 4.5660` | 1 | `figures/Fig3.pgf:313` |
| `TraceCost :: 4.7041` | 1 | `figures/Fig3.pgf:337` |
| `Xframe :: \symglyph{Xframe}^*` | 1 | `paper.tex:416` |
| `Xframe :: ^T` | 1 | `counterexample.tex:77` |
| `Yframe :: ^T` | 1 | `counterexample.tex:84` |
| `theta :: \symglyph{theta}_3` | 1 | `figures/Fig3.pgf:194` |
| `theta :: \symglyph{theta}_m` | 1 | `formalization_enabled_extension.tex:13` |
| `v :: \symglyph{v}_{\symglyph{theta}}` | 1 | `paper.tex:1283` |

## Raw mathematical atoms: all distinct source forms

Every item below was printed directly in math mode rather than supplied by a `\sym` glyph definition. The `Registered glyph?` column finds exact glyph matches, **not** semantic equivalence. `script` counts indicate uses inside subscripts/superscripts, including `\like` variants. All locations are in the occurrence CSV.

| Raw source form | Occurrences | Script/variant uses | Registered glyph? | Sample locations |
|---|---:|---:|---|---|
| `j` | 75 | 68 | — | `paper.tex:416`, `paper.tex:417`, `paper.tex:421`, `paper.tex:422` |
| `i` | 71 | 59 | — | `paper.tex:422`, `paper.tex:693`, `counterexample.tex:282`, `counterexample.tex:286` |
| `p` | 50 | 23 | — | `paper.tex:810`, `paper.tex:812`, `paper.tex:822`, `paper.tex:823` |
| `T` | 46 | 12 | `IntertwinerT` | `paper.tex:278`, `paper.tex:1157`, `paper.tex:1476`, `paper.tex:1477` |
| `x` | 42 | 2 | `SourceVector, PairPhaseX, RayleighTestVector, SylvesterScalarUnknown` | `paper.tex:683`, `paper.tex:684`, `paper.tex:1115`, `paper.tex:1116` |
| `K` | 36 | 21 | `MatchingSourceSubspace` | `formalization_enabled_extension.tex:127`, `formalization_enabled_extension.tex:135`, `formalization_enabled_extension.tex:144`, `formalization_enabled_extension.tex:155` |
| `t` | 36 | 1 | — | `formalization_enabled_extension.tex:162`, `formalization_enabled_extension.tex:172`, `formalization_enabled_extension.tex:174`, `formalization_enabled_extension.tex:175` |
| `u` | 27 | 0 | `u` | `paper.tex:1147`, `paper.tex:1150`, `paper.tex:1152`, `formalization_enabled_extension.tex:357` |
| `B` | 22 | 0 | `B, SylvesterLeft, Bblock, SkewDirection` | `paper.tex:747`, `paper.tex:891`, `paper.tex:1157`, `appendices.tex:270` |
| `Z` | 20 | 0 | `CounterFixedPlane` | `paper.tex:808`, `paper.tex:809`, `paper.tex:810`, `paper.tex:812` |
| `b` | 20 | 0 | `b, PairPowerCost, PairPhaseCosineY, CounterChordB, SylvesterScalarLeft` | `paper.tex:1107`, `paper.tex:1109`, `paper.tex:1111`, `paper.tex:1117` |
| `n` | 20 | 11 | — | `paper.tex:400`, `paper.tex:480`, `paper.tex:1128`, `formalization_enabled_extension.tex:12` |
| `C` | 18 | 0 | `SylvesterRight, Cblock, Cturn, PairCosineBlock, TraceCost, HalmosCosineBlock` | `paper.tex:891`, `appendices.tex:270`, `appendices.tex:272`, `appendices.tex:274` |
| `z` | 13 | 3 | — | `paper.tex:687`, `paper.tex:688`, `paper.tex:689`, `paper.tex:693` |
| `a` | 12 | 2 | `SingletonPowerCost, PairPhaseCosineX, CounterChordA, SylvesterScalarRight` | `paper.tex:256`, `paper.tex:1114`, `paper.tex:1115`, `formalization_enabled_extension.tex:143` |
| `v` | 12 | 0 | `v` | `paper.tex:1147`, `paper.tex:1150`, `paper.tex:1152`, `formalization_enabled_extension.tex:363` |
| `\infty` | 11 | 0 | — | `paper.tex:256`, `paper.tex:810`, `paper.tex:1105`, `paper.tex:1117` |
| `I` | 10 | 0 | `Identity` | `paper.tex:1109`, `paper.tex:1111`, `paper.tex:1114`, `formalization_enabled_extension.tex:505` |
| `M` | 10 | 3 | `NormM, Matching, CounterMovingPlane` | `paper.tex:278`, `paper.tex:279`, `paper.tex:1352`, `paper.tex:1353` |
| `X` | 9 | 0 | `Xframe, X, ProjectionRealPart` | `appendices.tex:411`, `appendices.tex:416`, `appendices.tex:420`, `appendices.tex:421` |
| `c` | 7 | 0 | `CosAngle, SingletonCost, PairCost` | `paper.tex:536`, `paper.tex:537`, `formalization_enabled_extension.tex:459` |
| `e_0` | 7 | 0 | — | `counterexample.tex:168`, `counterexample.tex:169`, `counterexample.tex:205`, `counterexample.tex:224` |
| `Y` | 6 | 0 | `Yframe, SylvesterRHS, ProjectionImaginaryPart` | `appendices.tex:411`, `appendices.tex:416`, `appendices.tex:420`, `appendices.tex:421` |
| `v_j` | 6 | 0 | — | `appendices.tex:384`, `appendices.tex:385`, `appendices.tex:393`, `appendices.tex:395` |
| `W` | 5 | 2 | `Wcompetitor` | `appendices.tex:399`, `figures/Fig2.pgf:762`, `figures/Fig2.pgf:930` |
| `\mathrm{range}` | 5 | 0 | — | `figures/Fig1.pgf:206`, `figures/Fig1.pgf:212`, `figures/Fig1.pgf:409`, `figures/Fig1.pgf:415` |
| `e_1` | 5 | 0 | — | `counterexample.tex:168`, `counterexample.tex:206`, `counterexample.tex:224`, `figures/Fig2.pgf:1700` |
| `e_2` | 5 | 0 | — | `counterexample.tex:169`, `counterexample.tex:206`, `counterexample.tex:224`, `figures/Fig2.pgf:1736` |
| `Z^*` | 4 | 0 | — | `paper.tex:809`, `counterexample.tex:238`, `counterexample.tex:243`, `counterexample.tex:244` |
| `\varepsilon` | 4 | 4 | `EpsilonAngle, EigenvalueExampleEpsilon, FrameLowerBoundEpsilon` | `paper.tex:492`, `paper.tex:494`, `paper.tex:498` |
| `d` | 4 | 0 | `PairHalfDifference` | `paper.tex:669`, `paper.tex:693`, `formalization_enabled_extension.tex:223` |
| `e_n` | 4 | 0 | — | `paper.tex:1128` |
| `k` | 4 | 3 | — | `counterexample.tex:199`, `counterexample.tex:202`, `counterexample.tex:203` |
| `T^*` | 3 | 0 | — | `paper.tex:278`, `appendices.tex:68`, `appendices.tex:75` |
| `\mathrm{span}` | 3 | 0 | — | `figures/Fig2.pgf:1700`, `figures/Fig2.pgf:1730`, `figures/Fig2.pgf:1736` |
| `e_3` | 3 | 0 | — | `counterexample.tex:205`, `counterexample.tex:224`, `figures/Fig2.pgf:1730` |
| `q` | 3 | 0 | `FigureInput` | `counterexample.tex:171` |
| `u_1` | 3 | 2 | — | `counterexample.tex:168`, `figures/Fig2.pgf:210`, `figures/Fig2.pgf:216` |
| `u_2` | 3 | 2 | — | `counterexample.tex:168`, `figures/Fig2.pgf:483`, `figures/Fig2.pgf:489` |
| `z^2` | 3 | 0 | — | `formalization_enabled_extension.tex:500`, `formalization_enabled_extension.tex:507`, `formalization_enabled_extension.tex:510` |
| `A_0` | 2 | 0 | `ReferenceBlock0` | `paper.tex:1020`, `appendices.tex:508` |
| `D` | 2 | 2 | `Rrotation, SourceDirectRotation, Dblock, Dplanar, PairDirectRotation` | `figures/Fig2.pgf:216`, `figures/Fig2.pgf:489` |
| `L` | 2 | 0 | `MatchingTargetSubspace` | `appendices.tex:430`, `appendices.tex:433` |
| `M^\perp` | 2 | 0 | — | `paper.tex:1353`, `paper.tex:1365` |
| `Q_-` | 2 | 0 | — | `appendices.tex:351`, `appendices.tex:353` |
| `S_2` | 2 | 0 | — | `paper.tex:816`, `paper.tex:828` |
| `\mathrm{HS}` | 2 | 0 | — | `appendices.tex:456`, `appendices.tex:457` |
| `\mathrm{gen}` | 2 | 2 | — | `paper.tex:559`, `paper.tex:561` |
| `\mathrm{plane}` | 2 | 0 | — | `formalization_enabled_extension.tex:204`, `formalization_enabled_extension.tex:207` |
| `\mathtt{A_0}` | 2 | 0 | — | `appendices.tex:115`, `appendices.tex:117` |
| `g` | 2 | 0 | `GradientLevel, g` | `paper.tex:1184` |
| `h` | 2 | 0 | `PairMeanAngle` | `paper.tex:1184` |
| `m` | 2 | 1 | — | `formalization_enabled_extension.tex:13`, `formalization_enabled_extension.tex:15` |
| `v^*` | 2 | 0 | — | `paper.tex:1147`, `paper.tex:1150` |
| `B^*` | 1 | 0 | — | `paper.tex:747` |
| `B^{-1}` | 1 | 0 | — | `appendices.tex:413` |
| `C_0` | 1 | 0 | `SingletonBaseline` | `appendices.tex:246` |
| `C_0^2` | 1 | 0 | — | `appendices.tex:350` |
| `C_1` | 1 | 0 | `ComplementCosineBlock` | `appendices.tex:246` |
| `C_j` | 1 | 0 | — | `appendices.tex:247` |
| `F^2` | 1 | 0 | — | `formalization_enabled_extension.tex:266` |
| `I_2` | 1 | 0 | `IdentityTwo` | `counterexample.tex:59` |
| `N` | 1 | 0 | `NormN` | `paper.tex:278` |
| `S_0` | 1 | 0 | — | `appendices.tex:246` |
| `S_0^*` | 1 | 0 | — | `appendices.tex:246` |
| `S_1` | 1 | 0 | — | `paper.tex:814` |
| `S_p` | 1 | 0 | — | `paper.tex:812` |
| `U` | 1 | 1 | `U, Usource, PairFreeOrthogonal` | `paper.tex:840` |
| `\Pi_1` | 1 | 0 | `CounterPrincipalOne` | `counterexample.tex:166` |
| `\Pi_2` | 1 | 0 | `CounterPrincipalTwo` | `counterexample.tex:166` |
| `\ell^2` | 1 | 0 | — | `paper.tex:1127` |
| `\mathbb N_{\geq1}` | 1 | 0 | — | `paper.tex:1127` |
| `\mathrm{ker}` | 1 | 0 | — | `figures/Fig2.pgf:1748` |
| `\mathtt{H}` | 1 | 0 | — | `appendices.tex:120` |
| `\operatorname{Re}` | 1 | 0 | — | `formalization_enabled_extension.tex:355` |
| `e^{\pm i(\sym{PairPhaseX}+\sym{PairPhaseY})}` | 1 | 0 | — | `formalization_enabled_extension.tex:513` |
| `e^{\pm i(\sym{PairPhaseX}-\sym{PairPhaseY})}` | 1 | 0 | — | `formalization_enabled_extension.tex:514` |
| `e^{\pm it}` | 1 | 0 | — | `formalization_enabled_extension.tex:553` |
| `e^{\sym{AngleGenerator}\sym{Theta}}` | 1 | 0 | — | `appendices.tex:248` |
| `e^{i\like{GradientEigenphase}{\symglyph{GradientEigenphase}_1}}` | 1 | 0 | — | `formalization_enabled_extension.tex:339` |
| `e^{i\like{GradientEigenphase}{\symglyph{GradientEigenphase}_2}}` | 1 | 0 | — | `formalization_enabled_extension.tex:339` |
| `e^{i\sym{theta}}` | 1 | 0 | — | `counterexample.tex:287` |
| `z^3` | 1 | 0 | — | `formalization_enabled_extension.tex:506` |
| `z^4` | 1 | 0 | — | `formalization_enabled_extension.tex:506` |

## Raw TeX commands that bypass the registry

These are *not assumed to be mathematical symbols*. They include user-defined helpers, formatting commands, and class-specific macros. Their occurrences are exhaustive for this category; each must be classified before claiming full semantic coverage.

| Control sequence | Uses | Sample locations |
|---|---:|---|

## Remaining mathematical vocabulary (operators, numerals, and syntax)

No glyphs are discarded from the scanner. Standard LaTeX controls and punctuation are tallied here rather than being treated as candidate object names.

### layout (197 occurrences; 18 distinct)

`\qquad` × 42, `\\` × 31, `\quad` × 25, `\sqrt` × 22, `\bigl` × 15, `\bigr` × 15, `\` × 11, `\,` × 10, `\frac` × 5, `\left` × 5, `\right` × 5, `\ldots` × 3, `\underbrace` × 2, `\;` × 2, `\substack` × 1, `\hline` × 1, `\big` × 1, `\tfrac` × 1

### number (677 occurrences; 34 distinct)

`2` × 294, `1` × 153, `0` × 109, `4` × 49, `3` × 20, `8` × 6, `45^\circ` × 6, `2^p` × 5, `6` × 4, `12` × 3, `0.7` × 2, `30^\circ` × 2, `75^\circ` × 2, `4.4350` × 2, `1.9` × 1, `40^\circ` × 1, `0_2` × 1, `37.5^\circ` × 1, `16` × 1, `90^\circ` × 1, `0^\circ` × 1, `0.765` × 1, `1.414` × 1, `3.061` × 1, `2.828` × 1, `1.0353` × 1, `1.5307` × 1, `2.0000` × 1, `0.1310` × 1, `0.1381` × 1, `0.0666` × 1, `4.5660` × 1, `4.7041` × 1, `4.4994` × 1

### registered-wrapper (80 occurrences; 9 distinct)

`DKRange` × 24, `dkOperatorNorm` × 20, `DKDom` × 17, `DKKernel` × 9, `dkFrobeniusNorm` × 3, `dkTraceNorm` × 3, `dkModulus` × 2, `dkKyFanNorm` × 1, `dkHilbertSchmidtNorm` × 1

### standard-operator (1929 occurrences; 58 distinct)

`=` × 362, `-` × 271, `,` × 269, `+` × 117, `/` × 103, `\\|` × 82, `\le` × 68, `&` × 63, `\sin` × 59, `\|` × 57, `*` × 54, `\{` × 40, `\}` × 40, `\cos` × 35, `<` × 34, `\leq` × 26, `\in` × 20, `>` × 20, `\sum` × 19, `\ge` × 18, `\circ` × 14, `\langle` × 13, `\rangle` × 13, `\min` × 13, `:` × 10, `\geq` × 9, `\oplus` × 8, `\to` × 8, `\tan` × 7, `\exp` × 7, `\Vert` × 6, `\cap` × 5, `;` × 5, `\subset` × 5, `\approx` × 5, `\pm` × 4, `\max` × 3, `\subseteq` × 3, `\perp` × 3, `\cdot` × 3, `\angle` × 3, `\int` × 2, `\ne` × 2, `\cup` × 2, `\mapsto` × 2, `\binom` × 2, `\times` × 2, `\sup` × 2, `\varnothing` × 2, `\simeq` × 1, `\bigoplus` × 1, `\ker` × 1, `\det` × 1, `\prod` × 1, `\arccos` × 1, `\longrightarrow` × 1, `\Longleftrightarrow` × 1, `\downarrow` × 1

### syntax (1384 occurrences; 10 distinct)

`(` × 478, `)` × 475, `{` × 103, `}` × 103, `.` × 79, `^` × 56, `_` × 38, `]` × 23, `[` × 20, `'` × 9

## Known limits and required next work

1. Lexical coverage is not semantic completeness: a bare `x`, `X`, `A_0`, or `\Gamma` can have unrelated meanings in different contexts. This file exposes every source use but cannot decide those meanings automatically.
2. The scan follows all direct TeX/PGF `\input`/`\include` dependencies of the active `paper.tex` (not hard-coded filenames). It intentionally excludes inactive papers, standalone studies, class files, and bibliography fields. The PGF labels are derived from Python generators: edit those generators, not the generated artifacts, when changing a figure's notation.
3. A fully registry-controlled paper requires assigning roles to the raw atoms and replacing their source occurrences with `\sym`/derived glyphs; **this pass does neither**, so there is no false claim of 100% centralization.
4. The existing `\like{Key}{expression}` mechanism permits hand-written glyphs inside `expression`; this census lists those raw constituents. To make every printed variant centrally controllable, introduce explicit registry keys for meaningful variants, or use `\symglyph{Key}` plus separately registered modifiers.
5. Re-run the census when the TeX changes. Source hashes above identify exactly which version was inspected. `--require-centralized` is an optional failing check for the unfinished source migration; `--strict` checks only parser and registry integrity.
