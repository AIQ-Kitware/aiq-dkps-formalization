# Publication and mathematical anchors

Repository references are treated as validated, per Jon’s instruction.
Card titles are shortened for legibility where needed; full titles appear below.
No new claim of first priority is inferred from a named theorem or a date.

## jordan

Camille Jordan (1875). *Essai sur la géométrie à n dimensions*. Bull. Soc. Math. France 3, 103–174. [Publication](https://doi.org/10.24033/bsmf.90).

## rayleigh

John William Strutt (Lord Rayleigh) (1877). *The Theory of Sound, volume 1*. Macmillan, London.

## ritz

Walter Ritz (1909). *Über eine neue Methode zur Lösung gewisser Variationsprobleme der mathematischen Physik*. J. reine angew. Math. 135, 1–61. [Publication](https://doi.org/10.1515/crll.1909.135.1).

## weyl

Hermann Weyl (1912). *Das asymptotische Verteilungsgesetz der Eigenwerte linearer partieller Differentialgleichungen (mit einer Anwendung auf die Theorie der Hohlraumstrahlung)*. Math. Ann. 71, 441–479. [Publication](https://doi.org/10.1007/BF01456804).

## hotelling

Harold Hotelling (1936). *Relations Between Two Sets of Variates*. Biometrika 28, 321–377. [Publication](https://doi.org/10.1093/biomet/28.3-4.321).

## sznagy

Béla Sz.-Nagy (1947). *Perturbations des transformations autoadjointes dans l’espace de Hilbert*. Comment. Math. Helv. 19, 347–366.

## davis58

Chandler Davis (1958). *Separation of Two Linear Subspaces*. Acta Sci. Math. (Szeged) 19, 172–187. [Publication](https://acta.bibl.u-szeged.hu/13858/1/math_019_fasc_003_004_172-187.pdf).

## kato

Tosio Kato (1966). *Perturbation Theory for Linear Operators*. Springer, first edition. [Publication](https://doi.org/10.1007/978-3-662-12678-3).

## halmos

Paul R. Halmos (1969). *Two Subspaces*. Trans. AMS 144, 381–389. [Publication](https://doi.org/10.1090/S0002-9947-1969-0251519-5).

## rosenblum

Marvin Rosenblum (1956). *On the Operator Equation BX − XA = Q*. Duke Math. J. 23, 263–269. [Publication](https://doi.org/10.1215/S0012-7094-56-02324-9).

## davis63

Chandler Davis (1963 / 1965). *The Rotation of Eigenvectors by a Perturbation, I / II*. J. Math. Anal. Appl. 6, 159–173; 11, 20–27. [Publication](https://doi.org/10.1016/0022-247X(63)90001-5).

## dk

Chandler Davis · William Kahan (1970). *The Rotation of Eigenvectors by a Perturbation. III*. SIAM J. Numer. Anal. 7, 1–46. [Publication](https://doi.org/10.1137/0707001).

## wedin

Per-Åke Wedin (1972). *Perturbation Bounds in Connection with Singular Value Decomposition*. BIT 12, 99–111. [Publication](https://doi.org/10.1007/BF01932678).

## golub

Åke Björck · Gene H. Golub (1973). *Numerical Methods for Computing Angles Between Linear Subspaces*. Math. Comp. 27, 579–594. [Publication](https://doi.org/10.1090/S0025-5718-1973-0348991-3).

## yws

Yi Yu · Tengyao Wang · Richard J. Samworth (2014 preprint / 2015 journal). *A Useful Variant of the Davis–Kahan Theorem for Statisticians*. Biometrika 102, 315–323. [Publication](https://doi.org/10.1093/biomet/asv008).

## quench

Hayden Helm · Ben Johnson · Carey E. Priebe (2026). *Query-Efficient Model Evaluation Using Cached Responses*. ICML · PMLR 306, 42691–42706. [Publication](https://proceedings.mlr.press/v306/helm26a.html).

## vonneumann

John von Neumann (1937). *Some Matrix-Inequalities and Metrization of Matric-Space*. Tomsk University Review 1, 286–300.

## schatten

Robert Schatten (1950). *A Theory of Cross-Spaces*. Princeton · Annals of Math. Studies 26.

## fan

Ky Fan (1951). *Maximum Properties and Inequalities for the Eigenvalues of Completely Continuous Operators*. PNAS 37, 760–766. [Publication](https://doi.org/10.1073/pnas.37.11.760).

## Scene-to-source correspondence

| Scenes | Evidence |
| --- | --- |
| HiJordan through HiRosenblum | Bibliography keys `jordan1875essai`, `rayleigh1877sound`, `ritz1909variations`, `weyl1912eigenwerte`, `hotelling1936relations`, `sznagy1947perturbations`, `davis1958separation`, `kato1966perturbation`, `halmos1969two`, `sylvester1884equation`, `rosenblum1956equation`; manuscript §2 historical exposition. |
| HiDavisKahan, HiBound | `davis1963rotation`, `davis1965rotation`, `daviskahan1969bounds`, `davis1970rotation`; source reconstruction and 29-result inventory. The bound slide is a conceptual schematic, not a replacement for the gap hypotheses. |
| HiWedinGolub | `wedin1972perturbation`, `bjorck1973numerical`. |
| HiYws | `yu2015davis`; 2014 preprint arXiv:1405.0680; YWS source reconstruction, Theorems 2 and 3. |
| HiQuench | `helm2026query`; application semantic reviews. This is a short application sketch, not a claim that every raw-source formulation is proved without repair. |
| HiNormPeople | `vonneumann1937matrix`, `schatten1950crossspaces`, `fan1951maximum`. |
| HiCorrection, HiMatching, HiEvidence | Publication-direction note, transport source comparisons, source-facing counterexample and Q-norm repair, `RealNuclearMatching.lean`, upstream contribution ledger. |

## Repository evidence

- [Manuscript bibliography](../../../papers/dk_formalization_journal/references.bib)
- [Historical exposition](../../../papers/dk_formalization_journal/paper.tex)
- [Davis–Kahan source reconstruction](../../../prose/distilled_literature/DavisKahan1970_part_III.tex)
- [YWS source reconstruction](../../../prose/distilled_literature/YuWangSamworth2015_statistical_davis_kahan.tex)
- [Application semantic review](../../../dev/dkps-application-result-semantic-review.md)
- [Publication direction and precise extension scope](../../../dev/publication-direction-dkps-to-transport-2026-10-27.md)
- [Transport comparisons](../../../dev/spectral-transport-unification.md)
- [Real matching statements](../../../DavisKahan/FiniteDimensional/DirectRotation/RealNuclearMatching.lean)
- [Upstream lineage](../../../dev/tauceti/dkps-upstream-contribution-census.md)
