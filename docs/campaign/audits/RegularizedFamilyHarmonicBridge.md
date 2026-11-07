# Regularized family harmonic-test bridge

`HarmonicBalls/Proofs/Sec5/RegularizedFamilyHarmonicBridge.lean` proves
`regularizedClusterFamily_isHarmonicBallFamily` with exactly the requested
premise, and in fact proves the more general
`IsSubharmonicBall.isHarmonicBallGen` for any measure and any subharmonic ball.
No literature input or additional hypothesis is used.

The corrected paper, lines 143–150 and 746–757, describes the enlarged tests and
argues from both signs of the subharmonic inequality. The formal proof keeps the
two summands separate, so no extension of the harmonic summand to the potential
witness domain is needed. Its neighbourhood of harmonicity is the open set of
points where it is harmonic. The signed Green-potential summand and its negative
use the original domain and the two source measures in opposite orders. Their
compact source set avoids the cluster, so the two source measures do not charge
the pole and their Green kernels are integrable there by
`greenFunctionIntegrableAwayFromPoleStep_holds`. Mean-value properties add by
Bochner integral linearity.

This proves a one-way implication between the frozen Lean predicates. It does
not prove the separate E51 equivalence between unrestricted and bounded
subharmonic test representatives, settle source/definition semantics or
irregular-boundary conventions, discharge staged literature premises, or
establish a numbered paper result. The proof does not invoke the unrelated
unbounded-witness representative theorem.

`#print axioms` for the final bridge reports only `propext`, `Classical.choice`,
and `Quot.sound`.
