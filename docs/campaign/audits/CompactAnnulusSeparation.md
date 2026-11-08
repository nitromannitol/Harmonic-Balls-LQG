# Compact families of annulus across distances

`HarmonicBalls/Proofs/Metric/CompactAnnulusSeparation.lean` proves a deterministic
compactness lemma and its annulus consequence. This is a helper, not a numbered
result or a source-check of any literature input.

For one fixed `IsEuclideanLengthMetric D`, the parameter set `P` consists of
triples `(z, r, R')` in the Euclidean product topology and is required to be
compact. The theorem assumes a fixed `δ > 0` and a fixed real upper bound `R`
such that, for each triple in `P`, `0 ≤ r`, `r + δ ≤ R'`, and `R' ≤ R`.
It concludes that one `c : ℝ≥0∞` is positive and bounds the ambient
`pfefferAcross D z r R'` from below for every triple in `P`. The empty family
is allowed; there is no need to assume `R ≥ 0` separately.

The proof forms the compact image of `P × closedBall 0 R` under
`(p, v) ↦ p.1 + v`, containing both circles. It minimizes `D` on pairs in this
compact set whose Euclidean distance is at least `δ`; the separating property
of `D` makes the minimum positive. A triangle inequality supplies this
Euclidean separation for points on the two circles. The across-distance bound
then follows directly from its infimum definition. The preliminary lemma
requires only continuity, nonnegativity, and point separation of `D`.

This makes no claim about random metrics, moment bounds, or joint parameter
measurability. The import defining `pfefferAcross` contains staged literature
statements, but the proof uses none of them as premises or axioms. Both
printed axiom sets are exactly `propext`, `Classical.choice`, and `Quot.sound`.
