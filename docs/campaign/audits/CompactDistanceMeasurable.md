# Countable set-distance representation: audit

Task: `compact-metric-distance-countable-measurability`.

The corrected paper defines set distance at lines 459–465. The proof uses the
existing `ofReal_setDist_eq_iInf` (Steps/Sec11/LocalPathLength.lean:148) and
joint continuity of a compatible length metric
(Steps/Sec11/ProperMetricDyadic.lean:77). For any nonempty subsets of the
plane, fixed dense sequences in their relative topologies exist. Continuity on
their product identifies the full infimum with the infimum over the sequences;
compactness and disjointness are not needed. The expression is precisely
`ENNReal.ofReal (setDist D K L)`.

The measurable theorem assumes continuity for every sample and measurability
only at the countably many pairs. Its a.e. version assumes continuity almost
surely and a.e. measurability at each pair. The separate representative theorem
assumes only pairwise a.e. equality with measurable evaluations; a single
countable intersection yields the a.e. equality of infima. It does not assert
equality of the underlying fields. The circle corollaries use the existing
ambient `pfefferAcross` definition, and work for nonnegative radii, hence in
particular for disjoint circles of distinct positive radii.

No proposed literature proposition is assumed. All printed axioms are
`propext`, `Classical.choice`, and `Quot.sound`. We acknowledge Leonardo
Bonanno's contributions to this formalization.
