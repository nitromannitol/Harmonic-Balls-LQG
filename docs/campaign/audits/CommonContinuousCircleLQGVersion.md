# Common continuous circle LQG version audit

The measurable continuous circle version uses the construction of Leonardo Bonanno.
This module derives a common full-measure event from raw sample continuity and
fixed-circle agreement, using a countable dense sequence and continuity on the
positive-radius parameter space. It does not require joint measurability of the
raw process or agreement of distribution pairings.

On that event the literal `lqgApprox` measures agree at every positive radius,
for every real γ and α. Dyadic positivity transports the complete `IsLQGLimit`
condition, including local finiteness, and hence `IsLQGMeasureOfField` in both
directions. The random evaluation theorem gives `AEMeasurable` for dependent
measurable positive-radius and center parameters, without claiming raw
measurability. The profile is extended by zero at nonpositive radii, which do
not occur in these equalities or in the dyadic limit.

Standalone Lean check: `~/paper-fleets/hb/lc HarmonicBalls/Proofs/GFF/CommonContinuousCircleLQGVersion.lean`.
All five printed declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. No additional literature input or numbered-result closure is claimed.
