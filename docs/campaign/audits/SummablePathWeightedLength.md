# Summable concatenation in original arclength

Task: `summable-path-arclength-weighted-integral`. This checks the deterministic
concatenation and weighted-integral step in
`~/paper-fleets/hb/notes/sec11-proof/sec11-proof-r10.tex:583-615`, for use in
the Lemma 11.12 development. It does not close a numbered result.

In `HarmonicBalls/Proofs/Metric/SummablePathWeightedLength.lean`,
`IsEuclideanLengthMetric.summablePath_parametrized_of_norm_le` proves exact
`IsLengthParametrized D (summablePath L p S) S` from length-parametrized pieces,
matching endpoints, summable durations, and shrinking Euclidean balls.
For each subinterval, finite prefix agreement gives the lower bound on length;
a limit handles the final time. The metric increment bound gives the upper
bound. The proof also supplies a version assuming endpoint convergence directly.

`IsEuclideanLengthMetric.lintegral_summablePath_of_norm_le` proves the exact
weighted integral identity over closed intervals. Consecutive half-open
intervals partition `[0,S)`, endpoint sets are null, and translation preserves
Lebesgue measure. The identity holds for every `F : ℂ → ℝ≥0∞`, so Borel
measurability and integrability are unnecessary. Both results allow zero-duration
pieces and `S = 0`. No extra literature input is introduced.

Shrinking balls alone do not imply that the path avoids zero before time `S`;
that property requires corresponding hypotheses on the pieces. No conclusion
about singular-metric finiteness, topology, or a numbered theorem is asserted.
