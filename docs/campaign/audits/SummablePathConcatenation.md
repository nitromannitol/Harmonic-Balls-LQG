# Summable path concatenation

Task: `summable-path-concatenation-endpoint`. The deterministic portion of
`~/paper-fleets/hb/notes/sec11-proof/sec11-proof-r10.tex:583-605` is proved in
`HarmonicBalls/Proofs/Metric/SummablePathConcatenation.lean` by
`IsEuclideanLengthMetric.exists_summable_path_concatenation`.

The hypotheses are matching `IsLengthParametrized` pieces `p n` of durations
`L n`, `HasSum L S`, and a shrinking Euclidean radius `r n` containing each
piece. The result supplies one curve `P` on `[0,S]`, traces each piece in
sequence, sets `P S = 0`, is Euclidean-continuous, satisfies
`D (P s) (P t) ≤ t - s` for `0 ≤ s ≤ t ≤ S`, and has
`curveLength D P 0 S ≤ ENNReal.ofReal S`. The prefix agreement theorem covers
junctions and the case in which the partial duration already equals `S`;
zero-length pieces need no positivity assumption.

Finite concatenations use `isLengthParametrized_piecewise_concat`; compatible
prefixes define the countable curve. Convergence of endpoints, derived from
the shrinking balls, and joint Euclidean continuity of `D` give the endpoint
bound. The partition definition of curve length gives the final estimate.
No stochastic or additional literature input is used.

This is a deterministic helper, not a numbered-result closure. Subsequent
obligations for the source argument include proving `IsLengthParametrized D P S`
if the consumer requires exact original-arclength parametrization, and the
weighted integral identity below for the chosen weight `F : ℂ → ℝ≥0∞`:

```lean
(∫⁻ t in Set.Icc (0 : ℝ) S, F (P t)) =
  ∑' n, ∫⁻ t in Set.Icc (0 : ℝ) (L n), F (p n t)
```

The assertion that the path visits zero only at its final time also requires
additional avoidance hypotheses on the pieces and is not part of this task.
