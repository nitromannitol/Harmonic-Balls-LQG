# Circle-average lognormal moments

For `IsWholePlaneGFF P hC hcirc`, fixed `0 < L ≤ 1`, `R ≥ 0`, real `ξ, q`, and `z ∈ Metric.closedBall 0 R`, the module proves that `(exp (ξ * hcirc ω L z)) ^ q` is almost everywhere measurable and Bochner integrable. The exact ENNReal moment is `ofReal (exp ((q * ξ)^2 * Var[hcirc · L z; P] / 2))`. Its bound is the finite deterministic constant `ofReal (exp ((q * ξ)^2 * (2 * log (R + 1) - log L) / 2))`, uniform in `z`. All real `q` are covered, in particular every positive moment, and no positivity of the variance or of `ξ` is assumed.

The proof uses `IsWholePlaneGFF.lintegral_exp_circleAverage_eq` and `variance_circleAverage_eq` from `Proofs/Sec11/FixedSquareFrontierNull.lean`, together with its upper bound for the whole-plane normalization's circle average. Integrability follows by transport from mathlib's Gaussian exponential integrability. No moment bound is assumed. The centre-dependent variance is retained in the equality, and bounded only in the uniform estimate.

The module also proves null measurability of each fixed threshold event and an ENNReal Markov bound uniform over the closed ball, for positive `q` and threshold. The integrability theorem directly supplies the all-positive-moments hypothesis of `dyadic_product_tail_of_all_moments` for each fixed centre. The metric-diameter estimate and its source bridge are separate: the corrected paper's metric input is at `paper/lqg_harmonic_ball-corrected.tex:3308`, and this module does not establish it or close a numbered result.

The import closure contains Leonardo Bonanno's LatticeProb code. All six declarations print only `propext`, `Classical.choice`, and `Quot.sound`; the Lean file has no forbidden proof tokens or heartbeat overrides.
