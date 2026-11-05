# Shared Harnack and crossing constant

2026-11-05. This is a conditional witness combination; it does not establish
Proposition 6.2 or Lemma 10.1 unconditionally or close either numbered result.
The assumptions are exactly `HarnackTypeComponentStmt.{u}` and
`ClusterBoundedCrossingsStmt.{u}`. Any staged literature inputs used to supply
them remain subject to their existing source reviews.

`HarmonicBalls.Proofs.Sec10.SharedHarnackCrossingConstant` exports:

* `component_estimate_of_smaller_threshold`: for a fixed realization and
  events, decreasing the mass threshold preserves the complete component
  conclusion. It applies monotonicity of `ENNReal.ofReal` and multiplication.
* `crossing_bound_of_smaller_threshold`: for a fixed realization, decreasing a
  positive parameter preserves the entire almost-sure eventual crossing
  conclusion. It uses reciprocal antitonicity and monotonicity of `Nat.ceil`;
  it retains the same selected radius.
* `exists_shared_harnack_crossing_constant`: takes both statement assumptions
  explicitly and states both complete conclusions directly, including the
  component events, prevalence bound and crossing bound. It retains the
  universal positive `c` and events from 6.2. For each subcritical γ it takes
  the minimum of the two witnesses and 1/2, giving a positive α below 1 before
  α₀ and every realization. The same α occurs in the mass threshold and
  crossing ceiling. No identity of the original witnesses is assumed.

The relevant frozen propositions are `Draft/Section6.lean:230-250` and
`Draft/Section10.lean:48-63`. The paper's component result is at corrected
TeX lines 1078-1081 and its explicit shared-α link is at lines 2496-2502.
This establishes that link conditionally for the frozen Lean propositions.
The source reconciliation E49 and remaining source/semantic review described in
`audits/Section10CrossingExports.md` are not resolved by this witness proof.

Checks: `lc` and `lb` pass for the module; the placeholder and heartbeat
scan is clean. `#print axioms` for each of the three exports reports only
`propext`, `Classical.choice`, and `Quot.sound`.
