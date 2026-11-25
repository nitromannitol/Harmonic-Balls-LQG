# Proposition 2.5: an LQG clock from every start on one event

The frozen Proposition 2.5 (`GreenPotentialLiouvilleHolderStmt`, `HarmonicBalls/Draft/Section2.lean:161`) states the LBM
clause for every family `F` of clocks with
`∀ᵐ ω ∂P, ∀ x, IsLQGClock planarBrownianMotion γ (fieldCircleAverage α₀ (hcirc ω)) x (F ω x)`, and is proved at every
universe (`greenPotentialLiouvilleHolderStmt_holds`, `LBMClauseSubcritical.md`). This note records the proof that such a
family exists, for every `0 < γ < 2`, every `α₀ < Q` and every sample space, so that the LBM clause applies to a
clock that exists.

## What is proved

All files are in `HarmonicBalls/Proofs/Potential/`. `A_k(b, t) = ∫_0^t ε_k^{γ²/2} e^{γ h_{ε_k}(b_s)} ds` is
`lqgClockApprox γ hε (dyadicScale k) b t`, `ε_k = 2^{-k}`.

| Result | Declaration | File:line |
|---|---|---|
| a sequence Cauchy in measure uniformly on bounded time sets has a limit in the sense of `IsLQGClock` | `exists_tendsto_of_uniformCauchyInMeasure` | `UniformCauchyInMeasure.lean:25` |
| small times give small approximate clocks from a fixed start, uniformly in `k`, from a ball bound `ν_k(B_t(x)) ≤ C t^β` | `exists_pos_time_measure_clock_ge_le` | `LQGClockNearStart.lean:150` |
| uniform absolute continuity of a finite measure | `exists_pos_lt_of_absolutelyContinuous` | `LQGClockAllStarts.lean:44` |
| Cauchy in probability after a time `a > 0` from every start, from Cauchy in probability from one start | `exists_index_shift_diff_le` | `LQGClockAllStarts.lean:168` |
| an LQG clock from every start for one field | `forall_exists_isLQGClock_of_cauchy_one_start` | `LQGClockAllStarts.lean:222` |
| for almost every field, from Cauchy in probability from one start | `ae_forall_exists_isLQGClock_of_cauchy` | `LQGClockAllStarts.lean:286` |
| weighted primitives of uniformly Cauchy primitives are uniformly Cauchy | `weightedPrimitive_uniformCauchy` | `WeightedPrimitiveCauchy.lean:21` |
| the inserted approximate clocks along a path avoiding `0` are uniformly Cauchy | `uniformCauchy_inserted_of_zero` | `LQGClockInsertedEveryStart.lean:33` |
| the inserted approximate clocks are almost surely Cauchy in probability from the start `1` | `ae_cauchy_inserted_one` | `LQGClockInsertedEveryStart.lean:121` |
| a version of the clock from every start, every `0 < γ < 2`, `α < Q`, any sample space | `exists_ae_forall_isLQGClock` | `LQGClockInsertedEveryStart.lean:143` |
| the LBM clause for that family | `exists_lbmClause` | `LQGClockInsertedEveryStart.lean:157` |
| the frozen statement together with the existence of its clock family | `greenPotentialLiouvilleHolderStmt_holds_and_clock_exists` | `LQGClockInsertedEveryStart.lean:184` |
| on one field event, from every start: an LQG clock, almost surely a time-change clock (zero at zero, continuous, strictly increasing, unbounded), with speed measure `μ_h` (`E_x[τ_O] = ∫_O 2 G_O(x, y) μ_h(dy)`) | `exists_ae_forall_isLQGClock_isTimeChangeClock` | `LQGClockStrictEveryStart.lean:35` |

All declarations print `[propext, Classical.choice, Quot.sound]` (`checks/AxiomGate.lean`).

## Route

1. **After a fixed time.** For `a > 0` the law of the path after time `a` from any start is absolutely continuous with
   respect to its law from any other start (`planarBrownianMotion_map_shift_absolutelyContinuous`), uniformly in the
   sense of `exists_pos_lt_of_absolutelyContinuous`. The approximations of the shifted path are increments of the
   approximations (`lqgClockApprox_dyadic_shift`), so Cauchy convergence in probability from one start gives it from
   every start, the supremum over `[0, T]` being replaced by a supremum over a countable dense set of times
   (`exists_measurableSet_sup_diff_between`).
2. **Before a small time.** For a fixed field, the approximate measures satisfy
   `ν_k(B_s(z)) ≤ C s^β` for `‖z‖ ≤ R`, `s ≤ r₀`, uniformly in `k`
   (`IsWholePlaneGFF.ae_singular_approximant_ball_power_all_disks`). The expected occupation integral up to the exit
   time of `B_ρ(x)` is `∫ 2 G_{B_ρ(x)}(x, y) ν_k(dy)` (`GreenOccupation.lintegral_brownian_occupation_eq_green_integral`),
   at most a constant times `ρ^{β/4}` (`green_integral_ball_le_of_local_mass_growth`), and the exit time is positive.
3. **One start.** Without insertion, the approximate clocks converge almost surely locally uniformly from every fixed
   start for every `0 < γ < 2` (`ae_exists_locally_uniform_limit_clock_zero`). For the inserted field `h - α log |·|`,
   from the start `1` the path almost surely never visits `0` (`Section6.planarBrownianMotion_point_avoidance`), and for
   `ε ≤ |z|`, `h^α_ε(z) = h_ε(z) - α log |z|` (`fieldCircleAverage_eq`), so on `[0, T]` and for small `ε` the inserted
   approximations are the approximations without insertion weighted by the continuous function `|b_s|^{-γα}`.

## Departures from the cited sources

- Garban–Rhodes–Vargas 2016 (Theorem 2.7) construct the clock from every start for the massive GFF, by a coupling of
  Brownian paths from nearby starts (their Lemma 2.9). Here every start comes from the Markov property at a fixed time
  and the ball bound uniform in the scale and the centre; the field is the whole-plane GFF normalized by `h₁(0) = 0`.
- Berestycki 2015 (Theorem 1.2) gives the clock from one start, annealed. The clock from one start used here is the almost
  sure locally uniform limit of `LQGClockZeroInsertionConvergence.lean`; the inserted field is reduced to it by point
  avoidance instead of a separate analysis near the insertion point.
- The family `F` is chosen by `Classical.epsilon` for each field and start; no measurability of `F` in `(ω, x)` is
  claimed or needed by `GreenPotentialLiouvilleHolderStmt`.
