# Proposition 2.5, LBM clause: the Green identity and Hölder continuity of expected exit times

Proposition 2.5 (`prop:lbm-exit-time`, corrected draft line 530; frozen form
`GreenPotentialLiouvilleHolderStmt`, `HarmonicBalls/Draft/Section2.lean:161`) has an LBM clause
(`Draft/Section2.lean:165-169`) with two conjuncts: for every family of LQG clocks from every start,
for almost every field and every smooth bounded domain `O`, the expected exit time `E_x[τ_O]` of
Liouville Brownian motion is finite for every `x ∈ O` and Hölder continuous on `O`. The finiteness
conjunct is recorded in `LBMClauseClocksEveryStart.md`. This note records the proof of both conjuncts
through the Green identity

> `E_x[τ_O] = ∫_O 2 G_O(x, y) μ_h(dy)` for every smooth bounded `O` and every `x ∈ O`, on one field event,

and the Green clause of Proposition 2.5 (`greenPotentialHolderStmt`) applied to the constant density 2.

## What is proved

All files are in `HarmonicBalls/Proofs/Potential/`. `F ω x` is a family of clocks with
`hF : ∀ᵐ ω ∂P, ∀ x, IsLQGClock planarBrownianMotion γ (fieldCircleAverage α (hcirc ω)) x (F ω x)`, and
`hT` is the time-change property of these clocks from every start, for almost every field.

| Result | Declaration | File:line |
|---|---|---|
| Green identity from every start, every insertion `α < Q`, `0 < γ < 2`, hyps `hF`, `hT` | `ae_forall_expectedLBMExitTime_eq_green` | `LBMExpectedExitTimeGreenHolder.lean:75` |
| both conjuncts of the LBM clause, hyps `hF`, `hT` | `ae_expectedLBMExitTime_lt_top_and_holder` | `LBMExpectedExitTimeGreenHolder.lean:211` |
| both conjuncts of the LBM clause, hyps `γ² < 2`, `hF` and the one-start event | `ae_expectedLBMExitTime_lt_top_and_holder_of_dyadicIncrementLiminf_pos` | `LBMExpectedExitTimeGreenHolder.lean:241` |
| Green integrals of the approximating measures converge for every smooth domain and pole | `IsWholePlaneGFF.ae_tendsto_green_lintegral_smooth` | `LQGSmoothGreenIntegralConvergence.lean:279` |
| the same with a continuous weight in `[0, 1]` | `IsWholePlaneGFF.ae_tendsto_green_mul_lintegral_smooth` | `LQGSmoothGreenWeightedConvergence.lean:228` |
| summable exit-time increments of weighted approximations from almost every start, every insertion | `ae_ae_lintegral_tsum_exit_weighted_increment_ne_top` | `LQGClockExitWeightedSummability.lean:32` |
| lower bound from every start by the Markov property at a fixed time | `le_expectedLBMExitTime_of_ae_lintegral_tsum_ne_top_of_le` | `LQGClockExitWeightedLowerBound.lean:186` |
| Markov property at a fixed time on an event of the canonical filtration | `setLIntegral_shift_eq` | `LQGClockExitShiftLowerBound.lean:174` |
| comparison of nested domains | `expectedLBMExitTime_le_add_sub_of_subset` | `LQGClockExitDomainComparison.lean:26` |

`ae_expectedLBMExitTime_lt_top_and_holder_of_dyadicIncrementLiminf_pos` has the hypotheses `0 < γ`, `γ² < 2`,
`α < Q`, `Ω : Type`, `IsWholePlaneGFF`, `IsLQGMeasureOfField`, `hF` and the one-start event of
`LBMClauseClocksEveryStart.md` (source: Berestycki, *Diffusion in planar Liouville quantum gravity*, Ann. Inst.
Henri Poincaré Probab. Stat. 51 (2015), arXiv:1301.3356, Theorem 1.2), and the conclusion of the frozen LBM
clause for the family `F`. The time-change property `hT` comes from
`ae_forall_isTimeChangeClock_of_dyadicIncrementLiminf_pos` (`LQGClockEveryStart.lean:371`).

## Route

1. **Upper bound.** By Fatou's lemma along an almost surely convergent subsequence,
   `E_x[τ_O] ≤ liminf_k ∫ 2 G_O(x, y) f_k(y) dy` (`expectedLBMExitTime_le_liminf_clockApprox_green`),
   where `f_k = ε^{γ²/2} e^{γ h_ε}` at `ε = 2^{-k}`. For a smooth bounded domain, `G_O(x, ·)` is continuous
   away from the pole on the whole plane and vanishes on `∂O`; a pole cutoff times it is a continuous test
   with compact support, and the uniform local Green bound near the pole gives the convergence of the Green
   integrals to `∫ 2 G_O(x, y) μ_h(dy)` for every `O` and every pole on one field event.
2. **Discs, away from the insertion point.** Let `D_n = B(0, n + 1)` and `φ_m = greenPoleCutoff 0 2^{-m}`,
   which vanishes on `B(0, 2^{-m})`. On `‖z‖ ≥ 2^{-m}` and at scales `ε ≤ 2^{-m}` the inserted density is
   the density normalized at radius `R`, times `exp (γ (h_R(0) - h_1(0)))` and the bounded weight
   `|z|^{-γ α}`, so the weighted increments `φ_m (f_{k+m+2} - f_{k+m+1})` have the summable unit-horizon
   bounds of the bounded-weight estimate, uniformly over the start and for every insertion `α`. Integrated
   over the starts in `D_n` (Tonelli), for almost every field the exit-time increments of the weighted
   approximations have finite expected sum from Lebesgue almost every start in `D_n`; there the weighted
   approximations converge almost surely and in `L¹`.
3. **Every start.** For `x ∈ D_n` and `s > 0`, on `{s < τ_{D_n}}` the weighted approximations of a path
   dominate those of the path shifted by `s`, and they are dominated by the clock approximations. The law
   of the path after time `s` is a mixture of Brownian laws over the law of the position at time `s`, which
   is absolutely continuous; the Markov property at time `s` gives
   `E_x[τ_{D_n}] ≥ E_x[V^m(b_s); s < τ_{D_n}]` with `V^m(y) = ∫ 2 G_{D_n}(y, z) φ_m(z) μ_h(dz)`. As `s → 0`
   the continuity of `V^m` (the Green clause with the bounded density `φ_m`) gives
   `E_x[τ_{D_n}] ≥ V^m(x)`, and `m → ∞` gives `E_x[τ_{D_n}] ≥ ∫ 2 G_{D_n}(x, z) μ_h(dz)` by dominated
   convergence, since `μ_h({0}) = 0` (small-ball bound `ae_singular_limit_and_approximant_ball_power`).
4. **Every domain.** For `O ⊆ D_n` the exit time from `D_n` splits as `F(τ_O) + (F(τ_{D_n}) - F(τ_O))`;
   Fatou's lemma for the second term gives
   `E_x[τ_{D_n}] ≤ E_x[τ_O] + ∫ 2 (G_{D_n} - G_O)(x, y) μ_h(dy)`, and with the identity for `D_n` this is
   the lower bound for `O`.
5. **Hölder continuity.** On `O`, `E_x[τ_O]` is the real Green potential `∫_O G_O(x, y) 2 μ_h(dy)`, which
   is Hölder continuous on the closure of `O` by `greenPotentialHolderStmt` with the density 2.

## Departures from the cited sources

- The paper cites Berestycki 2015 and Garban–Rhodes–Vargas, *Liouville Brownian motion*, Ann. Probab. 44
  (2016), for the construction of LBM (corrected draft line 525). Its proof of the clause (lines 540-542)
  cites the volume growth Lemma 2.4 and the Campanato embedding (Ponce 2016, Section 16.2), and uses the
  identity `E_x[τ_O] = ∫_O G_O(x, y) μ_h(dy)` without proof. The Lean proof proves the identity, with the
  factor 2 of the normalizations of `greenFunction` and of planar Brownian motion. It does not use a Revuz
  correspondence for positive continuous additive functionals: the identity is proved directly from the
  clock approximations by
  Fatou's lemma (upper bound), uniform integrability of weighted approximations at almost every start,
  the Markov property at a fixed time (lower bound at every start), and the comparison of nested
  domains (every smooth domain).
- The time spent near the insertion point is handled by weights vanishing near it and a monotone limit,
  so no moment bound for the clock near the insertion is needed; the identity holds for every `α < Q`.

## Assembly and what remains

The LBM clause of `GreenPotentialLiouvilleHolderStmt`, both conjuncts, holds with no hypothesis beyond the
antecedents of the frozen statement for `0 < γ`, `γ² < 2`, `α₀ < Q` and `Ω : Type`:
`greenPotentialLiouvilleHolder_lbmClause` (`LBMClauseOneStart.lean:26`), which applies
`ae_expectedLBMExitTime_lt_top_and_holder_of_dyadicIncrementLiminf_pos` (`LBMExpectedExitTimeGreenHolder.lean:241`)
to the one-start event `ae_forall_rat_ae_dyadicIncrementLiminf_pos` (`LQGClockOneStart.lean:521`; Berestycki
2015, Theorem 1.2, proved by the route of `LBMClauseClocksEveryStart.md`). With the
Green clause `greenPotentialHolderStmt_holds`, `greenPotentialLiouvilleHolder_of_sq_lt_two`
(`LBMClauseOneStart.lean:44`) is the conclusion of `GreenPotentialLiouvilleHolderStmt` in that range. The frozen
statement also covers `2 ≤ γ² < 4` (it assumes `γ < 2`) and `Ω : Type*`; both remain open.
