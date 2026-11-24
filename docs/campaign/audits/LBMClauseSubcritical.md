# Proposition 2.5, LBM clause, for every 0 < γ < 2

Proposition 2.5 (`prop:lbm-exit-time`, corrected draft line 530; frozen form
`GreenPotentialLiouvilleHolderStmt`, `HarmonicBalls/Draft/Section2.lean:161`) quantifies over `0 < γ < 2`.
`LBMClauseOneStart.lean` proves its conclusion for `γ² < 2` and `Ω : Type`. This note records the proof of
the LBM clause, and hence of the conclusion of the frozen statement, for every `0 < γ < 2`, with no
hypothesis beyond the antecedents of the frozen statement, on a probability space in any universe: the
frozen statement itself is proved (`greenPotentialLiouvilleHolderStmt_holds`).

## What is proved

All files are in `HarmonicBalls/Proofs/Potential/`. `F ω x` is a family of clocks with
`hF : ∀ᵐ ω ∂P, ∀ x, IsLQGClock planarBrownianMotion γ (fieldCircleAverage α (hcirc ω)) x (F ω x)`, and
`I^k_{a,b}`, `G_{a,b}` are the dyadic approximants and their lower limit (`dyadicIncrementApprox`,
`dyadicIncrementLiminf`, see `LBMClauseClocksEveryStart.md`).

| Result | Declaration | File:line |
|---|---|---|
| `L¹` bound of the thick-point truncation for the recentred increments along a bounded path, with its occupation measure as reference measure | `lintegral_ofReal_abs_integral_increment_le`, `lintegral_ofReal_abs_integral_dyadicIncrement_le_exp` | `LQGClockIncrementL1Rate.lean:92`, `:237` |
| pairs of points of the occupation measure at distance `< δ` have mass `≤ δ^β ∫∫ |w_s - w_t|^{-β}` | `pathOccupation_prod_lt_le` | `LQGClockIncrementL1Rate.lean:62` |
| `E_x ∫∫_{(a,b]²} |B_s - B_t|^{-β} < ∞` for `0 < β < 2` | `lintegral_planarBrownianMotion_Ioc_pair_lt_top` | `LQGClockIncrementL1Rate.lean:305` |
| `E[e^{-γ h_R(0)} ε^{γ²/2} e^{γ h_ε(z)}] = R^{γ²/2}` for `‖z‖ + ε ≤ R` | `lintegral_ofReal_recentred_dyadicDensity` | `LQGClockOneStartSubcritical.lean:71` |
| positivity of `G_{a,b}` without insertion from every start, `0 < γ < 2` | `ae_ae_dyadicIncrementLiminf_pos_zero_of_lt_two` | `LQGClockOneStartSubcritical.lean:104` |
| with every insertion from `x ≠ 0`, then from the origin | `ae_ae_dyadicIncrementLiminf_pos_of_ne_zero_of_lt_two`, `ae_ae_dyadicIncrementLiminf_pos_origin_of_lt_two` | `LQGClockOneStartSubcritical.lean:468`, `:484` |
| the one-start event for `0 < γ < 2` | `ae_forall_rat_ae_dyadicIncrementLiminf_pos_of_lt_two` | `LQGClockOneStartSubcritical.lean:520` |
| strict increase between rational times from every start | `ae_forall_rat_lt_of_isLQGClock_of_lt_two` | `LQGClockOneStartSubcritical.lean:539` |
| scaling of the dyadic lower limits, `G_{0,1}(h^{(m)}, b̃_m) = c_m⁻¹ G_{0,4^m}(h, b)` | `dyadicIncrementLiminf_rescaled_eq` | `LQGClockOriginDivergenceScaling.lean:35` |
| divergence of the clock from the origin from `G_{0,1} > 0`, any `γ > 0`, `α < Q` | `ae_ae_tendsto_atTop_lqgClock_origin_of_dyadicIncrementLiminf_pos` | `LQGClockOriginDivergenceScaling.lean:72` |
| time-change property from every start, `0 < γ < 2`, `α < Q` | `ae_forall_isTimeChangeClock_of_isLQGClock_of_lt_two` | `LBMClauseSubcritical.lean:37` |
| the LBM clause, both conjuncts, `0 < γ < 2`, `α₀ < Q` | `greenPotentialLiouvilleHolder_lbmClause_of_lt_two` | `LBMClauseSubcritical.lean:59` |
| the conclusion of `GreenPotentialLiouvilleHolderStmt` for `0 < γ < 2` | `greenPotentialLiouvilleHolder_of_lt_two` | `LBMClauseSubcritical.lean:76` |
| the frozen statement, `GreenPotentialLiouvilleHolderStmt.{u}` for every universe `u` | `greenPotentialLiouvilleHolderStmt_holds` | `LBMClauseSubcritical.lean:100` |
| its case `u = 0` | `greenPotentialLiouvilleHolderStmt_zero` | `LBMClauseSubcritical.lean:105` |

`greenPotentialLiouvilleHolder_of_lt_two` has exactly the type of the frozen statement, and the kernel checks
this: `greenPotentialLiouvilleHolderStmt_holds` is that theorem at the type
`GreenPotentialLiouvilleHolderStmt.{u}`. The
LBM clause is obtained from `ae_expectedLBMExitTime_lt_top_and_holder` (`LBMExpectedExitTimeGreenHolder.lean`,
`0 < γ < 2`, `hF` and the time-change property), and the Green clause is `greenPotentialHolderStmt_holds`.
No frozen declaration is changed.

## Every universe

The proof first gave the conclusion for `Ω : Type` only. Nothing in it needs `Type`: the restriction came
from declarations stated for `Ω : Type` whose proofs use only universe-polymorphic results. They are
generalized in place, with unchanged proofs, to a probability space in any universe:

- in Lattice-Probability, the dyadic circle-average bounds for a normalized whole-plane field,
  `LatticeProb.LQG.ae_exists_all_dyadic_circle_le_of_normalized_gff` and
  `ae_eventually_dyadic_circle_sup_le_of_normalized_gff`, and the circle-average model inputs of
  `MatedCRTHarmonic.GMCUpper` they rest on (`CircleAverageSupBoundModel`, `exists_circleAvgVersion_normalized`,
  `circleAverageSupBound_of_model`, `isGFFCircleAverage_of_version`, `circleAverage_square_tail`,
  `circleAverage_square_tail_neg`, `circleAverageSupBoundModel_holds` and a private lemma; copied from Leonardo
  Bonanno's lean-formalizations, where they are stated for `Type`); the Lattice-Probability pin moves to that
  revision;
- in this repository, 40 declarations in 18 files of `HarmonicBalls/Proofs/Potential/`: the Green identity
  for the expected exit times (`ae_forall_expectedLBMExitTime_eq_green`,
  `ae_expectedLBMExitTime_lt_top_and_holder`), the three convergence and ball-power facts for the field and
  its LQG measure behind it (`ae_tendsto_green_lintegral_smooth`, `ae_tendsto_green_mul_lintegral_smooth`,
  `ae_singular_limit_and_approximant_ball_power`), the circle-average, smoothing and approximant bounds
  they rest on (`LQGCompactCircleBound`, `LQGCompactRadialOscillation`, `LQGCircleRadialGridTail`,
  `LQGFineScaleHalfMesh`, `LQGCoarseSmoothingBallPower`, `LQGSingularContinuumBallPower`, `LQGUniformGreenTail`,
  `LQGActualApproximantPower`, `LQGActualLimitBallPower`, `LQGApprox*`, `LQGSmoothGreen*`), and the two
  theorems of `LBMClauseSubcritical.lean` above.

## Route and sources

1. **`L¹` rate.** Berestycki, *Diffusion in planar Liouville quantum gravity*, Ann. Inst. Henri Poincaré
   Probab. Stat. 51 (2015), arXiv:1301.3356, Section 2, proves the almost sure convergence of the clock
   approximants along `ε = 2^{-k}` for every `γ < 2` by truncating at thick points (the case `γ ≥ √2`).
   Here the truncation is the `L¹` bound for a general reference measure proved in Lattice-Probability
   (`LatticeProb.Gauss.IsWholePlaneGFF.integral_abs_integral_increment_le`, after Duplantier–Sheffield,
   *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Section 3): for `γ ≤ α ≤ 2γ`,
   `E |∫ g Δ_ε dν| ≤ ε^{γ²/2} ((B I_ε / τ + τ)/2 + 2 (∫ |g| dν) e^{L (γ²/2 - (α - γ)²/2)})` with
   `I_ε = ∫∫_{|z - z'| < 2ε} |g| |g| dν dν`. It is applied with `ν` the occupation measure of the path on
   `(a, b]` and `g = 1` on a disc containing the path, so that `I_ε ≤ (2ε)^β ∫∫ |w_s - w_t|^{-β}`, whose
   expectation under Brownian motion is finite for `β < 2`. With `α = 2γ` for `γ < 1`, `α = 2` for `γ ≥ 1`,
   `b = 2 - γ² + (2γ - α)²/2 > 0` and `β = 2 - b/2`, the expected increments are at most a constant times
   `ε^{b/4} + ε^{(α-γ)²/2}`, summable over the dyadic scales.
2. **Nondegeneracy.** As in `LBMClauseClocksEveryStart.md` (the Cameron–Martin zero-one law along a fixed
   path, then a contradiction on a set `E` of paths of positive probability along which positivity has
   probability `0`), with the `L²` bound replaced by the `L¹` rate: on `E`, with `R = N + 1`, the recentred
   approximants `1_E e^{-γ h_R(0)} I^k_{a,b}` have summable `L¹` increments under the joint law of the
   field and the path, so they converge almost surely and in `L¹` (`LatticeProb.SummableIncrements`); the
   almost sure limit vanishes on `E`, while the means equal `(b - a) R^{γ²/2} P_x(E) > 0`.
3. **Divergence.** Bertacco–Gwynne, arXiv:2501.15936v2, Theorem 5.12 (B4), as in
   `LBMClauseClocksEveryStart.md`, with the clocks of the rescaled fields replaced by the dyadic lower
   limits `Y_m = G_{0,1}(h^{(m)}, b̃_m)`: they are measurable functionals of the circle averages of the
   rescaled field and of the rescaled path, hence identically distributed; Brownian scaling of the
   approximants only shifts the dyadic index, so `c_m Y_m = G_{0,4^m}(h, b) ≤ F(4^m)`.

## Departures from the cited sources

- Berestycki's Section 2 bounds the quenched second moment of the truncated increments, given the path, by
  the occupation estimate of Dembo–Peres–Rosen–Zeitouni (*Thick points for planar Brownian motion and the
  Erdős–Taylor conjecture on random walk*, Acta Math. 186 (2001), Theorem 1.2). Here the increments are
  bounded in `L¹` under the joint law, and only the expected Brownian interval energy is used.
- Berestycki's Section 3 (nondegeneracy by an `L^q` bound from Kahane's convexity inequality and a
  second-moment count) is replaced as recorded in `LBMClauseClocksEveryStart.md`; no `L^q` bound, Kahane
  inequality or exactly scale-invariant field is used.
- Divergence uses no clock other than the given one: the rescaled clocks of Bertacco–Gwynne are replaced by
  lower limits of approximants.
