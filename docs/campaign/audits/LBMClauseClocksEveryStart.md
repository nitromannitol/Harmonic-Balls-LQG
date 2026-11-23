# Proposition 2.5, LBM clause: LQG clocks from every start and finite expected exit times

Proposition 2.5 (`prop:lbm-exit-time`, corrected draft line 530; frozen form
`GreenPotentialLiouvilleHolderStmt`, `HarmonicBalls/Draft/Section2.lean:161`) has a Green clause, proved by
`greenPotentialHolderStmt_holds`, and an LBM clause (`Draft/Section2.lean:165-169`): for every family of
LQG clocks from every start, for almost every field, the expected exit time of Liouville Brownian motion
from every smooth bounded domain is finite and Hölder continuous. This note records what the modules
below prove towards the finiteness part of the LBM clause, with which hypotheses, and what remains.

## What is proved

All files are in `HarmonicBalls/Proofs/Potential/`. The time-change and exit-time theorems below assume
`0 < γ`, `γ² < 2`, `α < Q` and `Ω : Type`; the strict increase and the transfer of divergence
(`LQGClockEveryStart.lean:231`, `:286`) assume none of these. `F ω x` is a family of clocks with
`hF : ∀ᵐ ω ∂P, ∀ x, IsLQGClock planarBrownianMotion γ (fieldCircleAverage α (hcirc ω)) x (F ω x)`.

For the dyadic scales `ε = 2^{-k}` let `I^k_{a,b}(w) = ∫_a^b ε^{γ²/2} e^{γ h_ε(w_v)} dv` for a path `w`
(`dyadicIncrementApprox`) and `G_{a,b} = liminf_k I^k_{a,b}` in `[0, ∞]` (`dyadicIncrementLiminf`), raw
functionals of the path that do not depend on a choice of clock. The **one-start event** is

> for almost every field, `G_{a,b} > 0` almost surely under planar Brownian motion from the origin, for all
> rationals `0 < a < b`.

| Result | Declaration | File:line |
|---|---|---|
| time-change property at the origin from strict increase between rational times at the origin | `ae_ae_isTimeChangeClock_lqgClock_origin` | `LQGClockOriginDivergenceLaw.lean:249` |
| divergence at the origin from positivity at time 1 at the origin | `ae_ae_tendsto_atTop_lqgClock_origin_of_pos` | `LQGClockOriginDivergenceLaw.lean:84` |
| `G_{a,b} ≤ F(t) - F(s)` a.s. for every LQG clock and `s ≤ a < b ≤ t` | `ae_dyadicIncrementLiminf_le_of_isLQGClock` | `LQGClockEveryStart.lean:177` |
| equivalence of the future path laws after a time `a > 0` from any two starts | `planarBrownianMotion_map_shift_absolutelyContinuous` | `LQGClockEveryStart.lean:190` |
| strict increase between rational times from every start (any `γ`) | `ae_forall_rat_lt_of_dyadicIncrementLiminf_pos` | `LQGClockEveryStart.lean:231` |
| divergence from every start, from divergence at the origin | `ae_forall_tendsto_atTop_of_origin` | `LQGClockEveryStart.lean:286` |
| time-change property from every start | `ae_forall_isTimeChangeClock_of_dyadicIncrementLiminf_pos` | `LQGClockEveryStart.lean:371` |
| finite expected exit times from every start in every smooth bounded domain | `ae_forall_expectedLBMExitTime_lt_top_of_dyadicIncrementLiminf_pos` | `LQGClockEveryStart.lean:401` |

The last theorem has the hypotheses `0 < γ`, `γ² < 2`, `α < Q`, `IsWholePlaneGFF`, `IsLQGMeasureOfField`,
`hF` and the one-start event, and the conclusion
`∀ᵐ ω ∂P, ∀ O, IsSmoothBoundedOpen O → ∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤`, the finiteness
conjunct of the frozen LBM clause. It consumes `ae_forall_expectedLBMExitTime_lt_top_of_strictly_increasing`
(`LQGClockTimeChangeReduction.lean:234`).

The supporting modules are `LQGClockScalingDivergence.lean` and
`LQGClockOriginDivergence.lean` (the divergence deduction from a scaling factorization),
`LQGClockScalingPrefactor.lean` (Brownian scaling of the clocks, `F(4^m t) = c_m F'(b̃)(t)`, and
`c_m → ∞`), `LQGClockMeasurableVersion.lean` (jointly measurable limits in probability; limits of
identically distributed sequences are identically distributed) and `LQGClockApproxPathDecoder.lean`
(measurable reconstruction of the approximating clocks from the circle averages). In total 40 theorems and
3 definitions, all new; no existing statement or frozen declaration is changed. The module
`LQGClockZeroOneStrictIncrease.lean` (strict increase at a fixed start from a zero-one law and positive
mean increments, after Garban–Rhodes–Vargas Theorem 2.7 (3) and Lemma 2.8) is not on this route: no module
of the route imports it, and strict increase comes from the one-start event instead.

## Route and sources

1. **Divergence at the origin.** Bertacco–Gwynne, *Liouville Brownian motion and quantum cones in dimension
   d > 2*, arXiv:2501.15936v2, Theorem 5.12 (B4), in the plane: the field rescaled by `2^m` is again a
   whole-plane GFF (affine invariance), the rescaled path is again a Brownian motion from the origin, the
   clock factors as `F(4^m) = c_m Y_m` with `c_m = 2^{m(2 + γ²/2 - γα)} e^{γ h^ℂ_{2^m}(0)}`, where
   `h^ℂ_{2^m}(0)` is the circle average of the whole-plane GFF (not of the inserted field), so that
   `c_m → ∞` almost surely; the `Y_m` are identically distributed under the joint law and almost surely
   positive, so `F` is unbounded along the times `4^m`. Deterministic times `4^m` replace the exit times
   of the balls `B(0, 2^m)`.
2. **Every start.** For `a > 0` the Markov property at time `a` writes the law of the path after time `a`
   as the mixture of Brownian laws over the planar Gaussian transition law at time `a`, and these transition
   laws are equivalent for any two starts. Hence a future event of full probability from the origin has full
   probability from every start. This is applied to the positivity event `{G_{a,b} > 0}` (strict increase)
   and to the event that the lower limits of the approximants over `[1, N + 1]`, along subsequences chosen
   at the origin, are unbounded in `N` (divergence).

## Departures from the cited sources

- Divergence uses Bertacco–Gwynne Theorem 5.12 (B4) in place of Garban–Rhodes–Vargas, *Liouville Brownian
  motion*, Ann. Probab. 44 (2016), Theorem 2.7 (4), whose proof uses the exponential decay of the
  correlations of the massive free field; the field here is the massless whole-plane GFF.
- The passage from one start to every start uses the fixed-time Markov transfer above in place of the
  coupling of Garban–Rhodes–Vargas Lemma 2.9 and Bertacco–Gwynne Lemma 5.13.

## The one-start event

The one-start event is proved for `0 < γ`, `γ² < 2` and every insertion `α` (no condition `α < Q`), for
`IsWholePlaneGFF` on any `Ω : Type*`:

| Result | Declaration | File |
|---|---|---|
| zero-one law for events of a centred Gaussian process invariant under its Cameron–Martin shifts | `measure_preimage_eq_zero_or_one_of_shift_invariant` | `CameronMartinZeroOne.lean` |
| along every fixed path, `P(G_{a,b} > 0) ∈ {0, 1}` | `measure_dyadicIncrementLiminf_pos_eq_zero_or_one` | `LQGClockProfileZeroOne.lean` |
| `E[J_k] ≥ b - a`; `E[J_k²] ≤ (N+1)^{4γ²} 2^{γ²} ∫∫ |w_s - w_t|^{-γ²}` along a path bounded by `N` | `le_lintegral_profileIncrement`, `lintegral_profileIncrement_sq_le` | `LQGClockIncrementMoments.lean` |
| almost sure convergence of the increment approximants from `x ≠ 0` under the joint law | `ae_prod_tendsto_dyadicIncrementApprox_of_ne_zero` | `LQGClockOneStart.lean` |
| positivity from `x ≠ 0`, then from the origin | `ae_ae_dyadicIncrementLiminf_pos_of_ne_zero`, `ae_ae_dyadicIncrementLiminf_pos_origin` | `LQGClockOneStart.lean` |
| the one-start event | `ae_forall_rat_ae_dyadicIncrementLiminf_pos` | `LQGClockOneStart.lean` |
| strict increase, time-change property and finite expected exit times from every start, without the one-start hypothesis | `ae_forall_rat_lt_of_isLQGClock`, `ae_forall_isTimeChangeClock_of_isLQGClock`, `ae_forall_expectedLBMExitTime_lt_top_of_isLQGClock` | `LQGClockOneStart.lean` |

Here `J_k = ∫_a^b ε^{γ²/2} e^{γ h_ε(w_v)} dv` with `ε = 2^{-k}`, read through a functional of the dyadic
circle-average profile that is measurable for the product σ-algebra (`profileIncrementLiminf`).

Route. Source: Berestycki, *Diffusion in planar Liouville quantum gravity*, Ann. Inst. Henri Poincaré
Probab. Stat. 51 (2015), arXiv:1301.3356, Theorem 1.2: almost sure dyadic convergence (Section 2) and
nondegeneracy (Section 3) of the clock. Section 2 is used through the convergence of the half-disc and
exterior clocks already proved for starts `x ≠ 0`. Nondegeneracy is proved as follows.

1. For a fixed path `w`, adding to the field a Cameron–Martin shift `Cov(h_·, X)`, with `X` a finite
   combination of circle averages, multiplies `J_k` by a factor in `[e^{-|γ| M}, e^{|γ| M}]`, since the
   shift is bounded uniformly in the scale on the bounded path range. The event `{G_{a,b}(w) > 0}` is
   therefore invariant, and has probability `0` or `1` by the zero-one law for Cameron–Martin invariant
   events (Bogachev, *Gaussian measures*, AMS 1998, Section 2.5), proved from the Cameron–Martin formula
   (`QuantumZipper.CameronMartin.map_tiltMeasure_path`, Lattice-Probability) and moment generating
   functions.
2. If the paths with probability `0` had positive probability from `x ≠ 0`, the approximants restricted
   to them (and to paths bounded by `N` on `[a, b]`) would tend to `0` almost surely under the joint law,
   stay bounded in `L²` (`E_x ∫∫ |B_s - B_t|^{-γ²} < ∞` for `γ² < 2`), and have means at least `b - a`
   times the probability of the restriction (`Var h_ε(z) ≥ log (1/ε)`): impossible.
3. The insertion multiplies the approximants by `e^{-γ α log max(ε, |B_v|)}`, bounded below on `[a, b]`
   since Brownian motion from `x ≠ 0` never visits `0`. The origin is reached by the fixed-time Markov
   transfer from the start `1`.

## Departures from the cited sources (one-start event)

- Berestycki's Section 3 proves an `L^q` bound (`q > 1`, all `γ < 2`) with Kahane's convexity inequality
  and an exactly scale-invariant field, and then probability one by a second-moment count of small squares
  where the clock charges, using the domain Markov property (with Gwynne–Miller, *Local metrics of the
  Gaussian free field*, Ann. Inst. Fourier 70 (2020), Lemma 2.1, for the whole-plane field). Here the
  `L²` bound replaces the `L^q` bound (valid exactly for `γ² < 2`, the range of the theorems above), and
  the Cameron–Martin zero-one law along a fixed path replaces the second-moment count; no domain Markov
  property is used. In the printed count the events attached to different squares depend on the same
  Brownian path and are independent only conditionally on it, while the lower bound on their expected
  number is annealed.
- The field is the circle-normalized whole-plane GFF itself, with the dyadic circle averages as the
  regularization, not a Dirichlet GFF.

## The Hölder conjunct and the assembled clause

The Hölder conjunct of the LBM clause is proved, with the same hypotheses, through the Green identity
`E_x[τ_O] = ∫_O 2 G_O(x, y) μ_h(dy)` from every start; see `LBMClauseGreenIdentityHolder.md`.

The LBM clause of `GreenPotentialLiouvilleHolderStmt`, both conjuncts, holds with no hypothesis beyond the
antecedents of the frozen statement for `0 < γ`, `γ² < 2`, `α₀ < Q` and `Ω : Type`:
`greenPotentialLiouvilleHolder_lbmClause` (`LBMClauseOneStart.lean:26`), which applies
`ae_expectedLBMExitTime_lt_top_and_holder_of_dyadicIncrementLiminf_pos` (`LBMExpectedExitTimeGreenHolder.lean:241`)
to the one-start event `ae_forall_rat_ae_dyadicIncrementLiminf_pos` (`LQGClockOneStart.lean:521`). With the
Green clause `greenPotentialHolderStmt_holds`, `greenPotentialLiouvilleHolder_of_sq_lt_two`
(`LBMClauseOneStart.lean:44`) is the conclusion of `GreenPotentialLiouvilleHolderStmt` in that range. The frozen
statement also covers `2 ≤ γ² < 4` (it assumes `γ < 2`) and `Ω : Type*`; both remain open.
