import HarmonicBalls.Proofs.Potential.LQGClockOriginDivergenceScaling
import HarmonicBalls.Proofs.Potential.LBMClauseOneStart

/-! # The LBM clause of Proposition 2.5 for `0 < γ < 2`

The LBM clause of `GreenPotentialLiouvilleHolderStmt` (Proposition 2.5, `prop:lbm-exit-time`): for
every family of LQG clocks from every start, for almost every field, the expected exit time of
Liouville Brownian motion from every smooth bounded domain is finite at every start and Hölder
continuous. It holds for `0 < γ < 2`, `α₀ < Q` and `Ω : Type` with no hypothesis beyond the
antecedents of the frozen statement.

* The clocks are time-change clocks from every start (`ae_forall_isTimeChangeClock_of_isLQGClock_of_lt_two`):
  strict increase from the one-start event `ae_forall_rat_ae_dyadicIncrementLiminf_pos_of_lt_two`
  and the transfer to every start (`ae_forall_rat_lt_of_dyadicIncrementLiminf_pos`); divergence
  from the origin by Brownian scaling of the dyadic lower limits
  (`ae_ae_tendsto_atTop_lqgClock_origin_of_dyadicIncrementLiminf_pos`) and from every start by
  the fixed-time Markov transfer (`ae_forall_tendsto_atTop_of_origin`).
* The expected exit times are the Green potentials `∫_O 2 G_O(x, y) μ_h(dy)`, finite and Hölder
  continuous (`ae_expectedLBMExitTime_lt_top_and_holder`).

With the Green clause `greenPotentialHolderStmt_holds`, this gives the conclusion of
`GreenPotentialLiouvilleHolderStmt` for every `0 < γ < 2` on every probability space `Ω : Type`
(`greenPotentialLiouvilleHolder_of_lt_two`). The frozen statement quantifies over `Ω : Type*`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- **The time-change property from every start for `0 < γ < 2`**: for every family of LQG clocks
of the inserted field from every start (`α < Q`), for almost every field, from every start, the
clock is almost surely a time-change clock. -/
theorem ae_forall_isTimeChangeClock_of_isLQGClock_of_lt_two {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω x)) :
    ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ w ∂(planarBrownianMotion x), IsTimeChangeClock (F ω x w) := by
  have hpos := ae_forall_rat_lt_of_isLQGClock_of_lt_two hh hγ hγ2 F hF
  have hF0 : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 (F ω 0) := by
    filter_upwards [hF] with ω hω
    exact hω 0
  have hdiv0 := ae_ae_tendsto_atTop_lqgClock_origin_of_dyadicIncrementLiminf_pos hh hγ hα
    (fun ω => F ω 0) hF0 (ae_ae_dyadicIncrementLiminf_zero_one_pos_of_lt_two hh hγ hγ2 α)
  filter_upwards [hF, hpos, ae_forall_tendsto_atTop_of_origin hh F hF hdiv0,
    ae_continuous_fieldCircleAverage hh α] with ω hFω hpω hdω hcω x
  exact ae_isTimeChangeClock_of_isLQGClock (fun k => hcω _ (dyadicScale_pos k)) (hFω x)
    (hpω x) (hdω x)

/-- **The LBM clause of Proposition 2.5** for `0 < γ < 2`, `α₀ < Q` and `Ω : Type`: for every
family of LQG clocks from every start, for almost every field, the expected exit times of Liouville
Brownian motion from every smooth bounded domain are finite and Hölder continuous. -/
theorem greenPotentialLiouvilleHolder_lbmClause_of_lt_two {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ,
      (∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
        (fieldCircleAverage α₀ (hcirc ω)) x (F ω x)) →
      ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
        (∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤) ∧
          ∃ C r : ℝ≥0, 0 < r ∧
            HolderOnWith C r (fun x => (expectedLBMExitTime (F ω x) O x).toReal) O :=
  fun F hF => ae_expectedLBMExitTime_lt_top_and_holder hh hγ hγ2 hα hμ F hF
    (ae_forall_isTimeChangeClock_of_isLQGClock_of_lt_two
      ((LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh) hγ hγ2 hα F hF)

/-- **Proposition 2.5 for `0 < γ < 2` and `Ω : Type`**: the conclusion of
`GreenPotentialLiouvilleHolderStmt`, the LBM clause and the Green clause, for `0 < γ < 2` and
`α₀ < Q`, on every probability space `Ω : Type`. -/
theorem greenPotentialLiouvilleHolder_of_lt_two :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
      IsLQGMeasureOfField P γ α₀ hcirc μ →
    (∀ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ,
      (∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
        (fieldCircleAverage α₀ (hcirc ω)) x (F ω x)) →
      ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
        (∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤) ∧
          ∃ C r : ℝ≥0, 0 < r ∧
            HolderOnWith C r (fun x => (expectedLBMExitTime (F ω x) O x).toReal) O) ∧
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
      ∀ f : ℂ → ℝ, MemLp f ⊤ ((μ ω).restrict (closure O)) →
        (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O (μ ω)) ∧
        ∃ C r : ℝ≥0, 0 < r ∧
          HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y * f y ∂(μ ω)) (closure O) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hh hμ
  exact ⟨greenPotentialLiouvilleHolder_lbmClause_of_lt_two hγ hγ2 hα hh hμ,
    greenPotentialHolderStmt_holds γ α₀ hγ hγ2 hα Ω P hC hcirc μ hh hμ⟩

end HarmonicBalls
