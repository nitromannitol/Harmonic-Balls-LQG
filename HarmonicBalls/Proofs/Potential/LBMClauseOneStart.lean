import HarmonicBalls.Proofs.Potential.LBMExpectedExitTimeGreenHolder
import HarmonicBalls.Proofs.Potential.LQGClockOneStart
import HarmonicBalls.FirstPass.Phase2.GreenPotentialHolderHolds

/-! # The LBM clause of Proposition 2.5 for `γ² < 2`

The LBM clause of `GreenPotentialLiouvilleHolderStmt` (Proposition 2.5, `prop:lbm-exit-time`): for
every family of LQG clocks from every start, for almost every field, the expected exit time of
Liouville Brownian motion from every smooth bounded domain is finite at every start and Hölder
continuous. It holds for `0 < γ`, `γ² < 2`, `α₀ < Q` and `Ω : Type` with no hypothesis beyond the
antecedents of the frozen statement: the one-start event, the hypothesis of
`ae_expectedLBMExitTime_lt_top_and_holder_of_dyadicIncrementLiminf_pos`, is
`ae_forall_rat_ae_dyadicIncrementLiminf_pos`. Together with the Green clause
`greenPotentialHolderStmt_holds`, this gives the conclusion of `GreenPotentialLiouvilleHolderStmt`
in that range. The frozen statement also quantifies over `2 ≤ γ² < 4` and over `Ω : Type*`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- **The LBM clause of Proposition 2.5** for `0 < γ`, `γ² < 2`, `α₀ < Q` and `Ω : Type`: for every
family of LQG clocks from every start, for almost every field, the expected exit times of Liouville
Brownian motion from every smooth bounded domain are finite and Hölder continuous. -/
theorem greenPotentialLiouvilleHolder_lbmClause {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2)
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
  fun F hF => ae_expectedLBMExitTime_lt_top_and_holder_of_dyadicIncrementLiminf_pos hh hγ hγ2 hα
    hμ (ae_forall_rat_ae_dyadicIncrementLiminf_pos ((LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh)
      hγ hγ2 α₀) F hF

/-- **Proposition 2.5 for `γ² < 2` and `Ω : Type`**: the conclusion of
`GreenPotentialLiouvilleHolderStmt`, the LBM clause and the Green clause, for `0 < γ`, `γ² < 2` and
`α₀ < Q`, on every probability space `Ω : Type`. -/
theorem greenPotentialLiouvilleHolder_of_sq_lt_two :
    ∀ γ α₀ : ℝ, 0 < γ → γ ^ 2 < 2 → α₀ < lqgQ γ →
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
  have hγ2' : γ < 2 := by nlinarith
  exact ⟨greenPotentialLiouvilleHolder_lbmClause hγ hγ2 hα hh hμ,
    greenPotentialHolderStmt_holds γ α₀ hγ hγ2' hα Ω P hC hcirc μ hh hμ⟩

end HarmonicBalls
