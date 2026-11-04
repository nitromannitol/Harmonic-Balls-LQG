import HarmonicBalls.Proofs.Sec8.RandomGoodAnnulus
import HarmonicBalls.Proofs.Sec8.LQGAnnulusComparison
import HarmonicBalls.Proofs.Sec8.LQGUniversalMeasureLaw

/-! # Measurable good-annulus representatives for LQG measures -/

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

universe u

open MarkovProcess in
/-- Under point avoidance, an LQG good-annulus event has a measurable version
when its mass threshold is positive. Nonatomicity is an explicit staged input. -/
theorem exists_measurable_lqg_isGoodAnnulus_of_ae_point_avoidance
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ) (ha : 0 < a)
    (hpolar : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsGoodAnnulus (μ ω) r z a b) := by
  have hnonempty : (annulus z (3 * r) (5 * r)).Nonempty := by
    refine ⟨z + (((4 * r : ℝ) : ℂ)), ?_⟩
    have hd : dist (z + (((4 * r : ℝ) : ℂ))) z = 4 * r := by
      simp [dist_eq_norm, hr.le]
    change dist (z + (((4 * r : ℝ) : ℂ))) z < 5 * r ∧
      ¬ dist (z + (((4 * r : ℝ) : ℂ))) z ≤ 3 * r
    rw [hd]
    constructor <;> linarith
  have hmass : ∀ᵐ ω ∂P, μ ω (annulus z (3 * r) (5 * r)) ≠ ∞ ∧
      0 < ENNReal.ofReal a * μ ω (annulus z (3 * r) (5 * r)) := by
    filter_upwards [hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hμ] with ω hωfull hωloc
    let : IsLocallyFiniteMeasure (μ ω) := hωloc.isLocallyFiniteMeasure
    have hpos := hωfull _ (isOpen_ball.sdiff isClosed_closedBall) hnonempty
    have hfinite : μ ω (annulus z (3 * r) (5 * r)) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_ne_top (measure_mono Set.sdiff_subset)
    exact ⟨hfinite, ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha).ne' hpos.ne'⟩
  apply exists_measurable_random_isGoodAnnulus_of_ae_point_avoidance P μ
    (hGFF.aemeasurable_lqgMeasure hμ) r hr z a b
    (hatom hGFF hγ hγ2 hα μ hμ) ?_ ?_ hpolar
  · filter_upwards [hmass] with ω hω
    exact hω.1
  · filter_upwards [hmass] with ω hω
    exact hω.2

end HarmonicBalls
