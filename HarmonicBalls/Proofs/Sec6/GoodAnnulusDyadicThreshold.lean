import HarmonicBalls.Proofs.Sec6.DiscDyadicRecurrence
import HarmonicBalls.Proofs.Sec6.GoodPrevalenceBall

/-! # Good-annulus thresholds from dyadic recurrence

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped ENNReal

universe u

/-- Dyadic disc fine support and the ball-submean estimate give a positive
threshold for the unit good-annulus event. -/
theorem ae_unit_goodAnnulus_threshold_of_disc_dyadic
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ v ∈ sphere (0 : ℂ) (4 * 1),
      planarBrownianMotion v
        {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
          ContinuousPath.exitTime Kᶜ path} ≤
      C * ∫⁻ x in ball v (1 / 4 : ℝ), planarBrownianMotion x
        {path | ContinuousPath.exitTime (annulus 0 (3 * 1) (5 * 1)) path ≤
          ContinuousPath.exitTime Kᶜ path} ∂volume)
    {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b := by
  let := h.isProbabilityMeasure
  apply ae_exists_goodAnnulus_threshold_of_ae_local_fine_support μ
    (z := 0) (r := 1) (by norm_num) hb ?_ ?_ hC0 hCtop hsubmean
  · filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  · exact ae_ae_lqg_fine_support_of_disc_dyadic hgrowth hγ hγ2 h hμ hAff

/-- Volume growth and affine field invariance give an almost sure positive
threshold for the unit good-annulus event. -/
theorem ae_unit_goodAnnulus_threshold_of_volumeGrowth_dyadic
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) 1 0 a b := by
  obtain ⟨C, hC0, hCtop, hsubmean⟩ := unit_goodAnnulus_avoidance_ball_submean
  exact ae_unit_goodAnnulus_threshold_of_disc_dyadic hgrowth hγ hγ2 h hμ hAff
    hC0 hCtop hsubmean hb

end HarmonicBalls.Section6
