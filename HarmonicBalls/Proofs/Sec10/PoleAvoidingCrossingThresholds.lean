import HarmonicBalls.Proofs.Sec10.PoleAvoidingMassThresholds
import HarmonicBalls.Proofs.Sec10.StrictMassCrossings

/-! # Crossing bounds from pole-avoiding annulus decay -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

/-- Uniform mass thresholds give the sharp crossing count at a displaced good
ball, assuming the one-good-annulus decay for every pole-avoiding component. -/
theorem exists_pole_avoiding_crossing_thresholds
    {β C₃ : ℝ} (hβ0 : 0 < β) (hC₃ : 0 < C₃) :
    ∃ b ∈ Ioo (0 : ℝ) 1, ∃ N₁ : ℝ → ℝ → ℝ → ℕ, ∃ α : ℝ → ℕ → ℝ → ℝ,
      (∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
        200 ≤ N₁ a C₁m C₂p ∧ ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ → α a N₀ C₁m ∈ Ioo (0 : ℝ) 1) ∧
      ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ → ∀ {βplus : ℝ}, VolumeGrowth μ 1 β βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {ρ : ℝ}, 0 < ρ → ∀ {x₀ : ℂ}, closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 →
      ∀ {w : ℂ}, dist w x₀ < ρ / 6 → μ (annulus x₀ (ρ / 2) ρ) ≠ ∞ →
      ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
      ∀ N₀ : ℕ, N₁ a C₁m C₂p ≤ N₀ →
      annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
      annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) →
      VeryGoodCriterionThree μ ρ x₀ N₀ a b C₃ →
      (∀ Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball x₀ ρ), z ∉ Λ →
        ∀ r : ℝ, 0 < r → ∀ v : ℂ, closedBall v (5 * r) ⊆ ball x₀ ρ →
        IsGoodAnnulus μ r v a b →
        μ (Λ ∩ annulus v (3 * r) (5 * r)) ≤ ENNReal.ofReal a * μ (annulus v (3 * r) (5 * r)) →
        (⨆ x ∈ Λ ∩ ball v (4 * r), odometerExt μ z t x) ≤
          ENNReal.ofReal b * ⨆ x ∈ Λ ∩ annulus v (3 * r) (5 * r), odometerExt μ z t x) →
      (crossingComponents (cluster μ 1 z t ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤
        ⌈1 / α a N₀ C₁m⌉₊ := by
  obtain ⟨b, hb, N₁, α, hparam, hmass⟩ := exists_pole_avoiding_mass_avoidance_thresholds hβ0 hC₃
  refine ⟨b, hb, N₁, α, hparam, ?_⟩
  intro μ hμ βplus hV z hz t ht ρ hρ x₀ hx₀ w hw hfin a ha C₁m C₁p C₂m C₂p hC₁ hC₂ N₀ hN₀ hmassratio hgreen hgood hdec
  have hopen := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ zero_lt_one hV hz ht).1
  have hα := (hparam a ha C₁m C₂p hC₁ hC₂).2 N₀ hN₀
  apply encard_crossingComponents_of_nearby_harnack_away_from_pole_sharp
    μ (cluster μ 1 z t) hopen hα.1 w x₀ z hρ hw hfin
  intro Λ hΛ hzΛ hsmall
  exact hmass hμ hV hz ht hρ hx₀ hΛ hzΛ a ha C₁m C₁p C₂m C₂p hC₁ hC₂ N₀ hN₀
    hmassratio hgreen hsmall hgood (hdec Λ hΛ hzΛ)

end HarmonicBalls
