import HarmonicBalls.Proofs.Sec7.AnnulusMass
import HarmonicBalls.Proofs.Sec7.LatticeApproximation

/-!
# The mass estimate in the Section 7 circle barrier

This combines the uniform ball-volume bound with the deterministic Harnack
cover. The cluster mass estimate and the Harnack exclusion are explicit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6

/-- A connected set of sufficiently small mass is confined by a circle of
Harnack annuli, using uniform lower bounds for ball volumes. -/
theorem closure_subset_ball_of_ball_volume_and_harnack
    (μ : Measure ℂ) {B : Set ℂ} {r ε α T β : ℝ} {z : ℂ}
    (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hsmall : 10 * Real.sqrt ε + ε < r / 32) (hz : dist z 0 < 1 / 2)
    (hB : IsPreconnected B) (hzB : z ∈ B) (hα : 0 < α)
    (hmass : μ B ≤ ENNReal.ofReal T) (hT : T ≤ α * (ε / 8) ^ β)
    (hvol : ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal ((ε / 8) ^ β) ≤ μ (ball x (ε / 8)))
    (P : ℝ → ℂ → Prop)
    (hgood : ∀ w ∈ prevalenceGrid ε, ∃ ρ ∈ Icc ε (Real.sqrt ε), P ρ w)
    (hharnack : ∀ w ∈ prevalenceGrid ε, ∀ ρ ∈ Icc ε (Real.sqrt ε), P ρ w →
      closedBall w ρ ⊆ ball 0 1 \ {z} →
      μ (B ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) →
      B ∩ ball w (ρ / 2) = ∅) :
    closure B ⊆ ball z (r / 2) := by
  apply closure_subset_ball_of_prevalence_grid μ hr hr1 hε hsmall hz hB hzB P hgood
  · intro w _ ρ hρ _ hdomain
    calc
      μ B ≤ ENNReal.ofReal T := hmass
      _ ≤ ENNReal.ofReal (α * (ε / 8) ^ β) := ENNReal.ofReal_le_ofReal hT
      _ = ENNReal.ofReal α * ENNReal.ofReal ((ε / 8) ^ β) := ENNReal.ofReal_mul hα.le
      _ ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) := by
        gcongr
        exact lower_mass_half_annulus_of_ball_volume μ hε hvol hρ.1
          (hdomain.trans sdiff_subset)
  · exact hharnack

end HarmonicBalls
