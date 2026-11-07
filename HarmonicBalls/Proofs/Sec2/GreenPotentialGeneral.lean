import HarmonicBalls.Steps.Sec2.GreenPotentialGeneral

/-! # Proposition 2.5: deterministic reduction

The Green clause follows from the all-scales volume-growth statement and the
unproved general-domain deterministic estimate `GreenPotentialGeneralStep`.
The event is chosen before quantifying over domains and densities.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- The Green clause of Proposition 2.5, conditional on the deterministic
  general-domain estimate and the all-scales volume-growth statement. -/
theorem greenPotentialHolderStmt_of_volumeGrowth
    (hstep : GreenPotentialGeneralStep) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) :
    GreenPotentialHolderStmt.{u} := by
  intro γ α hγ hγ2 hα Ω _ P hC hcirc μ hGFF hLQG
  have hb : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α)) :=
    lt_min (div_pos (sq_pos_of_pos (sub_pos.mpr hγ2)) (by norm_num))
      (mul_pos hγ (sub_pos.mpr hα))
  filter_upwards [hgrowth γ α hγ hγ2 hα Ω P hC hcirc μ hGFF hLQG, hLQG] with ω hvol hlim
  apply hstep (μ ω) hlim.isLocallyFiniteMeasure
  intro R hR
  let b := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α))
  let B := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α))
  have hB : 0 < B := lt_of_lt_of_le (mul_pos hγ (sub_pos.mpr hα)) (le_max_right _ _)
  obtain ⟨r₀, hr₀, hr⟩ := hvol R hR (b / 2) (B + 1) (by dsimp [b]; linarith)
    (by dsimp [b]; linarith) (by dsimp [B]; linarith)
  exact ⟨B + 1, b / 2, by linarith, by dsimp [b]; linarith, r₀, hr₀, hr⟩

#print axioms greenPotentialHolderStmt_of_volumeGrowth

end HarmonicBalls
