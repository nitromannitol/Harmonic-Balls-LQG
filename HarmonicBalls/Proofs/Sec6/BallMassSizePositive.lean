import HarmonicBalls.Defs.Annuli
import HarmonicBalls.Defs.Obstacle

/-! # Positivity of the annular ball-mass size -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- The lower volume-growth bound on a ball containing the annulus gives a
positive lower bound for its ball-mass size. -/
theorem annulusBallMassSize_pos_of_volumeGrowth
    {μ : Measure ℂ} {ρ β βplus : ℝ} (hρ : 0 < ρ)
    (hV : VolumeGrowth μ (2 * ρ) β βplus) :
    0 < annulusBallMassSize μ β ρ 0 := by
  obtain ⟨hβ, _, r₀, hr₀, hbound⟩ := hV
  let δ : ℝ := min (r₀ / 2) (ρ / 8)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr₀ : δ < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let c : ℝ := min (ρ ^ β) (δ ^ β)
  have hc : 0 < c := lt_min (Real.rpow_pos_of_pos hρ _) (Real.rpow_pos_of_pos hδ _)
  apply lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hc)
  unfold annulusBallMassSize
  refine le_iInf fun z => le_iInf fun hz => le_iInf fun r => le_iInf fun hr => ?_
  have hz' : z ∈ ball (0 : ℂ) (2 * ρ) := by
    exact ball_subset_ball (by linarith) hz.1
  have hrpos : 0 < r := hr.1
  have hrdiv : 0 < r / ρ := div_pos hrpos hρ
  have hdpos : 0 < (r / ρ) ^ β := Real.rpow_pos_of_pos hrdiv _
  have hdle : (r / ρ) ^ β ≤ 1 := Real.rpow_le_one hrdiv.le (by
    have : r < ρ := by linarith [hr.2]
    exact (div_le_one hρ).2 this.le) hβ.le
  by_cases hsmall : r < δ
  · have hmass := (hbound r hrpos (lt_trans hsmall hδr₀) z hz').1
    have heq : r ^ β / (r / ρ) ^ β = ρ ^ β := by
      rw [Real.div_rpow hrpos.le hρ.le]
      field_simp
    calc
      ENNReal.ofReal c ≤ ENNReal.ofReal (ρ ^ β) := ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ = ENNReal.ofReal (r ^ β) / ENNReal.ofReal ((r / ρ) ^ β) := by
        rw [← ENNReal.ofReal_div_of_pos hdpos, heq]
      _ ≤ μ (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) := ENNReal.div_le_div_right hmass _
  · have hmass := (hbound δ hδ hδr₀ z hz').1
    have hsub : ball z δ ⊆ ball z r := ball_subset_ball (le_of_not_gt hsmall)
    have hden : ENNReal.ofReal ((r / ρ) ^ β) ≤ 1 := by
      simpa using ENNReal.ofReal_le_ofReal hdle
    calc
      ENNReal.ofReal c ≤ ENNReal.ofReal (δ ^ β) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ ≤ μ (ball z r) := hmass.trans (measure_mono hsub)
      _ ≤ μ (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) := by
        simpa using (ENNReal.div_le_div_left hden (μ (ball z r)))

/-- Local finiteness makes the ball-mass size finite at every positive scale. -/
theorem annulusBallMassSize_ne_top_of_locallyFinite
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (β : ℝ) :
    annulusBallMassSize μ β ρ 0 ≠ ∞ := by
  let z : ℂ := ((3 * ρ / 4 : ℝ) : ℂ)
  let r : ℝ := ρ / 8
  have hz : z ∈ annulus (0 : ℂ) (ρ / 2) ρ := by
    change dist z 0 < ρ ∧ ¬ dist z 0 ≤ ρ / 2
    have hd : dist z 0 = 3 * ρ / 4 := by
      simp [z, dist_eq_norm, hρ.le]
    rw [hd]
    constructor <;> linarith
  have hr : r ∈ Ioo (0 : ℝ) (ρ / 4) := by
    dsimp [r]
    constructor <;> linarith
  have hden : ENNReal.ofReal ((r / ρ) ^ β) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (div_pos hr.1 hρ) _)).ne'
  apply ne_top_of_le_ne_top (ENNReal.div_ne_top (measure_ball_lt_top (μ := μ) (x := z) (r := r)).ne hden)
  unfold annulusBallMassSize
  exact iInf_le_of_le z (iInf_le_of_le hz (iInf_le_of_le r (iInf_le_of_le hr le_rfl)))

end HarmonicBalls.Section6
