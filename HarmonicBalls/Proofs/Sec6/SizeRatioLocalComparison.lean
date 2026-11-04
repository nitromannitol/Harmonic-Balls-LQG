import HarmonicBalls.Proofs.Sec6.Localization

/-! # Local comparison of annular size ratios -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- The balls tested by the ball-mass size lie in the larger annulus. -/
theorem annulusBallMassSize_ball_subset_annulus {x₀ z : ℂ} {ρ r : ℝ}
    (_hρ : 0 < ρ) (hz : z ∈ annulus x₀ (ρ / 2) ρ) (hr : r ∈ Ioo 0 (ρ / 4)) :
    ball z r ⊆ annulus x₀ (ρ / 4) (2 * ρ) := by
  intro y hy
  have hzouter : dist z x₀ < ρ := hz.1
  have hzinner : ρ / 2 < dist z x₀ := lt_of_not_ge hz.2
  have hyz : dist y z < r := hy
  have htri₁ := dist_triangle y z x₀
  have htri₂ := dist_triangle z y x₀
  have hsym : dist z y = dist y z := dist_comm z y
  constructor
  · change dist y x₀ < 2 * ρ
    linarith [hr.2]
  · change ¬ dist y x₀ ≤ ρ / 4
    linarith [hr.2]

/-- The ball-mass size only needs comparability on the larger annulus;
the interior of its hole may contain the singularity. -/
theorem annulusBallMassSize_comparable_on_annulus
    {μ ν : Measure ℂ} {x₀ : ℂ} {ρ : ℝ} {c : ℝ≥0∞}
    (h : IsComparableOn μ ν (annulus x₀ (ρ / 4) (2 * ρ)) c) (hρ : 0 < ρ)
    (β : ℝ) : c * annulusBallMassSize ν β ρ x₀ ≤ annulusBallMassSize μ β ρ x₀ ∧
      annulusBallMassSize μ β ρ x₀ ≤ 4 * c * annulusBallMassSize ν β ρ x₀ := by
  have h4c0 : 4 * c ≠ 0 := mul_ne_zero (by norm_num) h.ne_zero
  have h4ct : 4 * c ≠ ∞ := ENNReal.mul_ne_top (by norm_num) h.ne_top
  constructor
  · refine le_iInf₂ fun z hz => le_iInf₂ fun r hr => ?_
    calc c * annulusBallMassSize ν β ρ x₀ ≤ c * (ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β)) := by
          gcongr; exact iInf₂_le_of_le z hz (iInf₂_le r hr)
      _ = c * ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) := (mul_div_assoc _ _ _).symm
      _ ≤ μ (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) :=
          ENNReal.div_le_div_right (h.le_apply (annulusBallMassSize_ball_subset_annulus hρ hz hr)) _
  · unfold annulusBallMassSize
    simp_rw [ENNReal.mul_iInf_of_ne h4c0 h4ct]
    refine iInf₂_mono fun z hz => iInf₂_mono fun r hr => ?_
    calc μ (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) ≤
        4 * c * ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) :=
          ENNReal.div_le_div_right (h.apply_le (annulusBallMassSize_ball_subset_annulus hρ hz hr)) _
      _ = 4 * c * (ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β)) := mul_div_assoc _ _ _

/-- Comparable measures on the larger annulus transfer both size windows. -/
theorem veryGood_size_windows_of_comparable_on_annulus
    {μ ν : Measure ℂ} {x₀ : ℂ} {ρ : ℝ} {c : ℝ≥0∞}
    (h : IsComparableOn μ ν (annulus x₀ (ρ / 4) (2 * ρ)) c) (hρ : 0 < ρ)
    {β C₁m C₁p C₂m C₂p : ℝ}
    (hM : annulusBallMassSize ν β ρ x₀ / ν (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))
    (hG : annulusGreenPotentialSup ν x₀ (ρ / 4) (2 * ρ) /
      ν (annulus x₀ (ρ / 4) (2 * ρ)) ∈ Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)) :
    annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal (C₁m / 4)) (ENNReal.ofReal (4 * C₁p)) ∧
      annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) /
        μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal (C₂m / 4)) (ENNReal.ofReal (4 * C₂p)) := by
  have hM' := annulusBallMassSize_comparable_on_annulus h hρ β
  have hG' := annulusGreenPotentialSup_comparable h
  exact ⟨ratio_mem_of_comparable h.ne_zero h.ne_top hM'.1 hM'.2
      (h.le_apply Subset.rfl) (h.apply_le Subset.rfl) hM,
    ratio_mem_of_comparable h.ne_zero h.ne_top hG'.1 hG'.2
      (h.le_apply Subset.rfl) (h.apply_le Subset.rfl) hG⟩

end HarmonicBalls.Section6
