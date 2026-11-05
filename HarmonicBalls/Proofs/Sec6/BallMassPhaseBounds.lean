import HarmonicBalls.Proofs.Sec6.BallMassSizePositive

/-! # Ball-mass bounds over compact dyadic phases -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- Volume growth on one fixed disc gives a common positive lower bound for
all ball-mass sizes with phase in `[1/2,1]`. -/
theorem exists_ballMassSize_lower_bound_on_dyadic_phases
    {μ : Measure ℂ} {β βplus : ℝ} (hV : VolumeGrowth μ 2 β βplus) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ Icc (1 / 2 : ℝ) 1,
      ENNReal.ofReal c ≤ annulusBallMassSize μ β s 0 := by
  obtain ⟨hβ, _, r₀, hr₀, hbound⟩ := hV
  let δ : ℝ := min (r₀ / 2) (1 / 16)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr₀ : δ < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let c : ℝ := min ((1 / 2 : ℝ) ^ β) (δ ^ β)
  have hc : 0 < c := lt_min (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hδ _)
  refine ⟨c, hc, ?_⟩
  intro s hs
  have hspos : 0 < s := by linarith [hs.1]
  unfold annulusBallMassSize
  refine le_iInf fun z => le_iInf fun hz => le_iInf fun r => le_iInf fun hr => ?_
  have hz' : z ∈ ball (0 : ℂ) 2 := ball_subset_ball (by linarith [hs.2]) hz.1
  have hrdiv : 0 < r / s := div_pos hr.1 hspos
  have hdpos : 0 < (r / s) ^ β := Real.rpow_pos_of_pos hrdiv _
  have hdle : (r / s) ^ β ≤ 1 := Real.rpow_le_one hrdiv.le
    ((div_le_one hspos).2 (by linarith [hr.2])) hβ.le
  by_cases hsmall : r < δ
  · have hmass := (hbound r hr.1 (lt_trans hsmall hδr₀) z hz').1
    have heq : r ^ β / (r / s) ^ β = s ^ β := by
      rw [Real.div_rpow hr.1.le hspos.le]
      field_simp [(Real.rpow_pos_of_pos hr.1 β).ne']
    have hbase : (1 / 2 : ℝ) ^ β ≤ s ^ β :=
      Real.rpow_le_rpow (by norm_num) hs.1 hβ.le
    calc
      ENNReal.ofReal c ≤ ENNReal.ofReal (s ^ β) :=
        ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans hbase)
      _ = ENNReal.ofReal (r ^ β) / ENNReal.ofReal ((r / s) ^ β) := by
        rw [← ENNReal.ofReal_div_of_pos hdpos, heq]
      _ ≤ μ (ball z r) / ENNReal.ofReal ((r / s) ^ β) := ENNReal.div_le_div_right hmass _
  · have hmass := (hbound δ hδ hδr₀ z hz').1
    have hsub : ball z δ ⊆ ball z r := ball_subset_ball (le_of_not_gt hsmall)
    have hden : ENNReal.ofReal ((r / s) ^ β) ≤ 1 := by
      simpa using ENNReal.ofReal_le_ofReal hdle
    calc
      ENNReal.ofReal c ≤ ENNReal.ofReal (δ ^ β) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ ≤ μ (ball z r) := hmass.trans (measure_mono hsub)
      _ ≤ μ (ball z r) / ENNReal.ofReal ((r / s) ^ β) := by
        simpa using (ENNReal.div_le_div_left hden (μ (ball z r)))

/-- A single mass of the disc `B₂(0)` bounds all ball-mass sizes with phase
in `[1/2,1]`. -/
theorem ballMassSize_upper_bound_on_dyadic_phases
    (μ : Measure ℂ) (β : ℝ) {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    annulusBallMassSize μ β s 0 ≤ μ (ball 0 2) / ENNReal.ofReal ((1 / 8 : ℝ) ^ β) := by
  have hspos : 0 < s := by linarith [hs.1]
  let z : ℂ := ((3 * s / 4 : ℝ) : ℂ)
  let r : ℝ := s / 8
  have hz : z ∈ annulus (0 : ℂ) (s / 2) s := by
    change dist z 0 < s ∧ ¬ dist z 0 ≤ s / 2
    have hd : dist z 0 = 3 * s / 4 := by simp [z, dist_eq_norm, hspos.le]
    rw [hd]
    constructor <;> linarith
  have hr : r ∈ Ioo (0 : ℝ) (s / 4) := by
    dsimp [r]
    constructor <;> linarith
  have hsub : ball z r ⊆ ball (0 : ℂ) 2 := by
    intro x hx
    have hd := dist_triangle x z (0 : ℂ)
    have hzdist : dist z 0 = 3 * s / 4 := by simp [z, dist_eq_norm, hspos.le]
    change dist x z < r at hx
    change dist x 0 < 2
    rw [hzdist] at hd
    dsimp [r] at hx
    linarith [hs.2]
  have heq : r / s = 1 / 8 := by dsimp [r]; field_simp
  calc
    annulusBallMassSize μ β s 0 ≤ μ (ball z r) / ENNReal.ofReal ((r / s) ^ β) := by
      unfold annulusBallMassSize
      exact iInf_le_of_le z (iInf_le_of_le hz (iInf_le_of_le r (iInf_le_of_le hr le_rfl)))
    _ ≤ μ (ball 0 2) / ENNReal.ofReal ((1 / 8 : ℝ) ^ β) := by
      rw [heq]
      exact ENNReal.div_le_div_right (measure_mono hsub) _

end HarmonicBalls.Section6
