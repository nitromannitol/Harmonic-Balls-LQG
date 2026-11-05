import HarmonicBalls.Proofs.Sec6.ScaledDenseCentreCounts

/-! The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. -/

/-! # Scaled dense-centre comparison under full support -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- A point in the scaled relative centre ball has a relative coordinate in
 the unit centre ball. -/
theorem exists_relative_nearby_coordinate {x z : ℂ} {t : ℝ} (ht : 0 < t)
    (hz : z ∈ ball x (t / 100)) :
    ∃ v ∈ ball (0 : ℂ) ((1 : ℝ) / 100), z = x + t • v := by
  refine ⟨t⁻¹ • (z - x), ?_, ?_⟩
  · have hz' : ‖z - x‖ < t / 100 := by simpa [mem_ball, dist_eq_norm] using hz
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    rw [inv_mul_eq_div, div_lt_iff₀ ht]
    linarith
  · simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul]
    abel

/-- Full support gives positive mass to all annuli with radii three and five
 times a positive scale. -/
theorem annulus_three_five_pos_of_fullSupport (μ : Measure ℂ)
    (hfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U)
    (z : ℂ) {r : ℝ} (hr : 0 < r) : 0 < μ (annulus z (3 * r) (5 * r)) := by
  apply hfull _ (isOpen_ball.sdiff isClosed_closedBall)
  refine ⟨z + (((4 * r : ℝ) : ℂ)), ?_⟩
  have hd : dist (z + (((4 * r : ℝ) : ℂ))) z = 4 * r := by
    simp [dist_eq_norm, hr.le]
  change dist (z + (((4 * r : ℝ) : ℂ))) z < 5 * r ∧
    ¬ dist (z + (((4 * r : ℝ) : ℂ))) z ≤ 3 * r
  rw [hd]
  constructor <;> linarith

universe u

/-- Under all-scales volume growth, scaled dense-family good-radius counts
are bounded by the relaxed root count for mass-typical roots in the relevant
scaled balls. -/
theorem ae_lqg_ae_scaled_nearby_count_le_root_count_of_mem_ball
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ (S : Set ℝ), S.Finite → ∀ (x : ℂ) (R : ℝ → ℝ),
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      (∀ r ∈ S, 0 < R r ∧ z ∈ ball x (R r / 100)) →
      {r ∈ S | ∀ i, IsGoodAnnulus (μ ω) (R r)
        (x + R r • nearbyDenseCentre i) a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus (μ ω) (R r) z a' b'}.ncard := by
  filter_upwards [ae_lqg_ae_scaled_nearby_goodAnnuli_count_le_root_count
      hI2 hγ hγ2 hα hGFF hμ,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω hfull
  filter_upwards [hω] with z hz
  intro S hS x R a a' b b' ha' ha hb hbb hreg
  apply hz S hS x R ha' ha hb hbb
  intro r hr
  obtain ⟨hrpos, hrball⟩ := hreg r hr
  exact ⟨hrpos, exists_relative_nearby_coordinate hrpos hrball,
    annulus_three_five_pos_of_fullSupport (μ ω) hfull z hrpos⟩

/-- One ball at the smallest scale suffices for the count comparison over
any finite family of larger radii. -/
theorem ae_lqg_ae_scaled_nearby_count_le_root_count_of_smallest_ball
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ (S : Set ℝ), S.Finite → ∀ (x : ℂ) (s ε : ℝ),
      0 < s → 0 < ε → (∀ r ∈ S, ε ≤ r) → z ∈ ball x (s * ε / 100) →
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      {r ∈ S | ∀ i, IsGoodAnnulus (μ ω) (s * r)
        (x + (s * r) • nearbyDenseCentre i) a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus (μ ω) (s * r) z a' b'}.ncard := by
  filter_upwards [ae_lqg_ae_scaled_nearby_count_le_root_count_of_mem_ball
    hI2 hγ hγ2 hα hGFF hμ] with ω hω
  filter_upwards [hω] with z hz
  intro S hS x s ε hs hε hSε hzball a a' b b' ha' ha hb hbb
  apply hz S hS x (fun r => s * r) ha' ha hb hbb
  intro r hr
  have hεr := hSε r hr
  refine ⟨mul_pos hs (lt_of_lt_of_le hε hεr), ?_⟩
  apply ball_subset_ball ?_ hzball
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hεr hs.le) (by norm_num)

end HarmonicBalls.Section6
