import HarmonicBalls.Defs.LQG

/-!
# From closed to open balls

Mathlib states the Besicovitch density theorem for closed balls. This lemma
transfers a uniform mass bound to open balls for an arbitrary measure, without
assuming that spheres have zero measure.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- A uniform relative mass bound on smaller closed balls also holds on the
open ball. -/
theorem measure_inter_ball_le_of_closedBall
    (μ : Measure ℂ) (s : Set ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r) (c : ℝ≥0∞)
    (h : ∀ q : ℝ, 0 < q → q < r →
      μ (s ∩ closedBall z q) ≤ c * μ (closedBall z q)) :
    μ (s ∩ ball z r) ≤ c * μ (ball z r) := by
  let f : Iio r → Set ℂ := fun q => closedBall z q
  have hf : Monotone f := fun _ _ hab => closedBall_subset_closedBall hab
  have hUnion : (⋃ q, f q) = ball z r := by
    rw [← biUnion_lt_closedBall]
    ext x
    simp only [mem_iUnion, f, Subtype.exists, exists_prop, mem_Iio]
  conv_lhs => rw [← hUnion, inter_iUnion, (monotone_const.inter hf).measure_iUnion]
  refine iSup_le fun q => ?_
  have hq : μ (s ∩ closedBall z q) ≤ c * μ (ball z r) := by
    by_cases hpos : 0 < (q : ℝ)
    · exact (h q hpos q.property).trans (mul_le_mul_right (measure_mono (closedBall_subset_ball q.property)) _)
    · have hqhalf : (q : ℝ) ≤ r / 2 := le_trans (le_of_not_gt hpos) (le_of_lt (half_pos hr))
      calc
        _ ≤ μ (s ∩ closedBall z (r / 2)) := measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hqhalf))
        _ ≤ c * μ (closedBall z (r / 2)) := h (r / 2) (half_pos hr) (half_lt_self hr)
        _ ≤ c * μ (ball z r) := mul_le_mul_right (measure_mono (closedBall_subset_ball (half_lt_self hr))) _
  exact hq

/-- Closed-ball density zero implies a uniform relative mass bound for all
sufficiently small open balls. -/
theorem eventually_measure_inter_ball_le_of_closedBall_density_zero
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (s : Set ℂ) (z : ℂ)
    (c : ℝ≥0∞) (hc : 0 < c)
    (hlim : Tendsto (fun r : ℝ => μ (s ∩ closedBall z r) / μ (closedBall z r))
      (𝓝[>] 0) (𝓝 0)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, μ (s ∩ ball z r) ≤ c * μ (ball z r) := by
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0,
      μ (s ∩ closedBall z r) / μ (closedBall z r) < c :=
    hlim (Iio_mem_nhds hc)
  obtain ⟨δ, hδ, hδsmall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1 hsmall
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  apply measure_inter_ball_le_of_closedBall μ s z hr.1 c
  intro q hq hqr
  have hratio := hδsmall ⟨hq, hqr.trans hr.2⟩
  by_cases hzero : μ (closedBall z q) = 0
  · have hz : μ (s ∩ closedBall z q) = 0 := measure_mono_null inter_subset_right hzero
    simp [hz]
  · have htop : μ (closedBall z q) ≠ ∞ := measure_closedBall_lt_top.ne
    have hbound := (ENNReal.div_le_iff hzero htop).1 hratio.le
    simpa only [mul_comm] using hbound

/-- For almost every boundary point of an open set, the mass of the set in
small open balls is an arbitrarily small fraction of the mass of the ball. -/
theorem ae_eventually_measure_inter_ball_le_on_frontier
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {s : Set ℂ} (hs : IsOpen s)
    (c : ℝ≥0∞) (hc : 0 < c) :
    ∀ᵐ z ∂μ.restrict (frontier s), ∀ᶠ r : ℝ in 𝓝[>] 0,
      μ (s ∩ ball z r) ≤ c * μ (ball z r) := by
  have hden := Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet μ hs.measurableSet
  filter_upwards [ae_restrict_of_ae hden, ae_restrict_mem isClosed_frontier.measurableSet] with z hz hfront
  have hnot : z ∉ s := fun hzs => (disjoint_frontier_iff_isOpen.2 hs).le_bot ⟨hfront, hzs⟩
  rw [indicator_of_notMem hnot] at hz
  exact eventually_measure_inter_ball_le_of_closedBall_density_zero μ s z c hc hz

/-- The dyadic radii decrease to zero through positive values. -/
theorem tendsto_dyadicScale_nhdsGT : Tendsto dyadicScale atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · exact Eventually.of_forall dyadicScale_pos

/-- The density bound along the dyadic scales used in Section 8. -/
theorem ae_eventually_measure_inter_dyadicBall_le_on_frontier
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {s : Set ℂ} (hs : IsOpen s)
    (α m : ℝ) (hα : 0 < α) (hm : 0 < m) :
    ∀ᵐ z ∂μ.restrict (frontier s), ∀ᶠ n : ℕ in atTop,
      μ (s ∩ ball z (dyadicScale n)) ≤
        ENNReal.ofReal α * (ENNReal.ofReal m * μ (ball z (dyadicScale n))) := by
  have hc : 0 < ENNReal.ofReal α * ENNReal.ofReal m :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 hα).ne' (ENNReal.ofReal_pos.2 hm).ne'
  filter_upwards [ae_eventually_measure_inter_ball_le_on_frontier μ hs _ hc] with z hz
  filter_upwards [tendsto_dyadicScale_nhdsGT.eventually hz] with n hn
  simpa only [mul_assoc] using hn

end HarmonicBalls
