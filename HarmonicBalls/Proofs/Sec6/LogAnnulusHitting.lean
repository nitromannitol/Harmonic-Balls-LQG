import HarmonicBalls.Proofs.Sec6.LogAnnulusExit

/-! # A logarithmic bound for Brownian annulus crossings -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric InnerProductSpace
open scoped NNReal ENNReal Topology

/-- The probability of leaving an annulus through its inner circle is bounded
by the ratio of the corresponding logarithmic potentials. -/
theorem planarBrownian_exit_annulus_inner_le (a : ℂ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {x : ℂ} (hx : x ∈ annulus a r R) :
    planarBrownianMotion x {ω : ContinuousPath ℂ |
      ‖ω ((ContinuousPath.exitTime (annulus a r R) ω).toNNReal) - a‖ ≤ r} ≤
    ENNReal.ofReal (Real.log R - clippedAnnulusLog a r R x) /
      ENNReal.ofReal (Real.log R - Real.log r) := by
  let D := annulus a r R
  let q := clippedAnnulusLog a r R
  let F : ContinuousPath ℂ → ℝ := fun ω => Real.log R - q (ω ((ContinuousPath.exitTime D ω).toNNReal))
  have hD : IsOpen D := isOpen_ball.sdiff isClosed_closedBall
  have hDb : Bornology.IsBounded D := isBounded_ball.subset sdiff_subset
  have hqint : Integrable (fun ω : ContinuousPath ℂ => q (ω ((ContinuousPath.exitTime D ω).toNNReal)))
      (planarBrownianMotion x) :=
    integrable_at_exitTime_of_bounded_measurable hD hDb
      (continuous_clippedAnnulusLog a hr).measurable (norm_clippedAnnulusLog_le a hr hrR.le) x
  have hFint : Integrable F (planarBrownianMotion x) := (integrable_const _).sub hqint
  have hnonneg (ω : ContinuousPath ℂ) : 0 ≤ F ω := by
    dsimp [F, q, clippedAnnulusLog]
    have hlo : 0 < max r (min R ‖ω ((ContinuousPath.exitTime D ω).toNNReal) - a‖) :=
      lt_of_lt_of_le hr (le_max_left _ _)
    have hhi : max r (min R ‖ω ((ContinuousPath.exitTime D ω).toNNReal) - a‖) ≤ R :=
      max_le hrR.le (min_le_left _ _)
    exact sub_nonneg.mpr (Real.log_le_log hlo hhi)
  have hden : 0 < Real.log R - Real.log r := sub_pos.mpr (Real.log_lt_log hr hrR)
  have hint : ∫⁻ ω, ENNReal.ofReal (F ω) ∂(planarBrownianMotion x) =
      ENNReal.ofReal (Real.log R - q x) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hFint (Eventually.of_forall hnonneg)]
    congr 1
    change (∫ ω, (Real.log R - q (ω ((ContinuousPath.exitTime D ω).toNNReal)))
      ∂(planarBrownianMotion x)) = _
    rw [integral_sub (integrable_const _) hqint]
    simp only [integral_const, probReal_univ, one_smul]
    rw [← clippedAnnulusLog_eq_integral_exitTime a hr hrR.le hx]
  have hmeas := hFint.aemeasurable.ennreal_ofReal
  have hmarkov := meas_ge_le_lintegral_div hmeas ((ENNReal.ofReal_pos.mpr hden).ne')
    (ENNReal.ofReal_ne_top)
  rw [hint] at hmarkov
  refine (measure_mono ?_).trans hmarkov
  intro ω hω
  change ENNReal.ofReal (Real.log R - Real.log r) ≤ ENNReal.ofReal (F ω)
  apply ENNReal.ofReal_le_ofReal
  change Real.log R - Real.log r ≤ Real.log R - Real.log (max r (min R ‖ω _ - a‖))
  rw [min_eq_right (hω.trans hrR.le), max_eq_left hω]

/-- A path which reaches the centre before exiting the outer disc must first
exit the annulus through its inner boundary. -/
theorem hit_center_before_outer_exit_subset_inner_exit (a : ℂ) {r R : ℝ} (hr : 0 < r) :
    {ω : ContinuousPath ℂ | ∃ t : ℝ≥0, ω t = a ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (ball a R) ω} ⊆
    {ω | ‖ω ((ContinuousPath.exitTime (annulus a r R) ω).toNNReal) - a‖ ≤ r} := by
  intro ω hω
  obtain ⟨t, ht, hout⟩ := hω
  have ha : a ∉ annulus a r R := by
    simp only [annulus, Set.mem_sdiff, mem_closedBall, dist_self, hr.le, not_true_eq_false, and_false,
      not_false_eq_true]
  have htime : ContinuousPath.exitTime (annulus a r R) ω ≤ (t : ℝ≥0∞) :=
    ContinuousPath.exitTime_le_of_notMem _ ω t (by simpa only [ht] using ha)
  have hfin : ContinuousPath.exitTime (annulus a r R) ω ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top htime
  have hlt : ContinuousPath.exitTime (annulus a r R) ω <
      ContinuousPath.exitTime (ball a R) ω := htime.trans_lt hout
  have hin : ω ((ContinuousPath.exitTime (annulus a r R) ω).toNNReal) ∈ ball a R := by
    apply ContinuousPath.mem_of_lt_exitTime
    simpa only [ENNReal.coe_toNNReal hfin] using hlt
  have hnot : ω ((ContinuousPath.exitTime (annulus a r R) ω).toNNReal) ∉ annulus a r R :=
    coordinate_exitTime_notMem (isOpen_ball.sdiff isClosed_closedBall) ω hfin
  have hclosed : ω ((ContinuousPath.exitTime (annulus a r R) ω).toNNReal) ∈ closedBall a r := by
    by_contra h
    exact hnot ⟨hin, h⟩
  change ‖ω ((ContinuousPath.exitTime (annulus a r R) ω).toNNReal) - a‖ ≤ r
  simpa only [mem_closedBall, dist_eq_norm] using hclosed

/-- Logarithmic control of hitting the centre before the outer exit. -/
theorem planarBrownian_hit_center_before_exit_le (a : ℂ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {x : ℂ} (hx : x ∈ annulus a r R) :
    planarBrownianMotion x {ω : ContinuousPath ℂ | ∃ t : ℝ≥0, ω t = a ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (ball a R) ω} ≤
    ENNReal.ofReal (Real.log R - clippedAnnulusLog a r R x) /
      ENNReal.ofReal (Real.log R - Real.log r) :=
  (measure_mono (hit_center_before_outer_exit_subset_inner_exit a hr)).trans
    (planarBrownian_exit_annulus_inner_le a hr hrR hx)

/-- A planar Brownian motion does not hit the centre before leaving any
larger disc, provided it starts away from that centre. -/
theorem planarBrownian_hit_center_before_exit_eq_zero (a x : ℂ) {R : ℝ}
    (hx : x ≠ a) (hR : ‖x - a‖ < R) :
    planarBrownianMotion x {ω : ContinuousPath ℂ | ∃ t : ℝ≥0, ω t = a ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (ball a R) ω} = 0 := by
  have hd : 0 < ‖x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hlim : Tendsto (fun s : ℝ => ENNReal.ofReal
      ((Real.log R - Real.log ‖x - a‖) / (Real.log R + s))) atTop (𝓝 0) := by
    have hden : Tendsto (fun s : ℝ => Real.log R + s) atTop atTop :=
      tendsto_atTop_add_const_left atTop (Real.log R) tendsto_id
    have hq := (tendsto_const_nhds.div_atTop hden : Tendsto
      (fun s : ℝ => (Real.log R - Real.log ‖x - a‖) / (Real.log R + s)) atTop (𝓝 0))
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hq
  apply le_antisymm ?_ bot_le
  apply ge_of_tendsto hlim
  have hsmall : ∀ᶠ s : ℝ in atTop, Real.exp (-s) < ‖x - a‖ :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (Iio_mem_nhds hd))
  filter_upwards [hsmall] with s hs
  have hr : 0 < Real.exp (-s) := Real.exp_pos _
  have hrR : Real.exp (-s) < R := hs.trans hR
  have hmem : x ∈ annulus a (Real.exp (-s)) R := by
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le, dist_eq_norm]
    exact ⟨hR, hs⟩
  have hlog : clippedAnnulusLog a (Real.exp (-s)) R x = Real.log ‖x - a‖ := by
    simp only [clippedAnnulusLog, min_eq_right hR.le, max_eq_right hs.le]
  have hdenpos : 0 < Real.log R + s := by
    have := sub_pos.mpr (Real.log_lt_log hr hrR)
    simpa only [Real.log_exp, sub_neg_eq_add] using this
  have hbound := planarBrownian_hit_center_before_exit_le a hr hrR hmem
  rw [hlog, Real.log_exp, sub_neg_eq_add, ← ENNReal.ofReal_div_of_pos hdenpos] at hbound
  exact hbound

/-- Planar Brownian motion almost surely avoids every prescribed point
other than its starting point. -/
theorem planarBrownianMotion_point_avoidance (x a : ℂ) (hxa : x ≠ a) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ∀ t : ℝ≥0, ω t ≠ a := by
  let R : ℕ → ℝ := fun n => n + ‖x - a‖ + 1
  let U : ℕ → Set ℂ := fun n => ball a (R n)
  have hR (n : ℕ) : ‖x - a‖ < R n := by
    dsimp [R]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hU : ContinuousPath.IsOpenExhaustion U := by
    refine ⟨fun _ => isOpen_ball, ?_, ?_⟩
    · intro m n hmn
      apply ball_subset_ball
      dsimp [U, R]
      have hm : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
      linarith
    · rw [iUnion_eq_univ_iff]
      intro z
      obtain ⟨n, hn⟩ := exists_nat_gt (dist z a)
      refine ⟨n, ?_⟩
      change dist z a < R n
      dsimp [R]
      have hnorm : 0 ≤ ‖x - a‖ := norm_nonneg _
      linarith
  have hnull : (planarBrownianMotion x) (⋃ n : ℕ,
      {ω : ContinuousPath ℂ | ∃ t : ℝ≥0, ω t = a ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (U n) ω}) = 0 := by
    apply measure_iUnion_null
    intro n
    exact planarBrownian_hit_center_before_exit_eq_zero a x hxa (hR n)
  apply ae_iff.mpr
  apply measure_mono_null _ hnull
  intro ω hω
  simp only [Set.mem_ofPred_eq, not_forall, not_not] at hω
  obtain ⟨t, ht⟩ := hω
  obtain ⟨N, hN⟩ := hU.exists_lt_exitTime ω t
  exact mem_iUnion.mpr ⟨N, t, ht, hN N le_rfl⟩

end HarmonicBalls.Section6
