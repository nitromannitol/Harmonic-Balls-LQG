import HarmonicBalls.Proofs.Sec6.BoundedHarmonicExit

/-! # Logarithmic barriers on annuli

The logarithmic radial function, clipped at the two boundary circles, is
bounded and continuous on the plane. Its Brownian exit representation provides
the basic potential-theoretic step towards point polarity.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric InnerProductSpace
open scoped NNReal ENNReal Topology

/-- The radial logarithm, extended constantly across both boundary circles. -/
noncomputable def clippedAnnulusLog (a : ℂ) (r R : ℝ) (z : ℂ) : ℝ :=
  Real.log (max r (min R ‖z - a‖))

/-- A positive inner radius makes the clipped logarithm continuous. -/
theorem continuous_clippedAnnulusLog (a : ℂ) {r R : ℝ} (hr : 0 < r) :
    Continuous (clippedAnnulusLog a r R) := by
  change Continuous (fun z : ℂ => Real.log (max r (min R ‖z - a‖)))
  apply Continuous.log (by fun_prop)
  intro z
  exact ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _))

/-- The clipped logarithm is harmonic in the open annulus. -/
theorem harmonicOnNhd_clippedAnnulusLog (a : ℂ) {r R : ℝ} (hr : 0 < r) :
    HarmonicOnNhd (clippedAnnulusLog a r R) (annulus a r R) := by
  intro z hz
  have hopen : IsOpen (annulus a r R) := isOpen_ball.sdiff isClosed_closedBall
  have hz' : r < ‖z - a‖ ∧ ‖z - a‖ < R := by
    have h : ‖z - a‖ < R ∧ r < ‖z - a‖ := by
      simpa only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le, dist_eq_norm] using hz
    exact ⟨h.2, h.1⟩
  have hz0 : z - a ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    subst z
    simp only [sub_self, norm_zero] at hz'
    linarith [hz'.1]
  have ha : AnalyticAt ℂ (fun w : ℂ => w - a) z := by fun_prop
  have hlog := ha.harmonicAt_log_norm hz0
  apply (harmonicAt_congr_nhds ?_).2 hlog
  filter_upwards [hopen.mem_nhds hz] with w hw
  have hw' : r < ‖w - a‖ ∧ ‖w - a‖ < R := by
    have h : ‖w - a‖ < R ∧ r < ‖w - a‖ := by
      simpa only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le, dist_eq_norm] using hw
    exact ⟨h.2, h.1⟩
  simp only [clippedAnnulusLog, min_eq_right hw'.2.le, max_eq_right hw'.1.le]

/-- Uniform boundedness of the clipped logarithm. -/
theorem norm_clippedAnnulusLog_le (a : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (z : ℂ) :
    ‖clippedAnnulusLog a r R z‖ ≤ max |Real.log r| |Real.log R| := by
  have hlo : r ≤ max r (min R ‖z - a‖) := le_max_left _ _
  have hhi : max r (min R ‖z - a‖) ≤ R := max_le hrR (min_le_left _ _)
  have hloglo := Real.log_le_log hr hlo
  have hloghi := Real.log_le_log (lt_of_lt_of_le hr hlo) hhi
  change |Real.log (max r (min R ‖z - a‖))| ≤ _
  apply abs_le.mpr
  constructor
  · have := neg_abs_le (Real.log r)
    have := le_max_left |Real.log r| |Real.log R|
    linarith
  · exact hloghi.trans ((le_abs_self _).trans (le_max_right _ _))

/-- The clipped logarithm equals its expected value at the first exit from an
annulus. -/
theorem clippedAnnulusLog_eq_integral_exitTime (a : ℂ) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) {x : ℂ} (hx : x ∈ annulus a r R) :
    clippedAnnulusLog a r R x = ∫ ω : ContinuousPath ℂ,
      clippedAnnulusLog a r R (ω ((ContinuousPath.exitTime (annulus a r R) ω).toNNReal))
        ∂(planarBrownianMotion x) := by
  apply harmonic_eq_integral_planarBrownian_exitTime
    (isOpen_ball.sdiff isClosed_closedBall) (isBounded_ball.subset sdiff_subset)
    (continuous_clippedAnnulusLog a hr) (harmonicOnNhd_clippedAnnulusLog a hr)
    (norm_clippedAnnulusLog_le a hr hrR) hx

end HarmonicBalls.Section6
