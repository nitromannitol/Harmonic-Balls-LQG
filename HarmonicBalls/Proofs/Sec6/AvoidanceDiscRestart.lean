import HarmonicBalls.Proofs.Sec6.BrownianHittingTransfer
import HarmonicBalls.Proofs.Sec6.BoundedHarmonicExit
import HarmonicBalls.Proofs.Sec4.Sweep
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # Restarting compact avoidance at a disc exit

The strong Markov property bounds the probability of avoiding a compact set
until domain exit by the mean of the same probability at an inner disc exit.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric InnerProductSpace Complex
open scoped ENNReal NNReal Topology BoundedContinuousFunction

/-- If a path avoids `K` until leaving `U`, and is shifted strictly before
leaving `U`, the shifted path also avoids `K` until leaving `U`. -/
theorem avoidance_after_shift {U K : Set ℂ} (ω : ContinuousPath ℂ) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ContinuousPath.exitTime U ω)
    (havoid : ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω) :
    ContinuousPath.exitTime U (ContinuousPath.shift t ω) ≤
      ContinuousPath.exitTime Kᶜ (ContinuousPath.shift t ω) := by
  have htK : (t : ℝ≥0∞) < ContinuousPath.exitTime Kᶜ ω := ht.trans_le havoid
  rw [← ContinuousPath.exitTime_shift_add U ω t ht,
    ← ContinuousPath.exitTime_shift_add Kᶜ ω t htK] at havoid
  exact (ENNReal.add_le_add_iff_right (by simp : (t : ℝ≥0∞) ≠ ∞)).mp havoid

/-- Restarting at an inner disc exit gives a mean bound for compact avoidance.
The outer disc guarantees the restart takes place strictly before domain exit. -/
theorem planarBrownian_avoidance_le_disc_exit_mean
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) {x : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRU : ball x R ⊆ U) :
    planarBrownianMotion x {ω | ContinuousPath.exitTime U ω ≤
      ContinuousPath.exitTime Kᶜ ω} ≤
    ∫⁻ ω, planarBrownianMotion
      (ω ((ContinuousPath.exitTime (ball x r) ω).toNNReal))
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p}
      ∂(planarBrownianMotion x) := by
  let E : Set (ContinuousPath ℂ) := {ω | ContinuousPath.exitTime U ω ≤
    ContinuousPath.exitTime Kᶜ ω}
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime (ball x r)
  have hτ := ContinuousPath.isStoppingTime_exitTime (ball x r) isOpen_ball
  have hE : MeasurableSet E := measurableSet_le
    (ContinuousPath.measurable_exitTime U hU)
    (ContinuousPath.measurable_exitTime Kᶜ hK.isClosed.isOpen_compl)
  have hshift := ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ
  have hfin : ∀ᵐ ω ∂(planarBrownianMotion x), τ ω < ⊤ :=
    ae_planarBrownianMotion_exitTime_ball_lt_top x r
  have hcross := ae_planarBrownian_ball_crossing_unconditional (x := x) hr hrR
  have hrestart :=
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
      x τ hτ univ (by simp)
  rw [← planarBrownianMotion_eq_continuousProcess] at hrestart
  simp only [univ_inter] at hrestart
  have hre : (planarBrownianMotion x).restrict {ω | (τ ω : WithTop ℝ≥0) < ⊤} = planarBrownianMotion x :=
    Measure.restrict_eq_self_of_ae_mem hfin
  change ((planarBrownianMotion x).restrict {ω | τ ω < ⊤}).map
      (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) =
    Kernel.comap planarBrownianMotion (fun ω => ω ((τ ω).untopD 0))
      (ContinuousPath.measurable_eval_untopD_stoppingTime τ hτ) ∘ₘ
        ((planarBrownianMotion x).restrict {ω | τ ω < ⊤}) at hrestart
  rw [hre] at hrestart
  have happ := congrArg (fun m : Measure (ContinuousPath ℂ) => m E) hrestart
  rw [Measure.map_apply hshift hE, Measure.bind_apply hE (Kernel.aemeasurable _)] at happ
  simp only [Kernel.comap_apply] at happ
  calc
    planarBrownianMotion x E ≤ planarBrownianMotion x
        ((fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' E) := by
      apply measure_mono_ae
      filter_upwards [hfin, hcross] with ω hf ⟨hc, _⟩ hω
      have ht : (τ ω).untopD 0 < ContinuousPath.exitTime U ω := by
        simpa [τ, ENNReal.coe_toNNReal (ne_of_lt hf)] using
          hc.trans_le (ContinuousPath.exitTime_mono hRU ω)
      exact avoidance_after_shift ω _ ht hω
    _ = ∫⁻ ω, planarBrownianMotion (ω ((τ ω).untopD 0)) E ∂(planarBrownianMotion x) := happ
    _ = _ := by rfl

/-- The half-unit disc centred on the middle circle stays in the unit good annulus. -/
theorem middleCircle_half_disc_subset_goodAnnulus {v : ℂ}
    (hv : v ∈ sphere (0 : ℂ) 4) :
    ball v (1 / 2 : ℝ) ⊆ annulus 0 3 5 := by
  intro z hz
  have hv' : dist v 0 = 4 := hv
  have hz' : dist z v < 1 / 2 := hz
  have hu := dist_triangle z v 0
  have hl := dist_triangle v z 0
  have hs : dist v z = dist z v := dist_comm _ _
  change z ∈ ball 0 5 ∧ z ∉ closedBall 0 3
  simp only [mem_ball, mem_closedBall, not_le]
  constructor <;> linarith

/-- The disc-exit mean bound for unit-annulus compact avoidance. -/
theorem unit_goodAnnulus_avoidance_le_disc_exit_mean
    {K : Set ℂ} (hK : IsCompact K) {v : ℂ} (hv : v ∈ sphere (0 : ℂ) 4)
    {r : ℝ} (hr : 0 < r) (hrhalf : r < 1 / 2) :
    planarBrownianMotion v {ω | ContinuousPath.exitTime (annulus 0 3 5) ω ≤
      ContinuousPath.exitTime Kᶜ ω} ≤
    ∫⁻ ω, planarBrownianMotion
      (ω ((ContinuousPath.exitTime (ball v r) ω).toNNReal))
      {p | ContinuousPath.exitTime (annulus 0 3 5) p ≤ ContinuousPath.exitTime Kᶜ p}
      ∂(planarBrownianMotion v) :=
  planarBrownian_avoidance_le_disc_exit_mean (isOpen_ball.sdiff isClosed_closedBall)
    hK hr hrhalf (middleCircle_half_disc_subset_goodAnnulus hv)

/-- The exit distribution from a disc started at its centre has the circle
average of any bounded continuous test function. -/
theorem planarBrownian_integral_disc_exit_eq_circleAverage
    {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ}
    (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) :
    (∫ ω : ContinuousPath ℂ, f (ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal))
      ∂(planarBrownianMotion c)) = Real.circleAverage f c r := by
  let q := discSweep Set.univ c r f
  have hD : IsSweepDisc Set.univ c r := ⟨hr, subset_univ _⟩
  have hq : Continuous q := by
    apply continuousOn_univ.mp
    exact continuousOn_discSweep isOpen_univ hf.continuousOn
  have hci : CircleIntegrable f c r := hD.circleIntegrable hf.continuousOn
  have hh : HarmonicOnNhd q (ball c r) := by
    intro z hz
    have heq : q =ᶠ[𝓝 z] discPoissonIntegral f c r := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact discSweep_of_mem hD hw
    exact (harmonicAt_congr_nhds heq).2 (harmonicOnNhd_discPoissonIntegral hci z hz)
  have hbound : ∀ z, ‖q z‖ ≤ M := by
    intro z
    by_cases hz : z ∈ ball c r
    · rw [show q z = discPoissonIntegral f c r z from discSweep_of_mem hD hz]
      have hb (w : ℂ) : -M ≤ f w ∧ f w ≤ M := by
        have := hM w
        rw [Real.norm_eq_abs, abs_le] at this
        exact this
      have hlo := le_discPoissonIntegral hci hz (fun ζ _ => (hb ζ).1)
      have hhi : discPoissonIntegral f c r z ≤ M := by
        rw [← discPoissonIntegral_const M hz]
        exact discPoissonIntegral_mono hci continuousOn_const.circleIntegrable' hz
          (fun ζ _ => (hb ζ).2)
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hlo, hhi⟩
    · rw [show q z = f z from discSweep_of_not (fun h => hz h.2)]
      exact hM z
  have he := harmonic_eq_integral_planarBrownian_exitTime isOpen_ball isBounded_ball
    hq hh hbound (mem_ball_self hr)
  have hs := ae_planarBrownian_ball_crossing_unconditional (x := c) hr (by linarith : r < 2 * r)
  have hEq : ∀ᵐ ω ∂(planarBrownianMotion c),
      q (ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal)) =
      f (ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal)) := by
    filter_upwards [hs] with ω ⟨_, hsphere⟩
    exact discSweep_of_not (fun h => (sphere_disjoint_ball.ne_of_mem hsphere h.2) rfl)
  rw [integral_congr_ae hEq] at he
  rw [show q c = discPoissonIntegral f c r c from discSweep_of_mem hD (mem_ball_self hr),
    discPoissonIntegral_center hr.ne'] at he
  exact he.symm

/-- The normalized angular measure on a Euclidean circle. -/
noncomputable def normalizedCircleMeasure (c : ℂ) (r : ℝ) : Measure ℂ :=
  (ENNReal.ofReal ((2 * Real.pi)⁻¹) •
    (volume.restrict (Ioc (-Real.pi) Real.pi))).map (circleMap c r)

/-- The normalized angular measure represents the circle average of a bounded
continuous test function. -/
theorem integral_normalizedCircleMeasure (c : ℂ) (r : ℝ) (f : ℂ →ᵇ ℝ) :
    (∫ z, f z ∂(normalizedCircleMeasure c r)) = Real.circleAverage f c r := by
  rw [normalizedCircleMeasure, integral_map (continuous_circleMap c r).measurable.aemeasurable
    f.continuous.aestronglyMeasurable, integral_smul_measure]
  rw [Real.circleAverage_eq_integral_add (-Real.pi)]
  have heq := intervalIntegral.integral_comp_add_right
    (f := fun θ => f (circleMap c r θ)) (a := 0) (b := 2 * Real.pi) (-Real.pi)
  rw [heq]
  have hp : 0 + -Real.pi = -Real.pi := by ring
  have hp' : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [hp, hp', intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]

/-- Brownian motion started at the centre of a disc exits with normalized
angular distribution. -/
theorem planarBrownian_disc_exit_distribution {c : ℂ} {r : ℝ} (hr : 0 < r) :
    (planarBrownianMotion c).map
      (fun ω => ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal)) =
      normalizedCircleMeasure c r := by
  have ht := ContinuousPath.isStoppingTime_exitTime (ball c r) isOpen_ball
  have hm : Measurable (fun ω : ContinuousPath ℂ =>
      ω ((ContinuousPath.exitTime (ball c r) ω).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime (ball c r)) ht
  let : IsFiniteMeasure (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  let : IsFiniteMeasure (ENNReal.ofReal ((2 * Real.pi)⁻¹) •
      volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (normalizedCircleMeasure c r) := by
    unfold normalizedCircleMeasure
    infer_instance
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hm.aemeasurable f.continuous.aestronglyMeasurable,
    integral_normalizedCircleMeasure]
  exact planarBrownian_integral_disc_exit_eq_circleAverage hr f.continuous f.norm_coe_le_norm

/-- Compact avoidance is bounded by its normalized circular average on every
inner disc. -/
theorem planarBrownian_avoidance_le_circle_mean
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) {x : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRU : ball x R ⊆ U) :
    planarBrownianMotion x {ω | ContinuousPath.exitTime U ω ≤
      ContinuousPath.exitTime Kᶜ ω} ≤
    ∫⁻ y, planarBrownianMotion y {ω | ContinuousPath.exitTime U ω ≤
      ContinuousPath.exitTime Kᶜ ω} ∂(normalizedCircleMeasure x r) := by
  have hm := measurable_avoidance_probability hU hK
  have ht := ContinuousPath.isStoppingTime_exitTime (ball x r) isOpen_ball
  have hstop : Measurable (fun ω : ContinuousPath ℂ =>
      ω ((ContinuousPath.exitTime (ball x r) ω).toNNReal)) := by
    simpa using ContinuousPath.measurable_eval_untopD_stoppingTime
      (ContinuousPath.exitTime (ball x r)) ht
  have h := planarBrownian_avoidance_le_disc_exit_mean hU hK hr hrR hRU
  rw [← lintegral_map hm hstop, planarBrownian_disc_exit_distribution hr] at h
  exact h

/-- The unit-annulus compact avoidance probability satisfies a circular
submean inequality for all discs of radius less than one half. -/
theorem unit_goodAnnulus_avoidance_le_circle_mean
    {K : Set ℂ} (hK : IsCompact K) {v : ℂ} (hv : v ∈ sphere (0 : ℂ) 4)
    {r : ℝ} (hr : 0 < r) (hrhalf : r < 1 / 2) :
    planarBrownianMotion v {ω | ContinuousPath.exitTime (annulus 0 3 5) ω ≤
      ContinuousPath.exitTime Kᶜ ω} ≤
    ∫⁻ y, planarBrownianMotion y {ω | ContinuousPath.exitTime (annulus 0 3 5) ω ≤
      ContinuousPath.exitTime Kᶜ ω} ∂(normalizedCircleMeasure v r) :=
  planarBrownian_avoidance_le_circle_mean (isOpen_ball.sdiff isClosed_closedBall)
    hK hr hrhalf (middleCircle_half_disc_subset_goodAnnulus hv)

end HarmonicBalls.Section6
