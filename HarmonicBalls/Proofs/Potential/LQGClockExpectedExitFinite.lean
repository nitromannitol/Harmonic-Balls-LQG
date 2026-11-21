import HarmonicBalls.Proofs.Potential.LQGActualContinuousGreenConvergence
import HarmonicBalls.Proofs.Potential.LQGClockExpectationLimit
import HarmonicBalls.Proofs.Potential.LQGClockOfLocallyUniformLimit
import HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity
import HarmonicBalls.Proofs.Sec6.GreenIntegrability
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-! # Finite expected exit times of Liouville Brownian motion from every start

The expected exit time of the time change by an LQG clock is at most the lower limit of the
Green integrals of the approximating measures. The Green function of a bounded domain is
dominated by the Green function of a larger disc times a continuous cutoff that equals one on
the domain and has compact support in the disc. On one event of full probability the Green
integrals of every such cutoff against the approximating measures converge, for every disc and
every pole, to a finite limit. Hence, for almost every field, the expected exit time of
Liouville Brownian motion from every smooth bounded domain is finite from every start in the
domain, for every family of clocks that are LQG clocks and almost surely time-change clocks
from every start.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology Metric
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- For almost every field, for every smooth bounded domain and every start in it, the expected
exit time of Liouville Brownian motion is finite for every family of clocks that are, from
every start, LQG clocks of the inserted field and almost surely time-change clocks. -/
theorem ae_forall_expectedLBMExitTime_lt_top
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (fieldCircleAverage α (hcirc ω)) x (F ω x))
    (hT : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω x b)) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ x ∈ O,
      expectedLBMExitTime (F ω x) O x < ⊤ := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  filter_upwards [hF, hT, ae_continuous_fieldCircleAverage hlp α,
    hh.ae_tendsto_singular_green_integral_continuous hγ hγ2 hα hμ] with ω hFω hTω hcω hgreen
  intro O hO x hx
  obtain ⟨R, hR⟩ := hO.1.subset_ball (0 : ℂ)
  let O' : Set ℂ := ball (0 : ℂ) (R + 2)
  have hO'o : IsOpen O' := isOpen_ball
  have hO'b : Bornology.IsBounded O' := isBounded_ball
  have hOO' : O ⊆ O' := hR.trans (ball_subset_ball (by linarith))
  let φ : ℂ → ℝ := fun y => max 0 (min 1 (R + 1 - ‖y‖))
  have hφc : Continuous φ :=
    continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))
  have hφ0 (y : ℂ) : 0 ≤ φ y := le_max_left _ _
  have hφ1 (y : ℂ) : φ y ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have hφz (y : ℂ) (hy : R + 1 ≤ ‖y‖) : φ y = 0 := by
    simp only [φ]
    apply max_eq_left
    exact (min_le_right _ _).trans (by linarith)
  have hφO (y : ℂ) (hy : y ∈ O) : φ y = 1 := by
    have hyR : ‖y‖ < R := by simpa [mem_ball, dist_zero_right] using hR hy
    simp only [φ]
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  have hφs : Function.support φ ⊆ closedBall (0 : ℂ) (R + 1) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    exact hy (hφz y (le_of_lt (not_le.mp h)))
  have hφcs : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 1)) fun y hy => by
      by_contra h
      exact hy (hφs h)
  have hφO' : tsupport φ ⊆ O' :=
    (closure_minimal hφs isClosed_closedBall).trans (closedBall_subset_ball (by linarith))
  have hlim := hgreen O' hO'o hO'b x φ hφc hφcs hφO'
  let dens : ℕ → ℂ → ℝ := fun k y => dyadicScale k ^ (γ ^ 2 / 2) *
    Real.exp (γ * fieldCircleAverage α (hcirc ω) (dyadicScale k) y)
  have hdc (k : ℕ) : Continuous (dens k) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (hcω _ (dyadicScale_pos k))))
  have hd0 (k : ℕ) (y : ℂ) : 0 ≤ dens k y :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
  let I : ℕ → ℝ := fun k => ∫ y, greenFunction O' x y * φ y ∂
    (lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k))
  have hseq : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall fun k => dyadicScale_pos k⟩
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hIlim : Tendsto I atTop (𝓝 (∫ y, greenFunction O' x y * φ y ∂(μ ω))) :=
    hlim.comp hseq
  have hGm : Measurable (fun y => greenFunction O' x y * φ y) :=
    (measurable_greenFunction hO'o x).mul hφc.measurable
  have hGi : Integrable (greenFunction O' x) := integrable_greenFunction_pole hO'o hO'b x
  have hbound (k : ℕ) : (∫⁻ y, ENNReal.ofReal (2 * greenFunction O x y) *
      ENNReal.ofReal (dens k y)) ≤ 2 * ENNReal.ofReal (I k) := by
    obtain ⟨Mk, hMk⟩ := (isCompact_closedBall (0 : ℂ) (R + 1)).exists_bound_of_continuousOn
      (hdc k).continuousOn
    have hwd : lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) =
        volume.withDensity (fun y => ENNReal.ofReal (dens k y)) := rfl
    have hlin : (∫⁻ y, ENNReal.ofReal (greenFunction O' x y * φ y) ∂
        (lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k))) =
        ∫⁻ y, ENNReal.ofReal (dens k y) * ENNReal.ofReal (greenFunction O' x y * φ y) := by
      rw [hwd, lintegral_withDensity_eq_lintegral_mul _ (hdc k).measurable.ennreal_ofReal
        hGm.ennreal_ofReal]
      rfl
    have hpt (y : ℂ) : ENNReal.ofReal (dens k y) * ENNReal.ofReal (greenFunction O' x y * φ y) ≤
        ENNReal.ofReal (max Mk 0) * ENNReal.ofReal (greenFunction O' x y) := by
      rw [← ENNReal.ofReal_mul (hd0 k y), ← ENNReal.ofReal_mul (le_max_right _ _)]
      apply ENNReal.ofReal_le_ofReal
      have hG0 : 0 ≤ greenFunction O' x y := greenFunction_nonneg hO'b x y
      by_cases hy : ‖y‖ ≤ R + 1
      · have hyb : y ∈ closedBall (0 : ℂ) (R + 1) := by
          rwa [mem_closedBall, dist_zero_right]
        have hdk : dens k y ≤ max Mk 0 := by
          have := hMk y hyb
          rw [Real.norm_eq_abs, abs_of_nonneg (hd0 k y)] at this
          exact this.trans (le_max_left _ _)
        calc dens k y * (greenFunction O' x y * φ y) ≤ dens k y * greenFunction O' x y :=
              mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hG0 (hφ1 y)) (hd0 k y)
          _ ≤ max Mk 0 * greenFunction O' x y := mul_le_mul_of_nonneg_right hdk hG0
      · rw [hφz y (le_of_lt (not_le.mp hy)), mul_zero, mul_zero]
        exact mul_nonneg (le_max_right _ _) hG0
    have hfin : (∫⁻ y, ENNReal.ofReal (greenFunction O' x y * φ y) ∂
        (lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k))) ≠ ⊤ := by
      rw [hlin]
      refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
      rw [lintegral_const_mul _ (measurable_greenFunction hO'o x).ennreal_ofReal]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
      rw [← ofReal_integral_eq_lintegral_ofReal hGi
        (Filter.Eventually.of_forall fun y => greenFunction_nonneg hO'b x y)]
      exact ENNReal.ofReal_ne_top
    have hint : Integrable (fun y => greenFunction O' x y * φ y)
        (lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)) := by
      refine ⟨hGm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y =>
        mul_nonneg (greenFunction_nonneg hO'b x y) (hφ0 y))]
      exact lt_top_iff_ne_top.mpr hfin
    have hIk : ENNReal.ofReal (I k) = ∫⁻ y, ENNReal.ofReal (dens k y) *
        ENNReal.ofReal (greenFunction O' x y * φ y) := by
      rw [← hlin]
      exact ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y =>
        mul_nonneg (greenFunction_nonneg hO'b x y) (hφ0 y))
    rw [hIk, ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    apply lintegral_mono
    intro y
    have hle : greenFunction O x y ≤ greenFunction O' x y * φ y := by
      by_cases hy : y ∈ O
      · rw [hφO y hy, mul_one]
        exact Section6.greenFunction_le_of_subset hOO' hO'b x y
      · rw [greenFunction_of_notMem_right hy x]
        exact mul_nonneg (greenFunction_nonneg hO'b x y) (hφ0 y)
    calc ENNReal.ofReal (2 * greenFunction O x y) * ENNReal.ofReal (dens k y) =
        2 * (ENNReal.ofReal (dens k y) * ENNReal.ofReal (greenFunction O x y)) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          ring
      _ ≤ 2 * (ENNReal.ofReal (dens k y) * ENNReal.ofReal (greenFunction O' x y * φ y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hle)
            zero_le) zero_le
  have hFat := expectedLBMExitTime_le_liminf_clockApprox_green hO hx
    (fun k => hcω _ (dyadicScale_pos k)) (hFω x) (hTω x)
  have hlimI : Tendsto (fun k => 2 * ENNReal.ofReal (I k)) atTop
      (𝓝 (2 * ENNReal.ofReal (∫ y, greenFunction O' x y * φ y ∂(μ ω)))) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hIlim) (Or.inr (by norm_num))
  calc expectedLBMExitTime (F ω x) O x
      ≤ liminf (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (2 * greenFunction O x y) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
          fieldCircleAverage α (hcirc ω) (dyadicScale k) y))) atTop := hFat
    _ ≤ liminf (fun k => 2 * ENNReal.ofReal (I k)) atTop :=
      liminf_le_liminf (Filter.Eventually.of_forall hbound)
    _ = 2 * ENNReal.ofReal (∫ y, greenFunction O' x y * φ y ∂(μ ω)) := hlimI.liminf_eq
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top

end HarmonicBalls
