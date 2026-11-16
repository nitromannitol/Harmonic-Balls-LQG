import HarmonicBalls.Proofs.Potential.LQGClockExpectationLimit
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Convergence of expected Liouville exit times

Uniform integrability of the stopped dyadic clocks implies convergence of
 their expected Green integrals to the expected time-changed exit time.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- Under uniform integrability of the stopped clocks, their Green integrals
converge to the finite expected exit time. -/
theorem tendsto_clockApprox_green_expectedLBMExitTime_of_uniformIntegrable
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {D : Set ℂ}
    (hD : IsSmoothBoundedOpen D) (hx : x ∈ D)
    (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k)))
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b))
    (hui : UniformIntegrable (fun k : ℕ => fun b =>
      lqgClockApprox γ hε (dyadicScale k) b
        (ContinuousPath.exitTime D b).toNNReal) 1 (planarBrownianMotion x)) :
    (∀ k : ℕ, Integrable (fun b => lqgClockApprox γ hε (dyadicScale k) b
      (ContinuousPath.exitTime D b).toNNReal) (planarBrownianMotion x)) ∧
    Integrable (fun b => (lbmExitTime F D b).toReal) (planarBrownianMotion x) ∧
    expectedLBMExitTime F D x ≠ ⊤ ∧
    (∀ k : ℕ, (∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
      ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) y))) ≠ ⊤) ∧
    Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
      ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) y)))
      atTop (𝓝 (expectedLBMExitTime F D x)) := by
  let μ := planarBrownianMotion x
  let A : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    lqgClockApprox γ hε (dyadicScale k) b (ContinuousPath.exitTime D b).toNNReal
  let L : ContinuousPath ℂ → ℝ := fun b => (lbmExitTime F D b).toReal
  have hDo : IsOpen D := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hconv : TendstoInMeasure μ A atTop L := by
    apply tendstoInMeasure_iff_dist.mpr
    intro η hη
    simpa only [A, L, μ, Real.dist_eq] using
      hclock.tendsto_measure_clockApprox_lbmExitTime hDo hD.1 hF hη
  have hui' : UniformIntegrable A 1 μ := hui
  have hL : Integrable L μ := hui'.integrable_of_tendstoInMeasure hconv
  have hA (k : ℕ) : Integrable (A k) μ := memLp_one_iff_integrable.mp (hui'.memLp k)
  have hLp : Tendsto (fun k => eLpNorm (A k - L) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
      (fun k => (hA k).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hL)
      hui'.unifIntegrable hconv
  have hint : Tendsto (fun k => ∫ b, A k b ∂μ) atTop (𝓝 (∫ b, L b ∂μ)) :=
    tendsto_integral_of_L1' L (Eventually.of_forall hA) hLp
  have hAn (k : ℕ) : 0 ≤ᵐ[μ] A k := by
    filter_upwards with b
    exact intervalIntegral.integral_nonneg_of_forall (NNReal.coe_nonneg _) fun _ =>
      mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
  have hLn : 0 ≤ᵐ[μ] L := Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hfin : ∀ᵐ b ∂μ, lbmExitTime F D b ≠ ⊤ := by
    filter_upwards [hF, Section6.ae_planarBrownian_exitTime_bounded_lt_top x hD.1] with b hb hτ
    rw [lbmExitTime_eq_clockValue hDo hb hτ.ne]
    exact ENNReal.coe_ne_top
  have hE : ENNReal.ofReal (∫ b, L b ∂μ) = expectedLBMExitTime F D x := by
    rw [ofReal_integral_eq_lintegral_ofReal hL hLn]
    unfold expectedLBMExitTime
    apply lintegral_congr_ae
    filter_upwards [hfin] with b hb
    exact ENNReal.ofReal_toReal hb
  have hG (k : ℕ) : ENNReal.ofReal (∫ b, A k b ∂μ) =
      ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) y)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hA k) (hAn k)]
    exact (GreenOccupation.lintegral_lqgClockApprox_exit_eq_occupation_and_green
      hD hx γ (dyadicScale k) (dyadicScale_pos k) hε (hcont k)).2
  refine ⟨hA, hL, ?_, ?_, ?_⟩
  · rw [← hE]
    exact ENNReal.ofReal_ne_top
  · intro k
    rw [← hG k]
    exact ENNReal.ofReal_ne_top
  · have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hint
    simpa only [Function.comp_def, hG, hE] using ht

end HarmonicBalls
