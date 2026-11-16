import HarmonicBalls.Proofs.Potential.LBMExitApproximation
import HarmonicBalls.Proofs.Potential.LQGClockApproxOccupation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Lower bound for expected Liouville exit times

The expected exit time is bounded by the lower limit of the Green integrals
of the regularized clock densities.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- The expected time-changed exit is at most the lower limit of the
finite-scale Green integrals. -/
theorem expectedLBMExitTime_le_liminf_clockApprox_green
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {D : Set ℂ}
    (hD : IsSmoothBoundedOpen D) (hx : x ∈ D)
    (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k)))
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b)) :
    expectedLBMExitTime F D x ≤ liminf (fun k : ℕ =>
      ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) y))) atTop := by
  let μ := planarBrownianMotion x
  let A : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    lqgClockApprox γ hε (dyadicScale k) b (ContinuousPath.exitTime D b).toNNReal
  let E : ℕ → ℝ≥0∞ := fun k => ∫⁻ b, ENNReal.ofReal (A k b) ∂μ
  have hDo : IsOpen D := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  have hmeas (k : ℕ) : Measurable (A k) := by
    let g : ℂ → ℝ := fun y => dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) y)
    have hg : Continuous g := continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hcont k)))
    simpa only [A, lqgClockApprox, g, SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional, Function.comp_def, id_eq] using
      (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional_joint hg.measurable).measurable.comp
        ((ContinuousPath.measurable_exitTime D hDo).ennreal_toNNReal.prodMk measurable_id)
  have hconv : TendstoInMeasure μ A atTop (fun b => (lbmExitTime F D b).toReal) := by
    apply tendstoInMeasure_iff_dist.mpr
    intro η hη
    simpa only [A, μ, Real.dist_eq] using
      hclock.tendsto_measure_clockApprox_lbmExitTime hDo hD.1 hF hη
  obtain ⟨s, hsE, hs⟩ := exists_seq_tendsto_liminf (u := E) (f := (atTop : Filter ℕ))
  obtain ⟨t, ht, hpoint⟩ := (hconv.comp hs).exists_seq_tendsto_ae
  have hfin : ∀ᵐ b ∂μ, lbmExitTime F D b ≠ ⊤ := by
    filter_upwards [hF, Section6.ae_planarBrownian_exitTime_bounded_lt_top x hD.1] with b hb hτ
    rw [lbmExitTime_eq_clockValue hDo hb hτ.ne]
    exact ENNReal.coe_ne_top
  have hlim : ∀ᵐ b ∂μ, Tendsto (fun n => ENNReal.ofReal (A (s (t n)) b)) atTop
      (𝓝 (lbmExitTime F D b)) := by
    filter_upwards [hpoint, hfin] with b hb hbfin
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hb
    simpa only [Function.comp_def, ENNReal.ofReal_toReal hbfin] using h
  calc
    expectedLBMExitTime F D x = ∫⁻ b, liminf (fun n => ENNReal.ofReal (A (s (t n)) b)) atTop ∂μ := by
      unfold expectedLBMExitTime
      apply lintegral_congr_ae
      filter_upwards [hlim] with b hb
      exact hb.liminf_eq.symm
    _ ≤ liminf (fun n => E (s (t n))) atTop :=
      lintegral_liminf_le fun n => (hmeas (s (t n))).ennreal_ofReal
    _ = liminf E atTop := (hsE.comp ht.tendsto_atTop).liminf_eq
    _ = _ := by
      congr 1
      funext k
      exact (GreenOccupation.lintegral_lqgClockApprox_exit_eq_occupation_and_green
        hD hx γ (dyadicScale k) (dyadicScale_pos k) hε (hcont k)).2

end HarmonicBalls
