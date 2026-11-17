import HarmonicBalls.Proofs.Potential.LQGClockFullInnerExpectation
import HarmonicBalls.Proofs.Potential.LQGClockCutoffGluing

/-! # Expected removal of a half-disc clock cutoff

The inner occupation estimate controls the uniform clock error as the cutoff
shrinks.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The product-law expected uniform error from an inner cutoff vanishes over
all dyadic smoothing scales on the unit time interval. -/
theorem tendsto_lintegral_iSup_halfDisc_annularClock_error_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq1 : γ*α < 1) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2*(1-γ*α)) :
    Tendsto (fun n : ℕ => ∫⁻ q : Ω × ContinuousPath ℂ,
      (⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal
        (dist (stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)) 0
              (fun _ => t.1.toNNReal) q.2)
          (stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z))
              ((2 : ℝ)⁻¹ ^ (n+2)) (fun _ => t.1.toNNReal) q.2)))
      ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have heq (n : ℕ) : (∫⁻ q : Ω × ContinuousPath ℂ,
      (⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal
        (dist (stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)) 0
              (fun _ => t.1.toNNReal) q.2)
          (stoppedAnnularClock (fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z))
              ((2 : ℝ)⁻¹ ^ (n+2)) (fun _ => t.1.toNNReal) q.2)))
      ∂(P.prod (planarBrownianMotion x))) =
      ∫⁻ q : Ω × ContinuousPath ℂ, (⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x)) := by
    apply lintegral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hcont,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_recentered_inserted_circle_average hh α)] with q hc hr
    congr 1
    funext i
    congr 1
    funext t
    let D : ℂ → ℝ := fun z => (dyadicScale (i+1))^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z)
    have he : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z) =
        fun z => hcirc q.1 (dyadicScale (i+1)) z - hcirc q.1 1 0 - α * Real.log (max (dyadicScale (i+1)) ‖z‖) := by
      funext z
      exact (hr (dyadicScale (i+1)) z (dyadicScale_pos _)).symm
    have hD : Continuous D := by
      have hi : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (i+1)) z) := by
        rw [he]
        exact ((hc _ (dyadicScale_pos _)).sub continuous_const).sub (continuous_const.mul
          ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (dyadicScale_pos _)).ne')))
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hi))
    have hD0 (z : ℂ) : 0 ≤ D z :=
      mul_nonneg (Real.rpow_nonneg (dyadicScale_pos _).le _) (Real.exp_pos _).le
    simpa only [D, dyadicScale] using
      ofReal_dist_halfDisc_annularClock_eq_inner q.2 D hD hD0 ((2 : ℝ)⁻¹ ^ (n+2)) t
  simp_rw [heq]
  exact tendsto_lintegral_iSup_time_inner_inserted_zero hh x hq0 hq1 hγ hsub

end HarmonicBalls
