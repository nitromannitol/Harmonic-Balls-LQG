import HarmonicBalls.Proofs.Potential.LQGApproxFiniteBallMass
import HarmonicBalls.Proofs.GFF.LQGMeasureContinuumConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Ball bounds over compact smoothing intervals

Joint continuity of circle averages gives quadratic ball bounds when the
regularization scale stays in a compact interval of positive radii.
-/

open MeasureTheory Filter Set Metric

namespace HarmonicBalls

/-- A jointly continuous circle profile gives a common quadratic ball bound
for singular approximations over any compact interval of positive scales. -/
theorem singular_approximant_ball_bound_of_continuousOn
    (γ α : ℝ) (h : ℝ → ℂ → ℝ)
    (hc : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Ioi 0 ×ˢ univ))
    {a b : ℝ} (ha : 0 < a) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc a b, ∀ z : ℂ, ‖z‖ ≤ R →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        lqgApprox γ (fieldCircleAverage α h) t (ball z r) ≤
          ENNReal.ofReal (C * r ^ 2) := by
  let K : Set (ℝ × ℂ) := Icc a b ×ˢ closedBall (0 : ℂ) (R + 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKpos : K ⊆ Ioi (0 : ℝ) ×ˢ univ := by
    intro p hp
    exact ⟨lt_of_lt_of_le ha hp.1.1, mem_univ _⟩
  have ht : ContinuousOn (fun p : ℝ × ℂ => p.1 ^ (γ ^ 2 / 2)) K :=
    continuous_fst.continuousOn.rpow_const fun p hp => Or.inl (ne_of_gt (hKpos hp).1)
  have hm : ContinuousOn (fun p : ℝ × ℂ => Real.log (max p.1 ‖p.2‖)) K := by
    apply ((continuous_fst.max (continuous_norm.comp continuous_snd)).continuousOn).log
    intro p hp
    exact ne_of_gt (lt_max_of_lt_left (hKpos hp).1)
  have hd : ContinuousOn (fun p : ℝ × ℂ =>
      p.1 ^ (γ ^ 2 / 2) * Real.exp (γ * (h p.1 p.2 - α * Real.log (max p.1 ‖p.2‖)))) K :=
    ht.mul (Real.continuous_exp.continuousOn.comp
      (continuousOn_const.mul ((hc.mono hKpos).sub (continuousOn_const.mul hm)))
      (fun _ _ => mem_univ _))
  obtain ⟨B, hB⟩ := hK.bddAbove_image hd
  let A := max 1 B
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨A * Real.pi, mul_pos hA Real.pi_pos, ?_⟩
  intro t ht z hz r hr hr1
  have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
  have hsub : ball z r ⊆ closedBall (0 : ℂ) (R + 1) := by
    apply Set.Subset.trans (Metric.ball_subset_ball' ?_) Metric.ball_subset_closedBall
    simpa only [dist_zero_right, add_comm] using add_le_add hr1 hz
  have hv : volume (ball z r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  calc
    lqgApprox γ (fieldCircleAverage α h) t (ball z r) ≤
        ENNReal.ofReal A * volume (ball z r) := by
      rw [lqgApprox, withDensity_apply _ isOpen_ball.measurableSet]
      calc
        (∫⁻ w in ball z r, ENNReal.ofReal
          (t ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage α h t w))) ≤
            ∫⁻ _w in ball z r, ENNReal.ofReal A := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with w hw
          apply ENNReal.ofReal_le_ofReal
          have hmem : (t, w) ∈ K := ⟨ht, hsub hw⟩
          have hbd := (hB ⟨(t, w), hmem, rfl⟩).trans (le_max_right 1 B)
          have hcircle := LatticeProb.Gauss.circleAverage_log_norm_sub_eq_log_max ht0 w 0
          simp only [sub_zero] at hcircle
          simpa only [fieldCircleAverage, hcircle, A] using hbd
        _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
    _ = ENNReal.ofReal ((A * Real.pi) * r ^ 2) := by
      rw [hv, ← ENNReal.ofReal_mul hA.le]
      congr 1
      ring

/-- For one whole-plane field event, compact intervals of positive smoothing
scales have common quadratic ball bounds on each bounded set of centers. -/
theorem IsWholePlaneGFF.ae_singular_approximant_compact_scale_ball_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (γ α : ℝ) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 < a → ∀ R : ℝ, ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ Icc a b, ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) t (ball z r) ≤
          ENNReal.ofReal (C * r ^ 2) := by
  filter_upwards [hh.ae_continuousOn_circle] with ω hω a b ha R
  exact singular_approximant_ball_bound_of_continuousOn γ α (hcirc ω) hω ha R

end HarmonicBalls
