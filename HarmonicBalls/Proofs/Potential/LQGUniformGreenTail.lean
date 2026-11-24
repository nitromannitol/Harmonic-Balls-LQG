import HarmonicBalls.Proofs.Potential.LQGGMCGreenIntegralLimit
import HarmonicBalls.Proofs.Potential.LQGSingularContinuumBallPower
import HarmonicBalls.Proofs.Potential.LQGActualLimitBallPower

/-!
# Uniform local Green integrals for singular LQG

A local power bound on ball masses controls the Green kernel near its pole.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal
open LatticeProb.LQG LatticeProb.Gauss

namespace HarmonicBalls

/-- Local polynomial mass growth implies a quantitative Green bound. -/
theorem green_integral_ball_le_of_local_mass_growth {O : Set ℂ} {R C β r₀ r : ℝ}
    (hO : IsOpen O) (hR : 0 < R) (hOR : O ⊆ ball (0 : ℂ) R)
    (hC : 0 < C) (hβ : 0 < β) (hr₀ : 0 < r₀)
    (x : ℂ) (ν : Measure ℂ)
    (hball : ∀ t, 0 < t → t < r₀ → ν (ball x t) ≤ ENNReal.ofReal (C * t ^ β))
    (hr : 0 < r) (hrd : r ≤ r₀ / 4) :
    IntegrableOn (greenFunction O x) (ball x r) ν ∧
      (∫ y in ball x r, greenFunction O x y ∂ν) ≤
        ((2 * Real.pi)⁻¹ * ((β / 4)⁻¹ * (2 * R) ^ (β / 4))) * r ^ (β / 4) *
          (C * (r₀ / 4) ^ β + (C * ((2 : ℝ) ^ β + 1)) *
            ((2 * (β / 4)) / (β - 2 * (β / 4)))) := by
  let d : ℝ := r₀ / 4
  let A : ℝ := C * ((2 : ℝ) ^ β + 1)
  let m : ℝ := C * d ^ β
  have hd : 0 < d := by dsimp [d]; positivity
  have hd₀ : d < r₀ := by dsimp [d]; linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hmass : ν.restrict (ball x d) univ ≤ ENNReal.ofReal m := by
    rw [Measure.restrict_apply_univ]
    exact hball d hd hd₀
  have hballs : ∀ t, 0 < t → ν.restrict (ball x d) (closedBall x t) ≤
      ENNReal.ofReal (A * t ^ β) := by
    intro t ht
    by_cases htd : t < d
    · have ht₂ : 2 * t < r₀ := by dsimp [d] at htd; linarith
      calc ν.restrict (ball x d) (closedBall x t) ≤ ν (ball x (2 * t)) := by
            exact ((Measure.restrict_le_self : ν.restrict (ball x d) ≤ ν) _).trans
              (measure_mono (closedBall_subset_ball (by linarith)))
        _ ≤ ENNReal.ofReal (C * (2 * t) ^ β) := hball _ (by positivity) ht₂
        _ ≤ ENNReal.ofReal (A * t ^ β) := by
            apply ENNReal.ofReal_le_ofReal
            rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2) ht.le]
            dsimp [A]
            have hp : 0 ≤ t ^ β := Real.rpow_nonneg ht.le _
            nlinarith [mul_nonneg hC.le hp]
    · have hdt : d ≤ t := le_of_not_gt htd
      calc ν.restrict (ball x d) (closedBall x t) ≤ ν.restrict (ball x d) univ :=
            measure_mono (subset_univ _)
        _ ≤ ENNReal.ofReal m := hmass
        _ ≤ ENNReal.ofReal (A * t ^ β) := by
            apply ENNReal.ofReal_le_ofReal
            have hp : d ^ β ≤ t ^ β := Real.rpow_le_rpow hd.le hdt hβ.le
            have htβ : 0 ≤ t ^ β := Real.rpow_nonneg ht.le _
            dsimp [m, A]
            nlinarith [mul_nonneg hC.le htβ,
              mul_nonneg (Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) β) (mul_nonneg hC.le htβ)]
  have h := green_integral_ball_le_of_mass_growth hO hR hOR
    (show 0 < β / 4 by positivity) (show 2 * (β / 4) < β by linarith)
    hA hm hr x (ν.restrict (ball x d)) hmass hballs
  have hsub : ball x r ⊆ ball x d := ball_subset_ball hrd
  have heq : (ν.restrict (ball x d)).restrict (ball x r) = ν.restrict (ball x r) := by
    rw [Measure.restrict_restrict measurableSet_ball, inter_eq_left.mpr hsub]
  change Integrable (greenFunction O x) ((ν.restrict (ball x d)).restrict (ball x r)) ∧
    (∫ y, greenFunction O x y ∂((ν.restrict (ball x d)).restrict (ball x r))) ≤ _ at h
  rw [heq] at h
  exact h


/-- The actual singular measure and all continuum approximations have a common
small-ball Green bound on every bounded disk. -/
theorem IsWholePlaneGFF.ae_singular_green_integral_ball_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∃ K a r₀ : ℝ, 0 < K ∧ 0 < a ∧ 0 < r₀ ∧
      ∀ O : Set ℂ, IsOpen O → O ⊆ ball (0 : ℂ) R →
      ∀ x : ℂ, ‖x‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ r₀ →
        (IntegrableOn (greenFunction O x) (ball x r) (μ ω) ∧
          (∫ y in ball x r, greenFunction O x y ∂(μ ω)) ≤ K * r ^ a) ∧
        ∀ s : ℝ, 0 < s → s ≤ 1 →
          IntegrableOn (greenFunction O x) (ball x r)
            (lqgApprox γ (fieldCircleAverage α (hcirc ω)) s) ∧
          (∫ y in ball x r, greenFunction O x y ∂
            (lqgApprox γ (fieldCircleAverage α (hcirc ω)) s)) ≤ K * r ^ a := by
  filter_upwards [hh.ae_singular_continuum_small_ball_power_all_disks hγ hγ2 hαQ, hμ] with ω hb hlim R hR
  obtain ⟨C, β, d, hC, hβ, hd, hb⟩ := hb R
  let M : ℝ := C * (d / 4) ^ β + (C * ((2 : ℝ) ^ β + 1)) *
    ((2 * (β / 4)) / (β - 2 * (β / 4)))
  let D : ℝ := ((2 * Real.pi)⁻¹ * ((β / 4)⁻¹ * (2 * R) ^ (β / 4)))
  have hden : 0 < β - 2 * (β / 4) := by linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D * M + 1, β / 4, d / 4, by positivity, by positivity, by positivity, ?_⟩
  intro O hO hOR x hx r hr hrd
  have hvague : QuantumZipper.IsVagueLimitOn univ (fun k =>
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)) (μ ω) := by
    refine ⟨by simp, fun S hS _ => ?_, fun f hf hfc _ => hlim.tendsto_integral f hf hfc⟩
    let _ := hlim.isLocallyFiniteMeasure
    exact hS.measure_lt_top
  have hlimit : ∀ t, 0 < t → t < d → μ ω (ball x t) ≤ ENNReal.ofReal (C * t ^ β) := by
    intro t ht htd
    apply LatticeProb.LQG.measure_open_le_of_isVagueLimitOn hvague isOpen_ball isBounded_ball
    · refine ⟨x + (t + 1 : ℝ), ?_⟩
      simp only [mem_compl_iff, mem_ball, dist_eq_norm, add_sub_cancel_left,
        Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ t + 1 by linarith), not_lt]
      linarith
    · intro k
      exact hb x hx t ht htd (dyadicScale k) (dyadicScale_pos_bracket k) (dyadicScale_le_one' k)
  have hreduce (ν : Measure ℂ)
      (hν : ∀ t, 0 < t → t < d → ν (ball x t) ≤ ENNReal.ofReal (C * t ^ β)) :
      IntegrableOn (greenFunction O x) (ball x r) ν ∧
        (∫ y in ball x r, greenFunction O x y ∂ν) ≤ (D * M + 1) * r ^ (β / 4) := by
    obtain ⟨hi, hbnd⟩ := green_integral_ball_le_of_local_mass_growth hO hR hOR hC hβ hd x ν hν hr hrd
    refine ⟨hi, hbnd.trans ?_⟩
    have hp : 0 ≤ r ^ (β / 4) := Real.rpow_nonneg hr.le _
    change D * r ^ (β / 4) * M ≤ (D * M + 1) * r ^ (β / 4)
    nlinarith [mul_nonneg hD (mul_nonneg hp hM)]
  exact ⟨hreduce (μ ω) hlimit, fun s hs hs1 =>
    hreduce (lqgApprox γ (fieldCircleAverage α (hcirc ω)) s)
      (fun t ht htd => hb x hx t ht htd s hs hs1)⟩

end HarmonicBalls
