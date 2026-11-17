import HarmonicBalls.Proofs.Potential.LQGActualLimitBallPower
import HarmonicBalls.Proofs.Potential.GreenPotentialHolder

/-! # Green potentials of singular LQG measures on discs

The actual singular measure has Hölder Green potentials on every disc centered
at the origin, on one event simultaneously for all radii and densities.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A constant in a small-ball power bound can be absorbed by decreasing the exponent. -/
theorem small_ball_power_absorb_constant {μ : Measure ℂ} {R C β r₀ : ℝ}
    (hC : 0 < C) (hβ : 0 < β) (hr₀ : 0 < r₀)
    (hb : ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ r₀ →
      μ (ball z r) ≤ ENNReal.ofReal (C * r ^ β)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r, 0 < r → r < δ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ (β / 2)) := by
  have hcont : ContinuousAt (fun r : ℝ => r ^ (β / 2)) 0 :=
    Real.continuousAt_rpow_const 0 (β / 2) (Or.inr (by positivity))
  have hzero : (0 : ℝ) ^ (β / 2) = 0 := Real.zero_rpow (by positivity)
  obtain ⟨d, hd, hsmall⟩ := Metric.continuousAt_iff.mp hcont (1 / C) (by positivity)
  refine ⟨min d r₀, lt_min hd hr₀, ?_⟩
  intro r hr hrd z hz
  have hr_d : r < d := lt_of_lt_of_le hrd (min_le_left _ _)
  have hr_r₀ : r ≤ r₀ := (lt_of_lt_of_le hrd (min_le_right _ _)).le
  have hp : r ^ (β / 2) < 1 / C := by
    have h := hsmall (x := r) (by simpa [Real.dist_eq, abs_of_pos hr] using hr_d)
    rw [Real.dist_eq, hzero, sub_zero, abs_of_nonneg (Real.rpow_nonneg hr.le _)] at h
    exact h
  have hmul : C * r ^ (β / 2) ≤ 1 := by
    have := (lt_div_iff₀ hC).mp hp
    nlinarith
  have hpow : r ^ β = r ^ (β / 2) * r ^ (β / 2) := by
    rw [← Real.rpow_add hr]
    congr 1; ring
  refine (hb z (mem_ball_zero_iff.mp hz).le r hr hr_r₀).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [hpow]
  nlinarith [Real.rpow_nonneg hr.le (β / 2)]

/-- On one event, every origin-centered disc has Hölder Green potentials for
bounded densities with respect to the actual singular measure. -/
theorem IsWholePlaneGFF.ae_singular_greenPotential_ball_holder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ f : ℂ → ℝ,
      MemLp f ⊤ ((μ ω).restrict (closedBall 0 R)) →
      (∀ x ∈ closedBall (0 : ℂ) R,
        IntegrableOn (fun y => greenFunction (ball 0 R) x y * f y) (ball 0 R) (μ ω)) ∧
      ∃ C r : ℝ≥0, 0 < r ∧ HolderOnWith C r
        (fun x => ∫ y in ball 0 R, greenFunction (ball 0 R) x y * f y ∂(μ ω))
        (closedBall 0 R) := by
  filter_upwards [hh.ae_singular_limit_and_approximant_ball_power hγ hγ2 hαQ hμ, hμ] with ω hb hlim
  let _ := hlim.isLocallyFiniteMeasure
  intro R hR f hf
  obtain ⟨C, β, r₀, hC, hβ, hr₀, hb⟩ := hb R
  obtain ⟨δ, hδ, hup⟩ := small_ball_power_absorb_constant hC hβ hr₀
    (fun z hz r hr hrr => (hb z hz r hr hrr).1)
  set M := (eLpNorm f ⊤ ((μ ω).restrict (closedBall 0 R))).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hfM' : ∀ᵐ y ∂(μ ω).restrict (closedBall 0 R), |f y| ≤ M := by
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := (μ ω).restrict (closedBall 0 R))] with y hy
    rw [Real.enorm_eq_ofReal_abs] at hy
    exact (ENNReal.ofReal_le_iff_le_toReal hf.ne).1 (hy.trans eLpNormEssSup_le_eLpNorm_top)
  have hfM : ∀ᵐ y ∂(μ ω).restrict (ball 0 R), |f y| ≤ M :=
    ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hfM'
  obtain ⟨hI, hD⟩ := greenPotential_ball_holder_of_upper hR hδ (show 0 < β / 2 by positivity)
    hup measure_ball_lt_top.ne (hf.aestronglyMeasurable.mono_set ball_subset_closedBall) hM hfM
  refine ⟨hI, ⟨greenPotentialHolderConstant (β / 2) δ ((μ ω) (ball 0 R)).toReal * M,
    mul_nonneg (greenPotentialHolderConstant_nonneg (by positivity) hδ ENNReal.toReal_nonneg) hM⟩,
    ⟨greenPotentialHolderExponent (β / 2), (greenPotentialHolderExponent_pos (show 0 < β / 2 by positivity)).le⟩,
    greenPotentialHolderExponent_pos (show 0 < β / 2 by positivity),
    holderOnWith_of_dist_le fun x hx x' hx' => ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  exact hD x hx x' hx'

end HarmonicBalls
