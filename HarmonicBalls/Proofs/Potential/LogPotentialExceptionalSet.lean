import HarmonicBalls.Proofs.Potential.GreenPotentialHolder
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Diagonal exceptional set for logarithmic potentials

The potential-theoretic infrastructure used here is due to Leonardo Bonanno.
The upper volume-growth estimate excludes atoms on bounded restrictions. Fubini
then removes the atoms of an arbitrary finite measure at almost every point.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- Upper volume growth excludes atoms on the bounded restriction. -/
theorem restrict_ball_singleton_eq_zero_of_upper {μ : Measure ℂ} {R r₀ β : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) (x : ℂ) :
    μ.restrict (ball 0 R) {x} = 0 := by
  by_cases hx : x ∈ closedBall (0 : ℂ) R
  · apply measure_singleton_eq_zero_of_le_rpow hβ
    intro r hr
    exact restrict_ball_closedBall_le hR hr₀ hβ hup hfin hx hr
  · rw [Measure.restrict_apply (measurableSet_singleton x)]
    have : ({x} ∩ ball (0 : ℂ) R) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have : y = x := hy.1
      subst y
      exact hx (ball_subset_closedBall hy.2)
    rw [this, measure_empty]

/-- A finite measure has no atom at almost every point of an atomless bounded restriction. -/
theorem ae_measure_singleton_eq_zero_of_upper {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    {R r₀ β : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) :
    ∀ᵐ x ∂μ.restrict (ball 0 R), ν {x} = 0 := by
  let ρ := μ.restrict (ball 0 R)
  have : IsFiniteMeasure ρ := isFiniteMeasure_restrict.2 hfin
  have hd : (ν.prod ρ) (Set.diagonal ℂ) = 0 := by
    apply Measure.measure_prod_null_of_ae_null measurableSet_diagonal
    filter_upwards [] with x
    simpa [Set.diagonal, ρ] using restrict_ball_singleton_eq_zero_of_upper hR hr₀ hβ hup hfin x
  have hd' : (ρ.prod ν) (Set.diagonal ℂ) = 0 := by
    rw [← Measure.prod_swap, Measure.map_apply measurable_swap measurableSet_diagonal]
    simpa [Set.diagonal, eq_comm] using hd
  have h := Measure.measure_ae_null_of_prod_null hd'
  filter_upwards [h] with x hx
  simpa [Set.diagonal] using hx

/-- Uniform integrability and a quantitative bound for the Riesz kernel on a bounded
restriction, uniformly over poles in the corresponding closed ball. -/
theorem riesz_integrable_restrict_ball_of_upper {μ : Measure ℂ} {R r₀ β : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) :
    Integrable (fun y => ‖x - y‖ ^ (-greenPotentialHolderExponent β)) (μ.restrict (ball 0 R)) ∧
    (∫ y, ‖x - y‖ ^ (-greenPotentialHolderExponent β) ∂μ.restrict (ball 0 R)) ≤
      greenPotentialRieszBound β r₀ (μ (ball (0 : ℂ) R)).toReal := by
  have hm : 0 ≤ (μ (ball (0 : ℂ) R)).toReal := ENNReal.toReal_nonneg
  have hν : μ.restrict (ball 0 R) univ ≤ ENNReal.ofReal (μ (ball (0 : ℂ) R)).toReal := by
    rw [Measure.restrict_apply_univ, ENNReal.ofReal_toReal hfin]
  apply integrable_norm_sub_rpow_neg (greenPotentialRieszBound_nonneg hβ hr₀ hm)
  exact lintegral_norm_sub_rpow_neg_le (greenPotentialHolderExponent_pos hβ)
    (greenPotentialHolderExponent_lt hβ) hm (volumeGrowthAllScalesConstant_nonneg hr₀ hm) hν
    (fun r hr => restrict_ball_closedBall_le hR hr₀ hβ hup hfin hx hr)

/-- Product integrability of the Riesz kernel for finite measures restricted to a
closed ball and a measure satisfying the upper growth bound on that ball. -/
theorem riesz_integrable_product_of_upper {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    {R r₀ β : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) :
    Integrable (fun p : ℂ × ℂ => ‖p.1 - p.2‖ ^ (-greenPotentialHolderExponent β))
      ((ν.restrict (closedBall 0 R)).prod (μ.restrict (ball 0 R))) := by
  have : IsFiniteMeasure (μ.restrict (ball 0 R)) := isFiniteMeasure_restrict.2 hfin
  let f : ℂ × ℂ → ℝ := fun p => ‖p.1 - p.2‖ ^ (-greenPotentialHolderExponent β)
  have hf : Measurable f := by fun_prop
  apply (integrable_prod_iff hf.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact (riesz_integrable_restrict_ball_of_upper hR hr₀ hβ hup hfin hx).1
  · apply Integrable.mono' (integrable_const (greenPotentialRieszBound β r₀
        (μ (ball (0 : ℂ) R)).toReal))
      (hf.norm.aestronglyMeasurable.integral_prod_right')
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    have hi := riesz_integrable_restrict_ball_of_upper hR hr₀ hβ hup hfin hx
    have hn : (fun y => ‖f (x, y)‖) = fun y => f (x, y) := by
      funext y
      simp only [f, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [hn, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y =>
      Real.rpow_nonneg (norm_nonneg _) _)]
    exact hi.2

#print axioms riesz_integrable_product_of_upper
#print axioms riesz_integrable_restrict_ball_of_upper
#print axioms restrict_ball_singleton_eq_zero_of_upper
#print axioms ae_measure_singleton_eq_zero_of_upper

end HarmonicBalls
