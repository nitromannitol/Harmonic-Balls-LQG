import HarmonicBalls.Steps.Sec11.ExponentialCircleAverageTail
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Normalized internal-diameter moments

Markov's inequality turns a uniform first moment of a nonnegative
normalizing variable into summable local metric tail estimates. The moment
and pointwise diameter bounds are explicit assumptions.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- A uniform first moment yields a geometric upper tail. -/
theorem measure_exp_threshold_le_of_lintegral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ≥0∞)
    (C : ℝ≥0∞) (a : ℝ) (n : ℕ) (hX : AEMeasurable X P)
    (hC : (∫⁻ ω, X ω ∂P) ≤ C) :
    P {ω | ENNReal.ofReal (Real.exp (a * n)) ≤ X ω} ≤
      C * ENNReal.ofReal (Real.exp (-a)) ^ n := by
  have ht0 : ENNReal.ofReal (Real.exp (a * n)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  calc
    _ ≤ (∫⁻ ω, X ω ∂P) / ENNReal.ofReal (Real.exp (a * n)) :=
      meas_ge_le_lintegral_div hX ht0 ENNReal.ofReal_ne_top
    _ ≤ C / ENNReal.ofReal (Real.exp (a * n)) := by gcongr
    _ = C * ENNReal.ofReal (Real.exp (-a)) ^ n := by
      rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg,
        ← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
      congr 2
      ring

/-- Exceeding a decaying normalized-distance threshold forces a corresponding
exponential exceedance of the nonnegative normalization variable. -/
theorem internalMetric_exceedance_subset_exp_threshold
    {Ω : Type*} (D : Ω → ℂ → ℂ → ℝ) (H : Ω → ℝ) (X : Ω → ℝ≥0∞)
    (K W : Set ℂ) (η κ : ℝ) (n : ℕ)
    (hbound : ∀ ω, ∀ x ∈ K, ∀ y ∈ K,
      internalMetric (D ω) W x y ≤
        ENNReal.ofReal (Real.exp (-η * (n : ℝ) + H ω)) * X ω) :
    {ω | ∃ x ∈ K, ∃ y ∈ K,
      ENNReal.ofReal (Real.exp (-κ * (n : ℝ) + H ω)) < internalMetric (D ω) W x y} ⊆
    {ω | ENNReal.ofReal (Real.exp ((η - κ) * (n : ℝ))) ≤ X ω} := by
  intro ω ⟨x, hx, y, hy, hxy⟩
  have hprod : ENNReal.ofReal (Real.exp (-η * (n : ℝ) + H ω)) *
      ENNReal.ofReal (Real.exp ((η - κ) * (n : ℝ))) =
      ENNReal.ofReal (Real.exp (-κ * (n : ℝ) + H ω)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  have hle := le_trans (le_of_lt hxy) (hbound ω x hx y hy)
  rw [← hprod] at hle
  have hpos : ENNReal.ofReal (Real.exp (-η * (n : ℝ) + H ω)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have htop : ENNReal.ofReal (Real.exp (-η * (n : ℝ) + H ω)) ≠ ∞ := ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_left hpos htop).1
  simpa only [mul_comm] using hle

/-- Uniform first moments of normalized local distance bounds yield the
summable tail needed for logarithmic Weyl puncture removal. -/
theorem exists_scaled_ball_criterion_of_normalized_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hh : IsWholePlaneGFF P hC hcirc)
    (D E : Ω → ℂ → ℂ → ℝ) (s ξ α β κ η : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α)
    (hgap : ξ * α < β) (hκ : β < κ) (hη : κ < η)
    (V : Set ℂ) (hball : ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ∀ (X : ℕ → ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞), C ≠ ∞ →
        (∀ (n i : ℕ), i ≤ N → AEMeasurable (X n i) P) →
        (∀ (n i : ℕ), i ≤ N → (∫⁻ ω, X n i ω ∂P) ≤ C) →
        (∀ (n i : ℕ), i ≤ N → ∀ ω,
          ∀ x ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
          ∀ y ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
            internalMetric (D ω)
              (ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε))) x y ≤
              ENNReal.ofReal (Real.exp (-η * (n : ℝ) +
                ξ * hcirc ω (Real.exp (-(s + n))) 0)) * X n i ω) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_circleAverage_tail P hC hcirc hh D E (fun _ => 1)
      s ξ α β κ hs hξ hα hgap hκ V hball hD hE hDnonneg hEnonneg
      (Filter.Eventually.of_forall (fun _ => ENNReal.one_ne_top)) hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro X C hCfin hmeas hmoment hbound
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(η - κ)))
  have hq : q < 1 := by
    apply ENNReal.ofReal_lt_one.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hsum : (∑' n : ℕ, C * q ^ n) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top hCfin (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hq).ne')
  apply hcriterion (fun n => C * q ^ n) hsum
  intro n i hi
  calc
    _ ≤ P {ω | ENNReal.ofReal (Real.exp ((η - κ) * (n : ℝ))) ≤ X n i ω} := by
      apply measure_mono
      simpa only [one_mul] using internalMetric_exceedance_subset_exp_threshold D
        (fun ω => ξ * hcirc ω (Real.exp (-(s + n))) 0) (X n i) _ _ η κ n (hbound n i hi)
    _ ≤ C * q ^ n := measure_exp_threshold_le_of_lintegral_le P (X n i) C
      (η - κ) n (hmeas n i hi) (hmoment n i hi)

#print axioms exists_scaled_ball_criterion_of_normalized_moments

#print axioms measure_exp_threshold_le_of_lintegral_le
#print axioms internalMetric_exceedance_subset_exp_threshold

end HarmonicBalls
