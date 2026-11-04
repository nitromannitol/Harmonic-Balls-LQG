import HarmonicBalls.Proofs.Sec8.CircleAverageBrownian
import HarmonicBalls.Steps.Sec11.ScaledBallNormalization
import Mathlib.Probability.Moments.MGFAnalytic

/-! # Circle-average tails on exponential scales

The radial circle-average process of a normalized whole-plane GFF is
pre-Brownian. A fixed Chernoff parameter yields a summable upper tail along
any shifted sequence of nonnegative logarithmic scales.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

/-- The upper tail along exponential radii is summable for every positive
linear threshold. -/
theorem IsWholePlaneGFF.tsum_circleAverage_exp_upper_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {s δ : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ) :
    (∑' n : ℕ, P {ω | δ * (n : ℝ) < hcirc ω (Real.exp (-(s + n))) 0}) ≠ ∞ := by
  let _ := hh.isProbabilityMeasure
  let q : ℝ := Real.exp (-(δ ^ 2) / 2)
  let C : ℝ := Real.exp (s * δ ^ 2 / 2)
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hδ)) (by norm_num)
  have hbound : ∀ n : ℕ,
      P {ω | δ * (n : ℝ) < hcirc ω (Real.exp (-(s + n))) 0} ≤
        ENNReal.ofReal C * ENNReal.ofReal q ^ n := by
    intro n
    let t : ℝ≥0 := ⟨s + (n : ℝ), by positivity⟩
    let X : Ω → ℝ := radialCircleAverage hcirc t
    have hlaw : HasLaw X (gaussianReal 0 t) P :=
      hh.radialCircleAverage_isPreBrownianReal.hasLaw_eval t
    have hint : Integrable (fun ω => Real.exp (δ * X ω)) P := by
      have h := integrable_exp_mul_gaussianReal (μ := 0) (v := t) δ
      rw [← hlaw.map_eq] at h
      exact (integrable_map_measure (by fun_prop) hlaw.aemeasurable).1 h
    have ht : P.real {ω | δ * (n : ℝ) ≤ X ω} ≤ C * q ^ n := by
      calc
        _ ≤ Real.exp (-δ * (δ * (n : ℝ))) * mgf X P δ :=
          measure_ge_le_exp_mul_mgf (δ * n) hδ.le hint
        _ = C * q ^ n := by
          have htc : (t : ℝ) = s + (n : ℝ) := rfl
          rw [mgf_gaussianReal hlaw, htc]
          dsimp [C, q]
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    calc
      _ ≤ P {ω | δ * (n : ℝ) ≤ X ω} := by
        apply measure_mono
        intro ω hω
        change δ * (n : ℝ) ≤ X ω
        exact le_of_lt (show δ * (n : ℝ) < X ω from hω)
      _ = ENNReal.ofReal (P.real {ω | δ * (n : ℝ) ≤ X ω}) := by
        rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal (C * q ^ n) := ENNReal.ofReal_le_ofReal ht
      _ = ENNReal.ofReal C * ENNReal.ofReal q ^ n := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow hq0.le]
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.2 (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hq1)).ne')

/-- A positive multiple of the circle average has a summable upper tail
whenever the linear threshold has positive slope. -/
theorem IsWholePlaneGFF.tsum_weighted_circleAverage_exp_upper_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {s ξ κ β : ℝ}
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hgap : β < κ) :
    (∑' n : ℕ, P {ω | (κ - β) * (n : ℝ) <
      ξ * hcirc ω (Real.exp (-(s + n))) 0}) ≠ ∞ := by
  have heq (n : ℕ) :
      {ω | (κ - β) * (n : ℝ) < ξ * hcirc ω (Real.exp (-(s + n))) 0} =
      {ω | ((κ - β) / ξ) * (n : ℝ) < hcirc ω (Real.exp (-(s + n))) 0} := by
    ext ω
    change (κ - β) * (n : ℝ) < ξ * hcirc ω (Real.exp (-(s + n))) 0 ↔
      (κ - β) / ξ * (n : ℝ) < hcirc ω (Real.exp (-(s + n))) 0
    rw [mul_comm ξ (hcirc ω (Real.exp (-(s + n))) 0), ← div_lt_iff₀ hξ]
    ring
  simp_rw [heq]
  exact hh.tsum_circleAverage_exp_upper_lt_top hs (div_pos (sub_pos.mpr hgap) hξ)

/-- The circle-average contribution to the scaled-ball criterion is
summable. The normalized local metric tail remains an explicit hypothesis. -/
theorem exists_scaled_ball_criterion_of_circleAverage_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hh : IsWholePlaneGFF P hC hcirc)
    (D E : Ω → ℂ → ℂ → ℝ) (A : Ω → ℝ≥0∞) (s ξ α β κ : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α) (hgap : ξ * α < β) (hκ : β < κ)
    (V : Set ℂ) (hball : ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hA : ∀ᵐ ω ∂P, A ω ≠ ∞)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ∀ p : ℕ → ℝ≥0∞, (∑' n, p n) ≠ ∞ →
        (∀ (n i : ℕ), i ≤ N →
          P {ω | ∃ x ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
            ∃ y ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
              A ω * ENNReal.ofReal (Real.exp (-κ * (n : ℝ) +
                ξ * hcirc ω (Real.exp (-(s + n))) 0)) <
                internalMetric (D ω)
                  (ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε)))
                  x y} ≤ p n) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_log_normalization P D E A s ξ α β κ
      hξ.le hα hgap V hball hD hE hDnonneg hEnonneg hA hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro p hp htail
  apply hcriterion (fun ω n _ => ξ * hcirc ω (Real.exp (-(s + n))) 0) p
    (fun n => P {ω | (κ - β) * (n : ℝ) < ξ * hcirc ω (Real.exp (-(s + n))) 0})
    hp (hh.tsum_weighted_circleAverage_exp_upper_lt_top hs hξ hκ) htail
  intro n i hi
  exact le_rfl

#print axioms IsWholePlaneGFF.tsum_weighted_circleAverage_exp_upper_lt_top
#print axioms exists_scaled_ball_criterion_of_circleAverage_tail

#print axioms IsWholePlaneGFF.tsum_circleAverage_exp_upper_lt_top

end HarmonicBalls
