import HarmonicBalls.Proofs.Sec11.FixedSquareFrontierNull

/-!
# Moments of the circle-average lognormal prefactor

For a fixed positive radius at most one, the moments of the exponential of a
whole-plane GFF circle average are uniformly bounded over a fixed closed ball.
The variance depends on the centre; its upper bound is deterministic. The
import closure contains code by Leonardo Bonanno (LatticeProb).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

/-- A circle-average lognormal power is almost everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_circleAverage_lognormal_rpow
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {L : ℝ} (hL : 0 < L)
    (z : ℂ) (ξ q : ℝ) :
    AEMeasurable (fun ω => (Real.exp (ξ * hcirc ω L z)) ^ q) P := by
  have hG := hgff.hasGaussianLaw_circle hL z
  have heq : (fun ω => (Real.exp (ξ * hcirc ω L z)) ^ q) =
      (fun ω => Real.exp ((q * ξ) * hcirc ω L z)) := by
    funext ω
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [heq]
  exact (hG.aemeasurable.const_mul (q * ξ)).exp

/-- Every real power of a circle-average lognormal variable is integrable. -/
theorem IsWholePlaneGFF.integrable_circleAverage_lognormal_rpow
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {L : ℝ} (hL : 0 < L)
    (z : ℂ) (ξ q : ℝ) :
    Integrable (fun ω => (Real.exp (ξ * hcirc ω L z)) ^ q) P := by
  have hG := hgff.hasGaussianLaw_circle hL z
  have hm : ∫ ω, hcirc ω L z ∂P = 0 := hgff.integral_eq_zero (.circle L z) hL
  have hint := integrable_exp_mul_gaussianReal (μ := 0)
    (v := (Var[fun ω => hcirc ω L z; P]).toNNReal) (q * ξ)
  rw [← hm, ← hG.map_eq_gaussianReal] at hint
  have hint' := (integrable_map_measure (by fun_prop) hG.aemeasurable).1 hint
  convert hint' using 1
  funext ω
  rw [← Real.exp_mul]
  congr 1
  ring

/-- The ENNReal moment is given by the actual centre-dependent variance. -/
theorem IsWholePlaneGFF.lintegral_circleAverage_lognormal_rpow_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {L : ℝ} (hL : 0 < L)
    (z : ℂ) (ξ q : ℝ) :
    ∫⁻ ω, ENNReal.ofReal ((Real.exp (ξ * hcirc ω L z)) ^ q) ∂P =
      ENNReal.ofReal (Real.exp ((q * ξ)^2 * Var[fun ω => hcirc ω L z; P] / 2)) := by
  convert hgff.lintegral_exp_circleAverage_eq (q * ξ) hL z using 1
  congr 1
  funext ω
  rw [← Real.exp_mul]
  congr 1
  ring

/-- The deterministic moment bound is uniform in the centre in the closed
ball of radius `R`, for each fixed `L`, `ξ`, and moment order `q`. -/
theorem IsWholePlaneGFF.lintegral_circleAverage_lognormal_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {L R : ℝ}
    (hL : 0 < L) (hL1 : L ≤ 1) (hR : 0 ≤ R) (ξ q : ℝ)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ∫⁻ ω, ENNReal.ofReal ((Real.exp (ξ * hcirc ω L z)) ^ q) ∂P ≤
      ENNReal.ofReal (Real.exp ((q * ξ)^2 * (2 * Real.log (R + 1) - Real.log L) / 2)) := by
  have hzn : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hA := circleAverage_wholePlaneNormalization_le hR hzn hL hL1
  have hV : Var[fun ω => hcirc ω L z; P] ≤ 2 * Real.log (R + 1) - Real.log L := by
    rw [hgff.variance_circleAverage_eq hL z]
    linarith
  rw [hgff.lintegral_circleAverage_lognormal_rpow_eq hL z ξ q]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hV (sq_nonneg (q * ξ))
  linarith

/-- A threshold event is measurable in the completion of the field law. -/
theorem IsWholePlaneGFF.nullMeasurableSet_circleAverage_lognormal_gt
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {L : ℝ} (hL : 0 < L)
    (z : ℂ) (ξ t : ℝ) :
    NullMeasurableSet {ω | t < Real.exp (ξ * hcirc ω L z)} P := by
  have h := hgff.aemeasurable_circleAverage_lognormal_rpow hL z ξ 1
  simp only [Real.rpow_one] at h
  exact nullMeasurableSet_lt aemeasurable_const h

/-- A uniform Markov estimate for the circle-average lognormal prefactor. -/
theorem IsWholePlaneGFF.measure_circleAverage_lognormal_gt_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {L R : ℝ}
    (hL : 0 < L) (hL1 : L ≤ 1) (hR : 0 ≤ R) (ξ : ℝ)
    {q t : ℝ} (hq : 0 < q) (ht : 0 < t)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    P {ω | t < Real.exp (ξ * hcirc ω L z)} ≤
      ENNReal.ofReal (Real.exp ((q * ξ)^2 * (2 * Real.log (R + 1) - Real.log L) / 2)) /
        ENNReal.ofReal (t ^ q) := by
  have htq : 0 < t ^ q := Real.rpow_pos_of_pos ht q
  have hmarkov := meas_ge_le_lintegral_div
    (hgff.aemeasurable_circleAverage_lognormal_rpow hL z ξ q).ennreal_ofReal
    ((ENNReal.ofReal_pos.mpr htq).ne') ENNReal.ofReal_ne_top
  have hsub : {ω | t < Real.exp (ξ * hcirc ω L z)} ⊆
      {ω | ENNReal.ofReal (t ^ q) ≤ ENNReal.ofReal ((Real.exp (ξ * hcirc ω L z)) ^ q)} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ht.le hω.le hq.le)
  refine (measure_mono hsub).trans (hmarkov.trans ?_)
  gcongr
  exact hgff.lintegral_circleAverage_lognormal_rpow_le hL hL1 hR ξ q hz

#print axioms IsWholePlaneGFF.nullMeasurableSet_circleAverage_lognormal_gt
#print axioms IsWholePlaneGFF.measure_circleAverage_lognormal_gt_le
#print axioms IsWholePlaneGFF.aemeasurable_circleAverage_lognormal_rpow
#print axioms IsWholePlaneGFF.integrable_circleAverage_lognormal_rpow
#print axioms IsWholePlaneGFF.lintegral_circleAverage_lognormal_rpow_eq
#print axioms IsWholePlaneGFF.lintegral_circleAverage_lognormal_rpow_le

end HarmonicBalls
