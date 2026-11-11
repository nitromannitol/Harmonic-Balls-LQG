import HarmonicBalls.Proofs.GFF.CircleAverageLogRadiusFourthMoment
import HarmonicBalls.Proofs.GFF.CircleAverageGaussianTail
import Mathlib.Probability.Moments.SubGaussian

/-! # Sub-Gaussian log-radius circle-average increments

The centered Gaussian increment has variance exactly the distance between the
log radii. The tail estimate holds across the unit circle and for degenerate
increments. The import closure contains code by Leonardo Bonanno (LatticeProb).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Every fixed log-radius increment is measurable. -/
theorem IsWholePlaneGFF.measurable_logRadius_circle_increment
    (h : IsWholePlaneGFF P hC hcirc) (s t : ℝ) :
    Measurable (fun ω => hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0) :=
  (h.measurable_circle _ _ (Real.exp_pos s)).sub
    (h.measurable_circle _ _ (Real.exp_pos t))

/-- The two-sided threshold event is measurable, for every real threshold. -/
theorem IsWholePlaneGFF.measurableSet_logRadius_circle_increment_abs_ge
    (h : IsWholePlaneGFF P hC hcirc) (s t a : ℝ) :
    MeasurableSet {ω | a ≤ |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0|} :=
  measurableSet_le measurable_const (h.measurable_logRadius_circle_increment s t).abs

/-- The strict two-sided threshold event is measurable as well. -/
theorem IsWholePlaneGFF.measurableSet_logRadius_circle_increment_abs_gt
    (h : IsWholePlaneGFF P hC hcirc) (s t a : ℝ) :
    MeasurableSet {ω | a < |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0|} :=
  measurableSet_lt measurable_const (h.measurable_logRadius_circle_increment s t).abs

/-- Exact variance proxy for the log-radius increment, including zero variance. -/
theorem IsWholePlaneGFF.hasSubgaussianMGF_logRadius_circle_increment
    (h : IsWholePlaneGFF P hC hcirc) (s t : ℝ) :
    HasSubgaussianMGF (fun ω => hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0)
      (|s - t|).toNNReal P := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hlaw := h.logRadius_circle_increment_hasLaw s t
  constructor
  · intro u
    have hi := integrable_exp_mul_gaussianReal (μ := 0) (v := (|s - t|).toNNReal) u
    rw [← hlaw.map_eq] at hi
    exact (integrable_map_measure (by fun_prop) hlaw.aemeasurable).1 hi
  · intro u
    rw [mgf_gaussianReal hlaw]
    simp only [zero_mul, zero_add, le_refl]

/-- Gaussian two-sided tail with the exact log-radius variance. Lean's real
inverse convention makes the bound valid even when the variance is zero. -/
theorem IsWholePlaneGFF.measure_logRadius_circle_increment_abs_ge_le
    (h : IsWholePlaneGFF P hC hcirc) (s t : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    P {ω | a ≤ |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0|} ≤
      ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * |s - t|))) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let X : Ω → ℝ := fun ω => hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0
  have hg : HasSubgaussianMGF X (|s - t|).toNNReal P :=
    h.hasSubgaussianMGF_logRadius_circle_increment s t
  have hup := hg.measure_ge_le ha
  have hlow := hg.neg.measure_ge_le ha
  have hv : ((|s - t|).toNNReal : ℝ) = |s - t| := Real.coe_toNNReal _ (abs_nonneg _)
  rw [hv] at hup hlow
  have hsub : {ω | a ≤ |X ω|} ⊆ {ω | a ≤ X ω} ∪ {ω | a ≤ (-X) ω} := by
    intro ω hω
    rcases le_abs'.1 (show a ≤ |X ω| from hω) with hw | hw
    · exact Or.inr (by change a ≤ -X ω; linarith)
    · exact Or.inl hw
  calc
    P {ω | a ≤ |X ω|} ≤ P {ω | a ≤ X ω} + P {ω | a ≤ (-X) ω} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal (P.real {ω | a ≤ X ω}) +
        ENNReal.ofReal (P.real {ω | a ≤ (-X) ω}) := by
      rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(a ^ 2) / (2 * |s - t|))) +
        ENNReal.ofReal (Real.exp (-(a ^ 2) / (2 * |s - t|))) :=
      add_le_add (ENNReal.ofReal_le_ofReal hup) (ENNReal.ofReal_le_ofReal hlow)
    _ = ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / (2 * |s - t|))) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- For arbitrary real thresholds, the positive part gives the uniform tail bound. -/
theorem IsWholePlaneGFF.measure_logRadius_circle_increment_abs_ge_le_posPart
    (h : IsWholePlaneGFF P hC hcirc) (s t a : ℝ) :
    P {ω | a ≤ |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0|} ≤
      ENNReal.ofReal (2 * Real.exp (-((max a 0) ^ 2) / (2 * |s - t|))) := by
  have heq : {ω | a ≤ |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0|} =
      {ω | max a 0 ≤ |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, max_le_iff, abs_nonneg, and_true]
  rw [heq]
  exact h.measure_logRadius_circle_increment_abs_ge_le s t (le_max_right _ _)

/-- The same all-threshold estimate for the strict tail event. -/
theorem IsWholePlaneGFF.measure_logRadius_circle_increment_abs_gt_le
    (h : IsWholePlaneGFF P hC hcirc) (s t a : ℝ) :
    P {ω | a < |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0|} ≤
      ENNReal.ofReal (2 * Real.exp (-((max a 0) ^ 2) / (2 * |s - t|))) :=
  calc
    P {ω | a < |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0|} ≤
        P {ω | a ≤ |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0|} := by
      apply measure_mono
      intro ω hw
      exact le_of_lt (show a < |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp t) 0| from hw)
    _ ≤ _ := h.measure_logRadius_circle_increment_abs_ge_le_posPart s t a

/-- Strict positive thresholds have zero probability when the radii coincide. -/
theorem IsWholePlaneGFF.measure_logRadius_circle_increment_abs_gt_self
    (_h : IsWholePlaneGFF P hC hcirc) (s : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    P {ω | a < |hcirc ω (Real.exp s) 0 - hcirc ω (Real.exp s) 0|} = 0 := by
  simp only [sub_self, abs_zero, not_lt_of_ge ha, Set.ofPred_false, measure_empty]


end HarmonicBalls
