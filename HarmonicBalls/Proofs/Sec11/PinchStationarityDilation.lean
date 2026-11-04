import HarmonicBalls.Steps.Sec11.PinchMetricDilation
import HarmonicBalls.Steps.Sec11.PinchMetricMeasure

/-! # Pinch stationarity from a joint metric-measure scaling law -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

open Classical in
/-- A joint scaling law for the metric and measure implies stationarity of the
strengthened pinch indicators. The normalizing factors may be random and need
not be measurable separately. The joint scaling law and the length-metric
property under the observation law are explicit hypotheses. -/
theorem identDistrib_pinchIndicators_of_normalized_dilation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (a : Ω → ℝ≥0∞) (c : Ω → ℝ)
    (ha : ∀ᵐ ω ∂P, a ω ≠ 0 ∧ a ω ≠ ∞ ∧ 0 < c ω)
    (hmetric : ∀ᵐ v ∂P.map (fun ω => (μ ω, D ω)), IsEuclideanLengthMetric v.2)
    (hscaling : IdentDistrib (fun ω => (μ ω, D ω))
      (fun ω => (a ω • (μ ω).map (fun x : ℂ => (2 : ℝ) • x),
        fun x y => c ω * D ω ((2 : ℝ)⁻¹ • x) ((2 : ℝ)⁻¹ • y))) P P) :
    IdentDistrib
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0)
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ (n + 1)) 0 then (1 : ℝ) else 0) P P := by
  let R := P.map (fun ω => (μ ω, D ω))
  let F : (Measure ℂ × (ℂ → ℂ → ℝ)) → ℕ → ℝ := fun v n =>
    if pinchPointEventWithInternalBounds v.1 v.2 U T Q V M ((2 : ℝ)⁻¹ ^ n) 0
      then 1 else 0
  have hF : AEMeasurable F R := by
    apply AEMeasurable.of_eval
    intro n
    have hn : 0 < ((2 : ℝ)⁻¹ ^ n) := by positivity
    have hm := nullMeasurableSet_pinchPointEventWithInternalBounds_of_measurable_metric_measure
      (P := R) (D := fun v : Measure ℂ × (ℂ → ℂ → ℝ) => v.2)
      (μ := fun v : Measure ℂ × (ℂ → ℂ → ℝ) => v.1)
      hconfig M 0 hn
      (fun x y => (measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_snd))
      hmetric measurable_fst
    have hi := (aemeasurable_const : AEMeasurable (fun _ : Measure ℂ × (ℂ → ℂ → ℝ) => (1 : ℝ)) R).indicator₀ hm
    change AEMeasurable (fun v => Set.indicator _ (fun _ => (1 : ℝ)) v) R at hi
    simpa [F, Set.indicator_apply] using hi
  have hd := hscaling.comp_of_aemeasurable hF
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [ha] with ω hω
  funext n
  simp only [Function.comp_apply, F]
  have hdil := pinchPointEventWithInternalBounds_normalized_dilation (μ ω) (D ω)
    U T Q V M (((2 : ℝ)⁻¹) ^ n) 0 (by norm_num : 0 < (2 : ℝ)⁻¹) hω.2.2 hω.1 hω.2.1
  simp only [inv_inv, smul_zero] at hdil
  rw [hdil]
  simp [pow_succ, mul_comm]

#print axioms identDistrib_pinchIndicators_of_normalized_dilation

end HarmonicBalls
