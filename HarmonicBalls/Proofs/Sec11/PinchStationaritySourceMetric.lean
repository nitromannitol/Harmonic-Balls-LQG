import HarmonicBalls.Proofs.Sec11.PinchCommonObservation
import HarmonicBalls.Steps.Sec11.PinchMetricDilation
import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent
import HarmonicBalls.Steps.Sec11.InternalMetricPullback

/-! # Pinch stationarity from a joint scaling law and a length metric -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

open Classical in
/-- A joint scaling law gives stationary strengthened pinch indicators when
its continuous distance observation is almost surely a Euclidean length metric. -/
theorem identDistrib_pinchIndicators_of_normalized_dilation_of_ae_lengthMetric
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (D D' : Ω → C(ℂ × ℂ, ℝ))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (a : Ω → ℝ≥0∞) (c : Ω → ℝ)
    (ha : ∀ᵐ ω ∂P, a ω ≠ 0 ∧ a ω ≠ ∞ ∧ 0 < c ω)
    (hD' : ∀ᵐ ω ∂P, ∀ x y, D' ω (x, y) =
      c ω * D ω (((2 : ℝ)⁻¹ • x), ((2 : ℝ)⁻¹ • y)))
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D ω (x, y)))
    (hscaling : IdentDistrib (fun ω => (μ ω, D ω))
      (fun ω => (a ω • (μ ω).map (fun x : ℂ => (2 : ℝ) • x), D' ω)) P P) :
    IdentDistrib
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y)) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0)
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y)) U T Q V M
        ((2 : ℝ)⁻¹ ^ (n + 1)) 0 then (1 : ℝ) else 0) P P := by
  have hmetric' : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D' ω (x, y)) := by
    filter_upwards [ha, hD', hmetric] with ω hω hDω hm
    have heq : (fun x y => D' ω (x, y)) =
        (fun x y => c ω * D ω (((2 : ℝ)⁻¹ • x), ((2 : ℝ)⁻¹ • y))) := by
      funext x y
      exact hDω x y
    rw [heq]
    exact (hm.comp_homeomorph (Homeomorph.smulOfNeZero ((2 : ℝ)⁻¹) (by norm_num))).const_mul hω.2.2
  have hex (n : ℕ) :=
    exists_common_pinchEvent_representative_of_continuous_observations P μ
      (fun ω => a ω • (μ ω).map (fun x : ℂ => (2 : ℝ) • x)) D D'
      hconfig M 0 (r := ((2 : ℝ)⁻¹ ^ n)) (by positivity) hmetric hmetric'
  choose A hAm hA₀ hA₁ using hex
  let F : (Measure ℂ × C(ℂ × ℂ, ℝ)) → ℕ → ℝ := fun v n => if v ∈ A n then 1 else 0
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro n
    exact Measurable.ite (hAm n) measurable_const measurable_const
  have hd := hscaling.comp hF
  have hEq₀ : (F ∘ fun ω => (μ ω, D ω)) =ᵐ[P]
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y)) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0) := by
    filter_upwards [ae_all_iff.mpr hA₀] with ω hω
    funext n
    simp only [Function.comp_apply, F]
    rw [← hω n]
  have hEq₁ : (F ∘ fun ω => (a ω • (μ ω).map (fun x : ℂ => (2 : ℝ) • x), D' ω)) =ᵐ[P]
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y)) U T Q V M
        ((2 : ℝ)⁻¹ ^ (n + 1)) 0 then (1 : ℝ) else 0) := by
    filter_upwards [ha, hD', ae_all_iff.mpr hA₁] with ω hω hDω hAω
    funext n
    simp only [Function.comp_apply, F]
    rw [← hAω n]
    have heq : (fun x y => D' ω (x, y)) =
        (fun x y => c ω * D ω (((2 : ℝ)⁻¹ • x), ((2 : ℝ)⁻¹ • y))) := by
      funext x y
      exact hDω x y
    rw [heq]
    have hdil := pinchPointEventWithInternalBounds_normalized_dilation (μ ω)
      (fun x y => D ω (x, y)) U T Q V M (((2 : ℝ)⁻¹) ^ n) 0
      (by norm_num : 0 < (2 : ℝ)⁻¹) hω.2.2 hω.1 hω.2.1
    simp only [inv_inv, smul_zero] at hdil
    rw [hdil]
    simp [pow_succ, mul_comm]
  exact (IdentDistrib.of_ae_eq hd.aemeasurable_fst hEq₀).symm.trans
    (hd.trans (IdentDistrib.of_ae_eq hd.aemeasurable_snd hEq₁))


end HarmonicBalls
