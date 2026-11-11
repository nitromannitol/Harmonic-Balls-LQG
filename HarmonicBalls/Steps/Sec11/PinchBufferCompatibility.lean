import HarmonicBalls.Steps.Sec11.PinchBufferedThresholdSelection
import HarmonicBalls.Steps.Sec11.PinchMetricBarrier

/-! # Compatibility of the pinch contraction and radial barrier

The two strict margins require a common contraction. The product criterion
below makes their tradeoff explicit; it does not assert its probability.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- A strict path-to-barrier ratio and product bound leave a nonempty interval
of contraction factors. -/
theorem exists_pinch_contraction_of_product_bound
    {a c h b : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hh : 0 < h) (hb : 0 < b)
    (hab : a < b) (hprod : a * c < b * h) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ a < q * b ∧ q * c < h := by
  have hr : 0 ≤ a / b := div_nonneg ha hb.le
  have hr1 : a / b < 1 := (div_lt_one₀ hb).2 hab
  by_cases hc0 : c = 0
  · obtain ⟨q, hqlo, hqhi⟩ := exists_between hr1
    have hq : 0 < q := lt_of_le_of_lt hr hqlo
    refine ⟨q, hq, hqhi.le, ?_, ?_⟩
    · exact (div_lt_iff₀ hb).1 hqlo
    · simpa [hc0] using hh
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hratio : a / b < h / c := by
      apply (div_lt_div_iff₀ hb hcpos).2
      nlinarith
    obtain ⟨q, hqlo, hqhi⟩ := exists_between (lt_min hr1 hratio)
    have hq : 0 < q := lt_of_le_of_lt hr hqlo
    refine ⟨q, hq, (lt_of_lt_of_le hqhi (min_le_left _ _)).le, ?_, ?_⟩
    · exact (div_lt_iff₀ hb).1 hqlo
    · exact (lt_div_iff₀ hcpos).1 (lt_of_lt_of_le hqhi (min_le_right _ _))

/-- For finite nonnegative quantities the product criterion is also
necessary for a common contraction. -/
theorem pinch_contraction_iff_product_bound
    {a c h b : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hh : 0 < h) (hb : 0 < b) :
    (∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ a < q * b ∧ q * c < h) ↔
      a < b ∧ a * c < b * h := by
  constructor
  · rintro ⟨q, hq, hq1, hpath, hdiam⟩
    constructor
    · have hqb : q * b ≤ b := by nlinarith
      exact hpath.trans_le hqb
    · calc
        a * c ≤ (q * b) * c := mul_le_mul_of_nonneg_right hpath.le hc
        _ = b * (q * c) := by ring
        _ < b * h := mul_lt_mul_of_pos_left hdiam hb
  · rintro ⟨hab, hprod⟩
    exact exists_pinch_contraction_of_product_bound ha hc hh hb hab hprod


/-- Extended nonnegative path and diameter quantities satisfy the buffered
inequalities when their finite real values meet the product criterion. -/
theorem exists_pinch_contraction_of_finite_product_bound
    {L C : ℝ≥0∞} {h b : ℝ} (hL : L ≠ ∞) (hC : C ≠ ∞)
    (hh : 0 < h) (hb : 0 < b) (hab : L.toReal < b)
    (hprod : L.toReal * C.toReal < b * h) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ L < ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * C < ENNReal.ofReal h := by
  obtain ⟨q, hq, hq1, hpath, hdiam⟩ :=
    exists_pinch_contraction_of_product_bound ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      hh hb hab hprod
  refine ⟨q, hq, hq1, ?_, ?_⟩
  · rw [← ENNReal.ofReal_toReal hL]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hpath
  · rw [← ENNReal.ofReal_toReal hC, ← ENNReal.ofReal_mul hq.le]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (mul_nonneg hq.le ENNReal.toReal_nonneg)).2 hdiam

/-- A positive-mass product-gap event gives deterministic compatible pinch
margins. The barrier is the sum of two radial metric gaps. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_buffer_of_radial_product
    {U V W T Q' Q : Set ℂ} {δ M : ℝ}
    (hconfig : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (let b := setDist (D ω) {0} (sphere 0 5) +
        setDist (D ω) (sphere 0 5) (ball 0 6)ᶜ
       let L := ⨆ x ∈ sphere (0 : ℂ) 5,
         internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x
       let C := internalDiam (D ω) δ (thickening (3 * δ) W \ V)
       L.toReal < b ∧ L.toReal * C.toReal <
         b * setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    ∃ q b : ℝ, 0 < q ∧ q ≤ 1 ∧ 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (∀ w ∉ ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))} := by
  let A : Set Ω := {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
    pinchSecondEvent (μ ω) (D ω) U V δ M ∧
    (let b := setDist (D ω) {0} (sphere 0 5) +
      setDist (D ω) (sphere 0 5) (ball 0 6)ᶜ
     let L := ⨆ x ∈ sphere (0 : ℂ) 5,
       internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x
     let C := internalDiam (D ω) δ (thickening (3 * δ) W \ V)
     L.toReal < b ∧ L.toReal * C.toReal <
       b * setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}
  let G : Set Ω := {ω | IsEuclideanLengthMetric (D ω)}
  have heq : A =ᵐ[P] A ∩ G := by
    filter_upwards [hmetric] with ω hω
    simp only [mem_inter_iff, hω, and_true, G, mem_ofPred_eq]
  have hp : 0 < P (A ∩ G) := by rw [← measure_congr heq]; exact hA
  apply exists_positive_measure_pinch_buffer_parameters P D μ U V W T Q' Q δ M
  apply hp.trans_le (measure_mono ?_)
  intro ω hω
  obtain ⟨hfirst, hsecond, hgap, hprod⟩ := hω.1
  have hm : IsEuclideanLengthMetric (D ω) := hω.2
  have hnonneg : ∀ x y, 0 ≤ D ω x y := by
    intro x y
    have ht := hm.triangle x y x
    rw [hm.self_eq_zero, hm.symm y x] at ht
    linarith
  let b : ℝ := setDist (D ω) {0} (sphere 0 5) + setDist (D ω) (sphere 0 5) (ball 0 6)ᶜ
  let L : ℝ≥0∞ := ⨆ x ∈ sphere (0 : ℂ) 5,
    internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x
  let C : ℝ≥0∞ := internalDiam (D ω) δ (thickening (3 * δ) W \ V)
  have hL : L ≠ ∞ := (hfirst.1.trans_le le_top).ne
  have hC : C ≠ ∞ := (hconfig.internalDiam_outerAnnulus_lt_top hm hnonneg).ne
  have hb : 0 < b := lt_of_le_of_lt ENNReal.toReal_nonneg hgap
  have hh := (hm.pinch_sphere_distances_pos hconfig.δ₀_mem.1).2
  obtain ⟨q, hq, hq1, hpath, hdiam⟩ :=
    exists_pinch_contraction_of_finite_product_bound hL hC hh hb hgap hprod
  refine ⟨hfirst, hsecond, q, b, hq, hq1, ?_, hpath, hdiam⟩
  intro w hw
  exact hm.center_to_complement_lower_bound hnonneg (by norm_num) (by norm_num) hw



end HarmonicBalls
