import HarmonicBalls.Steps.Sec11.PinchThresholdSelection
import HarmonicBalls.Steps.Sec11.PinchBufferedThirdBump

/-! # Selection of compatible buffered pinch thresholds

Strictness permits simultaneous deterministic selection of the contraction
and barrier from sample-dependent choices. No event measurability is needed.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- Strict compatible margins survive decreasing both parameters to positive
rational values. The upper bound is monotone in the contraction. -/
theorem exists_rat_buffer_parameters {L C H : ℝ≥0∞} {q b : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hL : L < ENNReal.ofReal (q * b))
    (hC : ENNReal.ofReal q * C < H) :
    ∃ q' b' : ℚ, 0 < (q' : ℝ) ∧ (q' : ℝ) ≤ 1 ∧
      (b' : ℝ) ≤ b ∧ L < ENNReal.ofReal ((q' : ℝ) * (b' : ℝ)) ∧
      ENNReal.ofReal (q' : ℝ) * C < H := by
  have hLfin : L ≠ ∞ := (hL.trans_le (le_top)).ne
  have hprod : L.toReal < q * b := by
    have ht := (ENNReal.toReal_lt_toReal hLfin ENNReal.ofReal_ne_top).2 hL
    have hqb : 0 ≤ q * b := by
      by_contra hn
      have hz : ENNReal.ofReal (q * b) = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hn)
      rw [hz] at hL
      exact (not_le_of_gt hL) (zero_le : 0 ≤ L)
    simpa [ENNReal.toReal_ofReal hqb] using ht
  have hb : 0 < b := by
    have hl : 0 ≤ L.toReal := ENNReal.toReal_nonneg
    nlinarith
  have hd : L.toReal / q < b := (div_lt_iff₀ hq).2 (by nlinarith)
  obtain ⟨b', hb'low, hb'high⟩ := exists_rat_btwn hd
  have hb'pos : 0 < (b' : ℝ) := lt_of_le_of_lt (div_nonneg ENNReal.toReal_nonneg hq.le) hb'low
  have hqbound : L.toReal / (b' : ℝ) < q := by
    apply (div_lt_iff₀ hb'pos).2
    nlinarith [(div_lt_iff₀ hq).1 hb'low]
  obtain ⟨q', hq'low, hq'high⟩ := exists_rat_btwn hqbound
  have hq'pos : 0 < (q' : ℝ) := lt_of_le_of_lt (div_nonneg ENNReal.toReal_nonneg hb'pos.le) hq'low
  have hmul : L.toReal < (q' : ℝ) * (b' : ℝ) := by
    nlinarith [(div_lt_iff₀ hb'pos).1 hq'low]
  have hL' : L < ENNReal.ofReal ((q' : ℝ) * (b' : ℝ)) := by
    apply (ENNReal.toReal_lt_toReal hLfin ENNReal.ofReal_ne_top).1
    simpa [ENNReal.toReal_ofReal (mul_nonneg hq'pos.le hb'pos.le)] using hmul
  refine ⟨q', b', hq'pos, hq'high.le.trans hq1, hb'high.le, hL', ?_⟩
  apply lt_of_le_of_lt _ hC
  gcongr

/-- If compatible parameters exist on a positive-mass event, one deterministic
pair works on a positive-mass subevent. The barrier predicate must be preserved
when its threshold is decreased. -/
theorem exists_positive_measure_buffer_parameters
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (L C H : Ω → ℝ≥0∞) (B : Ω → ℝ → Prop)
    (hB : ∀ ω b b', b' ≤ b → B ω b → B ω b')
    (hA : 0 < P {ω | ω ∈ A ∧ ∃ q b : ℝ, 0 < q ∧ q ≤ 1 ∧ B ω b ∧
      L ω < ENNReal.ofReal (q * b) ∧ ENNReal.ofReal q * C ω < H ω}) :
    ∃ q b : ℝ, 0 < q ∧ q ≤ 1 ∧ 0 < P {ω | ω ∈ A ∧ B ω b ∧
      L ω < ENNReal.ofReal (q * b) ∧ ENNReal.ofReal q * C ω < H ω} := by
  let E : ℚ × ℚ → Set Ω := fun i => {ω | ω ∈ A ∧
    0 < (i.1 : ℝ) ∧ (i.1 : ℝ) ≤ 1 ∧ B ω (i.2 : ℝ) ∧
    L ω < ENNReal.ofReal ((i.1 : ℝ) * (i.2 : ℝ)) ∧
    ENNReal.ofReal (i.1 : ℝ) * C ω < H ω}
  have hcover : {ω | ω ∈ A ∧ ∃ q b : ℝ, 0 < q ∧ q ≤ 1 ∧ B ω b ∧
      L ω < ENNReal.ofReal (q * b) ∧ ENNReal.ofReal q * C ω < H ω} ⊆ ⋃ i, E i := by
    intro ω hω
    obtain ⟨hωA, q, b, hq, hq1, hb, hL, hC⟩ := hω
    obtain ⟨q', b', hq', hq'1, hb', hL', hC'⟩ := exists_rat_buffer_parameters hq hq1 hL hC
    exact mem_iUnion.mpr ⟨(q', b'), hωA, hq', hq'1, hB ω b b' hb' hb, hL', hC'⟩
  have hpos : 0 < P (⋃ i, E i) := hA.trans_le (measure_mono hcover)
  obtain ⟨⟨q, b⟩, hp⟩ := exists_measure_pos_of_not_measure_iUnion_null hpos.ne'
  by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) ≤ 1
  · refine ⟨q, b, hq.1, hq.2, hp.trans_le (measure_mono ?_)⟩
    intro ω hω
    exact ⟨hω.1, hω.2.2.2.1, hω.2.2.2.2.1, hω.2.2.2.2.2⟩
  · have hempty : E (q, b) = ∅ := by
      ext ω
      simp only [E, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨_, hq0, hq1, _⟩
      exact hq ⟨hq0, hq1⟩
    rw [hempty, measure_empty] at hp
    exact (lt_irrefl _ hp).elim

/-- Sample-dependent compatible pinch margins can be replaced by one
contraction and barrier on a positive-mass subevent. -/
theorem exists_positive_measure_pinch_buffer_parameters
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (U V W T Q' Q : Set ℂ) (δ M : ℝ)
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      ∃ q b : ℝ, 0 < q ∧ q ≤ 1 ∧
      (∀ w ∉ Metric.ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
      (⨆ x ∈ Metric.sphere (0 : ℂ) 5,
        internalMetric (D ω) (Metric.thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (Metric.thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (Metric.sphere 0 (2 * δ)) (Metric.sphere 0 (3 * δ)))}) :
    ∃ q b : ℝ, 0 < q ∧ q ≤ 1 ∧ 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (∀ w ∉ Metric.ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
      (⨆ x ∈ Metric.sphere (0 : ℂ) 5,
        internalMetric (D ω) (Metric.thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (Metric.thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (Metric.sphere 0 (2 * δ)) (Metric.sphere 0 (3 * δ)))} := by
  let A : Set Ω := {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
    pinchSecondEvent (μ ω) (D ω) U V δ M}
  let L : Ω → ℝ≥0∞ := fun ω => ⨆ x ∈ Metric.sphere (0 : ℂ) 5,
    internalMetric (D ω) (Metric.thickening (2 * δ) (Q ∪ W))ᶜ 0 x
  let C : Ω → ℝ≥0∞ := fun ω => internalDiam (D ω) δ (Metric.thickening (3 * δ) W \ V)
  let H : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (setDist (D ω) (Metric.sphere 0 (2 * δ)) (Metric.sphere 0 (3 * δ)))
  let B : Ω → ℝ → Prop := fun ω b => ∀ w ∉ Metric.ball (0 : ℂ) 6, b ≤ D ω 0 w
  have hB : ∀ ω b b', b' ≤ b → B ω b → B ω b' := by
    intro ω b b' hbb hb w hw
    exact hbb.trans (hb w hw)
  have hp : 0 < P {ω | ω ∈ A ∧ ∃ q b : ℝ, 0 < q ∧ q ≤ 1 ∧ B ω b ∧
      L ω < ENNReal.ofReal (q * b) ∧ ENNReal.ofReal q * C ω < H ω} := by
    simpa only [A, L, C, H, B, mem_ofPred_eq, and_assoc] using hA
  obtain ⟨q, b, hq, hq1, hp⟩ := exists_positive_measure_buffer_parameters P A L C H B hB hp
  refine ⟨q, b, hq, hq1, ?_⟩
  simpa only [A, L, C, H, B, mem_ofPred_eq, and_assoc] using hp

#print axioms exists_positive_measure_pinch_buffer_parameters

#print axioms exists_rat_buffer_parameters
#print axioms exists_positive_measure_buffer_parameters

end HarmonicBalls
