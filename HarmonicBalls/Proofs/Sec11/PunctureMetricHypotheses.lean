import HarmonicBalls.Proofs.Sec11.InternalDiameterLaw
import HarmonicBalls.Steps.Sec11.MetricField
import HarmonicBalls.Steps.Sec11.MetricArcLength

/-! # Metric hypotheses for puncture removal

The base-metric measurability and length assumptions follow from the LQG
metric axioms. The singular-field length assertion below uses the explicitly
staged metric-field proposition.
-/

namespace HarmonicBalls

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- A base LQG distance is measurable in a whole-plane GFF realization. -/
theorem IsWholePlaneGFF.measurable_baseMetric_apply
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (x y : ℂ) : Measurable fun ω => 𝔇 (hC ω) x y := by
  obtain ⟨F, hF, hF_eq⟩ := exists_common_observable_of_distribution_measurable
    (fun T => 𝔇 T x y) (h𝔇.measurable_apply x y)
  have hm : Measurable (fun (ω : Ω) (o : GFFObservable.Admissible) =>
      o.1.eval (hC ω) (hcirc ω)) := by
    apply Measurable.of_eval
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact h.measurable_pairing φ ho
    | circle r z => exact h.measurable_circle r z ho
  have heq : (F ∘ fun (ω : Ω) (o : GFFObservable.Admissible) =>
      o.1.eval (hC ω) (hcirc ω)) = fun ω => 𝔇 (hC ω) x y := by
    funext ω
    exact hF_eq (hC ω) (hcirc ω)
  rw [← heq]
  exact hF.comp hm

/-- The base metric is almost surely a Euclidean length metric. -/
theorem IsWholePlaneGFF.ae_isEuclideanLengthMetric_baseMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
  have hzero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
    funext φ
    simp [addFunPairing]
  have hm := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (by intro ω; fun_prop) (by intro x; fun_prop)).ae_isEuclideanLengthMetric
  simpa only [hzero] using hm

/-- Puncture removal follows from finitely many fixed-scale diameter moments,
for a singular metric with its length and Weyl identities made explicit. -/
theorem IsWholePlaneGFF.exists_puncture_criterion_of_lqgMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (E : Ω → ℂ → ℂ → ℝ) (s α : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ)
    (V : Set ℂ) (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω, ⨆ x ∈ Metric.closedBall (c i) ε,
        ⨆ y ∈ Metric.closedBall (c i) ε,
          internalMetric (𝔇 (hC ω)) (Metric.ball (c i) (2 * ε)) x y ∂P) ≠ ∞) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y) := by
  have hD := h.ae_isEuclideanLengthMetric_baseMetric 𝔇 h𝔇
  have hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ 𝔇 (hC ω) x y := by
    filter_upwards [hD] with ω hω
    intro x y
    have ht := hω.triangle x y x
    rw [hω.self_eq_zero, hω.symm y x] at ht
    linarith
  have hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y := by
    filter_upwards [hE] with ω hω
    intro x y
    have ht := hω.triangle x y x
    rw [hω.self_eq_zero, hω.symm y x] at ht
    linarith
  have hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (𝔇 (hC ω)) ξ 0 x y = ENNReal.ofReal (𝔇 (hC ω) x y) := by
    filter_upwards [hD] with ω hω
    exact hω.weylScaling_zero ξ
  exact h.exists_puncture_criterion_of_fixed_diameter_moments hAff 𝔇 h𝔇 E s α
    hs hξ hα hαQ V hball (h.measurable_baseMetric_apply 𝔇 h𝔇) hD hE
    hDnonneg hEnonneg hzero hscale

/-- For a metric of the log-singular field, the remaining hypotheses are
fixed-scale base-metric moments and the explicitly staged affine-invariance
and metric-field propositions. -/
theorem IsWholePlaneGFF.exists_puncture_criterion_of_metricOfField
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (E : Ω → ℂ → ℂ → ℝ) (s α : ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ)
    (hE : IsLQGMetricOfField P γ ξ α hC E)
    (V : Set ℂ) (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V) :
    ∃ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 ∧
      ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
        ((∀ i, i ≤ N → (∫⁻ ω, ⨆ x ∈ Metric.closedBall (c i) ε,
          ⨆ y ∈ Metric.closedBall (c i) ε,
            internalMetric (𝔇 (hC ω)) (Metric.ball (c i) (2 * ε)) x y ∂P) ≠ ∞) →
          ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
            internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y) := by
  have hm := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc E
    haxioms h hγ hγ₂ hαQ hE
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hE
  have hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y := by
    filter_upwards [hrepr] with ω hω
    exact fun x y => (hω x y).2
  exact ⟨𝔇, h𝔇, h.exists_puncture_criterion_of_lqgMetric hAff 𝔇 h𝔇 E s α
    hs hξ hα hαQ V hball hm hscale⟩

/-- The puncture criterion applies at the Liouville charge `α = γ`,
conditionally on fixed-scale diameter moments. -/
theorem IsWholePlaneGFF.exists_puncture_criterion_at_liouville_charge
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (E : Ω → ℂ → ℂ → ℝ) (s : ℝ)
    (haxioms : LQGMetricFieldAxioms P γ ξ γ hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hs : 0 ≤ s) (hξ : 0 < ξ)
    (hE : IsLQGMetricOfField P γ ξ γ hC E)
    (V : Set ℂ) (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V) :
    ∃ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 ∧
      ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
        ((∀ i, i ≤ N → (∫⁻ ω, ⨆ x ∈ Metric.closedBall (c i) ε,
          ⨆ y ∈ Metric.closedBall (c i) ε,
            internalMetric (𝔇 (hC ω)) (Metric.ball (c i) (2 * ε)) x y ∂P) ≠ ∞) →
          ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
            internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y) :=
  h.exists_puncture_criterion_of_metricOfField hAff E s γ haxioms hγ hγ₂
    hs hξ hγ.le (gamma_lt_lqgQ hγ hγ₂) hE V hball

#print axioms IsWholePlaneGFF.exists_puncture_criterion_at_liouville_charge
#print axioms IsWholePlaneGFF.exists_puncture_criterion_of_metricOfField
#print axioms IsWholePlaneGFF.exists_puncture_criterion_of_lqgMetric

end HarmonicBalls
