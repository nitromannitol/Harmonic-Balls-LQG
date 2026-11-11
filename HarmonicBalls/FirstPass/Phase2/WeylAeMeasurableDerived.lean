import HarmonicBalls.FirstPass.Frozen.S11d

/-! # Measurability of the weighted internal metric: reduction to one deterministic fact

`LQGInternalMetricWeylAeMeasurableFrozen` (FirstPass/Frozen/S11d.lean:130).

This file isolates the deterministic content of that frozen statement. The frozen Prop asks, for each open `W`, for a
`distributionMeasurableSpace`-measurable `Φ` which agrees almost surely with the internal metric of the `toReal`-weighted
metric `e^{-ξ α₀ log|·|} · 𝔇(h^ℂ + f)` on `W`. Once the metric `𝔇 T` is a measurable function of the distribution `T`
(`IsLQGMetric.measurable_apply`), the measurability half is the composition `Φ = G ∘ 𝔇`, where `G` is a
measurable functional of a metric. The only analytic content is therefore the following deterministic fact.

NOT PROVED. `LQGWeightedInternalDetMeasurable` below is the exact missing ingredient. The written argument sketches it through lower semicontinuity of the
constrained weighted distance in the continuous metric and a Borel exhaustion, but leaves the lower semicontinuity
claim unproved (l.389-391), does not treat the vertex `0` of the singular weight by a chain argument, and does not
verify the Borel-ness on the space of metrics. -/

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- Deterministic measurability of the weighted internal metric (UNVERIFIED target; the missing ingredient of
`LQGInternalMetricWeylAeMeasurableFrozen`). For every `ξ`, `α₀`, every open `U` and all `q q'`, there is a functional `G`
on metrics on `ℂ`, measurable for the product σ-algebra of the evaluations `D ↦ D a b`, which equals the internal metric
on `U` of the `toReal`-valued Weyl scaling `e^{-ξ α₀ log|·|} · D` for every Euclidean length metric `D` (Armstrong-Kuusi-
Mourrat, Euclidean length metric; Gwynne-Miller, Weyl scaling (1.8)). -/
def LQGWeightedInternalDetMeasurable : Prop :=
  ∀ (ξ α₀ : ℝ) (U : Set ℂ), IsOpen U → ∀ q q' : ℂ, ∃ G : (ℂ → ℂ → ℝ) → ℝ≥0∞, Measurable G ∧
    ∀ D : ℂ → ℂ → ℝ, IsEuclideanLengthMetric D →
      G D = internalMetric (fun u v => (weylScaling D ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal) U q q'

/-- Composition step: given the deterministic fact, the weighted internal metric of `𝔇 T` is a
`distributionMeasurableSpace`-measurable function of the distribution `T`, and equals the internal metric of the
weighted metric whenever `𝔇 T` is a Euclidean length metric. This is the measurability half of
`LQGInternalMetricWeylAeMeasurableFrozen`; the almost-sure half needs the length property of `𝔇 (h^ℂ + f)`, which is
axiom I of `SatisfiesLQGMetricAxioms` (not used here). -/
theorem exists_distributionMeasurable_weightedInternal_of_det (hdet : LQGWeightedInternalDetMeasurable)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hmeas : ∀ z w, Measurable[distributionMeasurableSpace] fun T => 𝔇 T z w)
    {ξ α₀ : ℝ} {U : Set ℂ} (hU : IsOpen U) (q q' : ℂ) :
    ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] Φ ∧
      ∀ T : (ℂ → ℝ) → ℝ, IsEuclideanLengthMetric (𝔇 T) →
        Φ T = internalMetric (fun u v => (weylScaling (𝔇 T) ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal) U q q' := by
  obtain ⟨G, hG, hGeq⟩ := hdet ξ α₀ U hU q q'
  have h𝔇 : Measurable[distributionMeasurableSpace] (fun T => 𝔇 T) := by
    -- The domain `(ℂ → ℝ) → ℝ` also carries `MeasurableSpace.pi`; pin the distribution σ-algebra locally.
    let _inst : MeasurableSpace ((ℂ → ℝ) → ℝ) := distributionMeasurableSpace
    exact measurable_pi_iff.2 fun z => measurable_pi_iff.2 fun w => hmeas z w
  exact ⟨fun T => G (𝔇 T), hG.comp h𝔇, fun T hT => hGeq (𝔇 T) hT⟩

end HarmonicBalls
