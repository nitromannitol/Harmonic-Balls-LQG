import HarmonicBalls.Proofs.Sec11.PunctureMetricHypotheses
import HarmonicBalls.Proofs.Sec11.PuncturedMetricOriginExtension

/-! # Locality through the origin from diameter moments

The normalized singular internal metric has a local version on a neighborhood
of the origin if finitely many fixed-scale base-metric diameter moments are
finite. The Section 8 inputs use Leonardo Bonanno's LatticeProb code.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- Fixed-scale diameter moments give a local normalized version of the
singular internal metric on a domain containing the origin. -/
theorem IsWholePlaneGFF.exists_modConst_internal_singularMetric_of_diameter_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (s : ℝ) (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ)
    {U V : Set ℂ} (hV : IsOpen V) (hne : (V \ {0}).Nonempty) (hVU : V ⊆ U)
    (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ (ε : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω, ⨆ x ∈ Metric.closedBall (z i) ε,
        ⨆ y ∈ Metric.closedBall (z i) ε,
          internalMetric (𝔇 (hC ω)) (Metric.ball (z i) (2 * ε)) x y ∂P) ≠ ∞) →
        ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
          (∀ᵐ ω ∂P, 0 < c ω) ∧
          (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U]
            (fun ω => G ω x y)) ∧
          ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
            internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y) := by
  have hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (D ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y := by
    filter_upwards [hD] with ω hω
    exact fun x y => (hω x y).2
  obtain ⟨ε, N, z, hε, hremove⟩ :=
    h.exists_puncture_criterion_of_lqgMetric hAff 𝔇 h𝔇 D s α
      hs hξ hα hαQ V hball hmetric hscale
  refine ⟨ε, N, z, hε, ?_⟩
  intro hmom
  apply h.exists_modConst_internal_singularMetric_of_point_removal
    𝔇 h𝔇 hD hmetric hV hne hVU ψ hψ hψint
  filter_upwards [hremove hmom] with ω hω x hx y hy
  exact hω x y (by simpa using hx.2) (by simpa using hy.2)

/-- At Liouville charge `α = γ`, a metric of the singular field has a
local normalized version once the displayed diameter moments are finite.
The metric-field and affine-invariance propositions are staged hypotheses. -/
theorem IsWholePlaneGFF.exists_modConst_locality_at_liouville_charge
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (haxioms : LQGMetricFieldAxioms P γ ξ γ hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ)
    (hD : IsLQGMetricOfField P γ ξ γ hC D)
    (s : ℝ) (hs : 0 ≤ s)
    {U V : Set ℂ} (hV : IsOpen V) (hne : (V \ {0}).Nonempty) (hVU : V ⊆ U)
    (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 ∧
      ∃ (ε : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ε ∧
        ((∀ i, i ≤ N → (∫⁻ ω, ⨆ x ∈ Metric.closedBall (z i) ε,
          ⨆ y ∈ Metric.closedBall (z i) ε,
            internalMetric (𝔇 (hC ω)) (Metric.ball (z i) (2 * ε)) x y ∂P) ≠ ∞) →
          ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
            (∀ᵐ ω ∂P, 0 < c ω) ∧
            (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst γ hC U]
              (fun ω => G ω x y)) ∧
            ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
              internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y) := by
  have hγQ := gamma_lt_lqgQ hγ hγ₂
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ γ hC hcirc D
    haxioms h hγ hγ₂ hγQ hD
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  exact ⟨𝔇, h𝔇, h.exists_modConst_internal_singularMetric_of_diameter_moments
    hAff 𝔇 h𝔇 hrepr hmetric s hs hξ hγ.le hγQ hV hne hVU hball ψ hψ hψint⟩


end HarmonicBalls
