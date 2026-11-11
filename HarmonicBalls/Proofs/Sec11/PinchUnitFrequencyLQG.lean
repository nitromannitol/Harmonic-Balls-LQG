import HarmonicBalls.Proofs.Sec11.PinchNormalizedUnitFrequency
import HarmonicBalls.Proofs.Sec11.PinchStationarityLQG
import HarmonicBalls.Proofs.Sec6.SimultaneousSingularMeasure
import HarmonicBalls.Proofs.Sec9.LQGExistenceConsequences

/-! # Unit-scale pinch frequency from LQG inputs

The Section 8 ergodic theorem and Section 6 assembly used here include
Leonardo Bonanno's LatticeProb formalization. The whole-plane mass bound,
measure existence and coordinate-change inputs, and the mixture metric-field
axioms are staged and remain subject to source review. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- The unit-scale internal-pinch event has positive block frequency under
normalized metric locality. Full support and stationarity follow from the
explicit whole-plane mass and LQG coordinate-change inputs. -/
theorem IsWholePlaneGFF.ae_positive_internal_pinch_frequency_of_lqg_inputs
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hDG : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (γ' : ℝ)
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P' γ' hC' hcirc')
    (hCC0 : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (γ' : ℝ)
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P' γ' 0 hC' hcirc')
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (haxioms : LQGMetricFieldAxioms (mixMeasure.prod (P.prod P)) γ ξ α
      (fun x => if x.1 = 0 then hC x.2.1 else
        affinePairing hC hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2)
      (fun x => if x.1 = 0 then hcirc x.2.1 else
        affineCircle hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (hmetric : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * D ω (x, y))
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y))
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y)) U T Q V M 1 0}) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y))
          U T Q V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  have hS : WholePlaneScaledBallMassStep :=
    wholePlaneScaledBallMassStep_of_rescaled
      (rescaledBallMassUniformStep_of_DG hDG
        (fun _ _ P' hC' hcirc' => wholePlaneGFFAffineInvariance_proved P' hC' hcirc')
        hCC0 wholePlaneGFFMixtureStep_holds)
  have hfull : ∀ᵐ ω ∂P, ∀ A : Set ℂ, IsOpen A → A.Nonempty → 0 < μ ω A := by
    filter_upwards [Section6.ae_fullSupport_all_singular_limits hS P γ hγ hγ₂ hC hcirc h hE0,
      hμ] with ω hsupport hμω
    exact hsupport α (μ ω) hμω
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hm := h.ae_lengthMetric_of_affine_mixture hAff hγ hγ₂ hα
    (k := (2 : ℝ)⁻¹) (by norm_num) 𝔇 h𝔇 hD haxioms
  have hs := h.identDistrib_pinchIndicators_of_normalizedLQG hAff hCC hγ hγ₂ hα hμ
    𝔇 h𝔇 hD haxioms hconfig M
  exact h.ae_positive_internal_pinch_frequency_of_normalized_metric P hμ hfull hm
    hconfig M hmetric hs hpos


end HarmonicBalls
