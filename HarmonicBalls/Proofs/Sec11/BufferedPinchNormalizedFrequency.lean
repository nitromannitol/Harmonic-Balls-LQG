import HarmonicBalls.Proofs.Sec11.PinchNormalizedUnitFrequency
import HarmonicBalls.Proofs.Sec11.BufferedPinchShiftLaw
import HarmonicBalls.Steps.Sec11.PinchBufferCompatibility
import HarmonicBalls.Steps.Sec11.ScalePowerBounds

/-! # Buffered singular-field pinch frequency

The Section 8 ergodic theorem used here is from Leonardo Bonanno's
LatticeProb formalization. The metric and measure field axioms are staged;
the product-gap event, shift realization, locality and stationarity remain
explicit hypotheses. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- A radial product-gap event and a compatible field shift give positive
internal-pinch block frequency at the singularity of strength `γ`. -/
theorem IsPinchPointProofConfiguration.ae_internal_pinch_frequency_of_radial_product
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (γ M : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ γ hC hcirc)
    (hweyl : LQGMeasureWeylScaling P γ γ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hD : IsLQGMetricOfField P γ ξ γ hC D)
    (hμ : IsLQGMeasureOfField P γ γ hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ A : Set ℂ, IsOpen A → A.Nonempty → 0 < μ ω A)
    (hshift : ∀ f : ℂ → ℝ, IsTestFunction univ f → (∀ x, f x ≤ 0) →
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) →
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∃ τ : Ω → Ω, Measure.QuasiMeasurePreserving τ P P ∧
        (∀ᵐ ω ∂P, fieldCircleAverage γ (hcirc (τ ω)) =
          addCircleAverage (fieldCircleAverage γ (hcirc ω)) f) ∧
        (∀ᵐ ω ∂P, D (τ ω) = fun x y => (weylScaling (D ω) ξ f x y).toReal))
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (let b := setDist (D ω) {0} (sphere 0 5) +
        setDist (D ω) (sphere 0 5) (ball 0 6)ᶜ
       let L := ⨆ x ∈ sphere (0 : ℂ) 5,
         internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x
       let C := internalDiam (D ω) δ (thickening (3 * δ) W \ V)
       L.toReal < b ∧ L.toReal * C.toReal <
         b * setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))})
    (hmetric : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst γ hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * D ω x y)
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y))
    (hstat : IdentDistrib
      (fun ω n => if HarmonicBalls.pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0)
      (fun ω n => if HarmonicBalls.pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 1)) 0 then (1 : ℝ) else 0) P P) :
    ∃ r ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, r * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        HarmonicBalls.pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  have hα := gamma_lt_lqgQ hγ hγ₂
  have hm := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ γ hC hcirc D
    haxioms hgff hγ hγ₂ hα hD
  obtain ⟨q, b, hq, hq1, hp⟩ := h.exists_positive_measure_buffer_of_radial_product P D μ hm hA
  have hunit := h.positive_singular_internal_pinch_of_buffer_shiftMap hξ hq hq1 P γ γ M
    hC hcirc D μ haxioms hweyl hgff hγ hγ₂ hα hD hμ hshift hp
  exact hgff.ae_positive_internal_pinch_frequency_of_normalized_metric P hμ hfull hm
    h.toIsPinchPointConfiguration M hmetric hstat hunit


end HarmonicBalls
