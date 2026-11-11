import HarmonicBalls.Steps.Sec11.PinchBufferedThirdBump
import HarmonicBalls.Steps.Sec11.SingularFieldWeylForward
import HarmonicBalls.Steps.Sec11.SingularWeylBumpInverse

/-! # Buffered pinch shift for logarithmically singular fields

The metric-field axioms are staged and await source check. The simultaneous
positive-measure hypothesis on the two margins is explicit, and no change of
law for the shift is asserted.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- A buffered positive-measure event yields the internal pinch event after a
single smooth Weyl shift of the singular metric. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_singular_internal_pinch_of_buffer
    {U V W T Q' Q : Set ℂ} {δ ξ q b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (∀ w ∉ ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      0 < P {ω | HarmonicBalls.pinchPointEventWithInternalBounds
        ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
        (fun x y => (weylScaling (D ω) ξ f x y).toReal) U T Q' Q M 1 0} := by
  obtain ⟨f, htest, hbound, hfzero, hfdisk, hproduce⟩ :=
    h.exists_smooth_weight_for_internal_pinch hξ hq hq1
  have hfneg : ∀ x, f x ≤ 0 := fun x => (hbound x).2
  let A : Set Ω := {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
    pinchSecondEvent (μ ω) (D ω) U V δ M ∧
    (∀ w ∉ ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
    (⨆ x ∈ sphere (0 : ℂ) 5,
      internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) < ENNReal.ofReal (q * b) ∧
    ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}
  let E : Ω → ℂ → ℂ → ℝ := fun ω x y => (weylScaling (D ω) ξ f x y).toReal
  let G : Set Ω := {ω | IsEuclideanLengthMetric (D ω) ∧ IsEuclideanLengthMetric (E ω) ∧
    (∀ x y, weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y)) ∧
    (∀ x y, ENNReal.ofReal (E ω x y) = weylScaling (D ω) ξ f x y) ∧
    (∀ x y, weylScaling (E ω) ξ 0 x y = ENNReal.ofReal (E ω x y)) ∧
    (∀ x y, ENNReal.ofReal (D ω x y) = weylScaling (E ω) ξ (fun z => -f z) x y)}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
        haxioms hgff hγ hγ₂ hα hD,
      ae_weylScaling_zero_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
        haxioms hgff hγ hγ₂ hα hD,
      ae_singularField_negative_weylScaling_finite P γ ξ α₀ hC hcirc D
        haxioms hgff hγ hγ₂ hα hD hξ.le,
      ae_singularField_weylBump_identities_of_metricFieldAxioms P γ ξ α₀ hC hcirc D
        haxioms hgff hγ hγ₂ hα hD hξ.le] with ω hm hz hfin hs
    have hb := hs f htest.1.continuous htest.2.1 hfneg
    exact ⟨hm, hb.1, hz, fun x y => (hfin f hfneg x y).2, hb.2.1, hb.2.2⟩
  have heq : A =ᵐ[P] A ∩ G := by
    filter_upwards [hG] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  have hp : 0 < P (A ∩ G) := by rw [← measure_congr heq]; exact hA
  refine ⟨f, htest, hfneg, hfzero, hfdisk, hp.trans_le (measure_mono ?_)⟩
  intro ω hω
  obtain ⟨hd, he, hz, hforward, hzeroE, hreverse⟩ := hω.2
  have henonneg : ∀ x y, 0 ≤ E ω x y := fun x y => ENNReal.toReal_nonneg
  exact hproduce _ _ _ γ M b hd he henonneg hz hforward hzeroE hreverse
    hω.1.1 hω.1.2.1 hω.1.2.2.1 hω.1.2.2.2.1 hω.1.2.2.2.2


end HarmonicBalls
