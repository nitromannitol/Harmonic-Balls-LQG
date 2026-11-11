import HarmonicBalls.Proofs.Sec11.BufferedPinchCanonicalLaw
import HarmonicBalls.Proofs.Sec11.PinchRadialProductShift
import HarmonicBalls.Steps.Sec11.PinchBufferCompatibility
import HarmonicBalls.Steps.Sec11.InternalPinchScales
import HarmonicBalls.Steps.Sec11.ScalePowerBounds

/-! # Audit of conditional Section 11 positivity

The smooth-shift development uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. These
checks retain the producer's hypotheses and do not close numbered results.
-/

namespace HarmonicBalls.Section11PinchPositivityAudit

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- The actual canonical-law producer, with all its outer assumptions visible. -/
example {U V W T Q' Q : Set ℂ} {δ ξ q b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ α M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (X : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d})
    (hX : AEMeasurable X P)
    (hdecode : ∀ᵐ ω ∂P, (X ω).1 = μ ω ∧ (X ω).2.1 = D ω)
    (hshiftLaw : ∀ f : ℂ → ℝ, IsTestFunction univ f → (∀ x, f x ≤ 0) →
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) →
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∃ Y : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d},
        AEMeasurable Y P ∧ P.map Y ≪ P.map X ∧
        (∀ᵐ ω ∂P, (Y ω).1 =
            (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))) ∧
          (Y ω).2.1 = fun x y => (weylScaling (D ω) ξ f x y).toReal))
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (∀ w ∉ ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M 1 0} :=
  h.positive_singular_internal_pinch_of_canonicalLaw hξ hq hq1 P γ α M hC hcirc D μ
    haxioms hgff hγ hγ₂ hα hD X hX hdecode hshiftLaw hA

/-- At Liouville charge the same buffered event and joint shift law remain hypotheses. -/
example {U V W T Q' Q : Set ℂ} {δ ξ q b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ γ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hD : IsLQGMetricOfField P γ ξ γ hC D)
    (X : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d})
    (hX : AEMeasurable X P)
    (hdecode : ∀ᵐ ω ∂P, (X ω).1 = μ ω ∧ (X ω).2.1 = D ω)
    (hshiftLaw : ∀ f : ℂ → ℝ, IsTestFunction univ f → (∀ x, f x ≤ 0) →
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) →
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∃ Y : Ω → Measure ℂ × {d : ℂ → ℂ → ℝ // IsEuclideanLengthMetric d},
        AEMeasurable Y P ∧ P.map Y ≪ P.map X ∧
        (∀ᵐ ω ∂P, (Y ω).1 =
            (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))) ∧
          (Y ω).2.1 = fun x y => (weylScaling (D ω) ξ f x y).toReal))
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (∀ w ∉ ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M 1 0} :=
  h.positive_singular_internal_pinch_of_canonicalLaw hξ hq hq1 P γ γ M hC hcirc D μ
    haxioms hgff hγ hγ₂ (gamma_lt_lqgQ hγ hγ₂) hD X hX hdecode hshiftLaw hA

/-- The radial-product producer requires a sample-space shift and common strict product gap. -/
example
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (γ α M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hshift : ∀ f : ℂ → ℝ, IsTestFunction univ f → (∀ x, f x ≤ 0) →
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) →
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) →
      ∃ τ : Ω → Ω, Measure.QuasiMeasurePreserving τ P P ∧
        (∀ᵐ ω ∂P, fieldCircleAverage α (hcirc (τ ω)) =
          addCircleAverage (fieldCircleAverage α (hcirc ω)) f) ∧
        (∀ᵐ ω ∂P, D (τ ω) = fun x y => (weylScaling (D ω) ξ f x y).toReal))
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (let b := setDist (D ω) {0} (sphere 0 5) +
        setDist (D ω) (sphere 0 5) (ball 0 6)ᶜ
       let L := ⨆ x ∈ sphere (0 : ℂ) 5,
         internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x
       let C := internalDiam (D ω) δ (thickening (3 * δ) W \ V)
       L.toReal < b ∧ L.toReal * C.toReal <
         b * setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    0 < P {ω | HarmonicBalls.pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M 1 0} :=
  h.positive_singular_internal_pinch_of_radial_product hξ P γ α M hC hcirc D μ
    haxioms hgff hγ hγ₂ hα hD hμ hshift hA

/-- Positive common buffered mass supplies each auxiliary event at fixed parameters.
These are outer-measure statements; the frozen statements demand measurable subsets. -/
example {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (U V W T Q' Q : Set ℂ) (δ M q b : ℝ)
    (hA : 0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      (∀ w ∉ ball (0 : ℂ) 6, b ≤ D ω 0 w) ∧
      (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) (thickening (2 * δ) (Q ∪ W))ᶜ 0 x) <
          ENNReal.ofReal (q * b) ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}) :
    0 < P {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (D ω) U V δ M} := by
  exact hA.trans_le (measure_mono fun _ hω => ⟨hω.1, hω.2.1⟩)

/-- The strengthened conclusion yields the original event only for length metrics. -/
example {μ : Measure ℂ} {D : ℂ → ℂ → ℝ} {U T Q' Q : Set ℂ}
    {M r : ℝ} {z : ℂ} (hD : IsEuclideanLengthMetric D)
    (h : pinchPointEventWithInternalBounds μ D U T Q' Q M r z) :
    pinchPointEvent μ D U T Q' Q M r z := pinchPointEvent_of_internalBounds hD h

universe u

/-- The third auxiliary frozen claim implies the second with the same
configuration and measurable witnesses. It does not provide the third claim. -/

example : PinchThirdEventPositiveStmt.{u} → PinchSecondEventPositiveStmt.{u} := by
  intro h
  obtain ⟨U, V, W, T, Q', Q, δ, hconfig, hpos⟩ := h
  refine ⟨U, V, W, T, Q', Q, δ, hconfig, ?_⟩
  intro γ ξ hγ hγ₂ Ω inst P hC hcirc μ D hgff hμ hD M hM
  obtain ⟨A, hA, hmeas, hp⟩ := hpos γ ξ hγ hγ₂ Ω P hC hcirc μ D hgff hμ hD M hM
  exact ⟨A, fun ω hω => ⟨(hA hω).1, (hA hω).2.1⟩, hmeas, hp⟩

/-- A common contraction requires the two strict margins simultaneously. -/
example {a c h b : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hh : 0 < h) (hb : 0 < b) :
    (∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ a < q * b ∧ q * c < h) ↔
      a < b ∧ a * c < b * h :=
  pinch_contraction_iff_product_bound ha hc hh hb

end HarmonicBalls.Section11PinchPositivityAudit
