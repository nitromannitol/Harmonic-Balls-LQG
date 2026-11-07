import HarmonicBalls.Proofs.Sec11.PositiveMomentPinchLocality
import HarmonicBalls.Proofs.Sec11.BufferedPinchCanonicalLaw

/-! # Local witness from a buffered pinch event

The Section 8 inputs use Leonardo Bonanno's LatticeProb formalization.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- A joint buffered event and its metric-measure decoder supply the
positive internal-pinch event required for the local witness. The joint event,
shift-law domination, full support and positive diameter moments remain
explicit obligations; the metric-field axiom is staged for source review. -/
theorem IsPinchPointProofConfiguration.local_witness_of_buffered_event
    {U V W T Q' Q : Set ℂ} {δ ξ q b : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {γ : ℝ} (M p : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (haxioms : LQGMetricFieldAxioms P γ ξ γ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2) (hp : 0 < p)
    (hD : IsLQGMetricOfField P γ ξ γ hC D) (hμ : IsLQGMeasureOfField P γ γ hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ A : Set ℂ, IsOpen A → A.Nonempty → 0 < μ ω A)
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
    ∃ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 ∧
      ∃ (ε : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ε ∧
        ((∀ i, i ≤ N → (∫⁻ ω, (⨆ x ∈ closedBall (z i) ε,
          ⨆ y ∈ closedBall (z i) ε,
            internalMetric (𝔇 (hC ω)) (ball (z i) (2 * ε)) x y) ^ p ∂P) ≠ ∞) →
          (∃ E : Set Ω, MeasurableSet[Section6.fieldSigmaAlgebraModConst γ hC (ball 0 7)] E ∧
            0 < P E ∧ ∀ᵐ ω ∂P, ω ∈ E → pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0) ∧
          (∃ E ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0}, MeasurableSet E ∧ 0 < P E)) := by
  have hpos := h.positive_singular_internal_pinch_of_canonicalLaw hξ hq hq1 P γ γ M
    hC hcirc D μ haxioms hgff hγ hγ₂ (gamma_lt_lqgQ hγ hγ₂) hD X hX hdecode hshiftLaw hA
  exact exists_local_internal_pinch_liouvilleCharge_of_positive_moments P hC hcirc μ D
    h.toIsPinchPointConfiguration M p hgff hμ hfull haxioms hγ hγ₂ hξ hp hD hpos

#print axioms IsPinchPointProofConfiguration.local_witness_of_buffered_event

end HarmonicBalls
