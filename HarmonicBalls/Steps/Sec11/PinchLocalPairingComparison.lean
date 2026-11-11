import HarmonicBalls.Steps.Sec11.LocalPairingLaw
import HarmonicBalls.Steps.Sec11.PinchLocalEvent

/-! # Local pairing comparison for pinch events

Local representatives under the sum of the rooted and reference laws give
one representative valid under both. Their local field laws can be compared
through the joint process of test-function pairings.
-/

namespace HarmonicBalls

open Set Metric Filter MeasureTheory Topology
open scoped ENNReal

/-- Local metric, potential, and mass representatives under the sum law,
together with local pairing-law absolute continuity, supply the local
comparison required by rooted pinch-scale transfer. -/
theorem exists_pinch_tail_local_comparison_of_pairing_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q : Measure Ω)
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {U T Q' V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' V)
    (M α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (z : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hm : fieldSigmaAlgebra α₀ hC (ball z ε) ≤ mΩ)
    (hAC : P.map (localFieldPairings α₀ hC (ball z ε)) ≪
      Q.map (localFieldPairings α₀ hC (ball z ε)))
    (hD : ∀ᵐ ω ∂(P + Q), IsEuclideanLengthMetric (D ω))
    (hdata : ∀ k : ℕ, 6 * ((2 : ℝ)⁻¹ ^ k) < ε →
      ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
        (∀ x y, Measurable[fieldSigmaAlgebra α₀ hC (ball z ε)] fun ω => G ω x y) ∧
        (∀ᵐ ω ∂(P + Q), ∀ x ∈ ball z (6 * ((2 : ℝ)⁻¹ ^ k)),
          ∀ y ∈ ball z (6 * ((2 : ℝ)⁻¹ ^ k)),
            internalMetric (D ω) (ball z (6 * ((2 : ℝ)⁻¹ ^ k))) x y = G ω x y) ∧
        (∃ Y : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC (ball z ε)] Y ∧
          ∀ᵐ ω ∂(P + Q), annulusGreenPotentialSup (μ ω) z
            (3 * ((2 : ℝ)⁻¹ ^ k)) (6 * ((2 : ℝ)⁻¹ ^ k)) = Y ω) ∧
        (∃ Y : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC (ball z ε)] Y ∧
          ∀ᵐ ω ∂(P + Q), μ ω (rescaledSet U ((2 : ℝ)⁻¹ ^ k) z) = Y ω)) :
    ∃ K : ℕ,
      (∀ k, K ≤ k → ∃ A : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball z ε)] A ∧
        ∀ᵐ ω ∂(P + Q),
          (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' V M
            ((2 : ℝ)⁻¹ ^ k) z ↔ ω ∈ A)) ∧
      P.trim hm ≪ Q.trim hm := by
  have hlim : Tendsto (fun k : ℕ => 6 * ((2 : ℝ)⁻¹ ^ k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 6
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨K, ?_, fieldSigmaAlgebra_trim_absolutelyContinuous_of_pairing_law P Q α₀ hC _ hm hAC⟩
  intro k hk
  obtain ⟨G, hG, hGeq, hgreen, hmass⟩ := hdata k (hK k hk)
  exact @exists_local_pinchEvent_representative Ω mΩ (P + Q)
    (fieldSigmaAlgebra α₀ hC (ball z ε)) D μ G U T Q' V hconfig M z
    ((2 : ℝ)⁻¹ ^ k) (by positivity) hD hG hGeq hgreen hmass


end HarmonicBalls
