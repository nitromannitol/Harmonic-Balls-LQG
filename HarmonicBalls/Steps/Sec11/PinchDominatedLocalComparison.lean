import HarmonicBalls.Steps.Sec11.PinchLocalPairingComparison
import HarmonicBalls.Steps.Sec11.PinchGermIndicator

/-! # Local comparison through a dominating GFF law

A single law on which the field, measure, and metric satisfy the staged LQG
locality assumptions supplies representatives simultaneously for any two
laws dominated by it. This is a sufficient condition; it does not assert
that the rooted comparison laws have such a domination.
-/

namespace HarmonicBalls

open Set Metric Filter MeasureTheory Topology

/-- A dominating GFF law supplies common local pinch-event representatives.
The comparison of local pairing laws remains an explicit hypothesis. -/
theorem exists_pinch_tail_local_comparison_of_dominating_gff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q S : Measure Ω)
    {γ ξ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {U T Q' V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' V)
    (M : ℝ) (z : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hgff : IsWholePlaneGFF S hC hcirc) (hμ : IsLQGMeasureOfField S γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField S γ ξ α₀ hC D)
    (hmloc : LQGMeasureLocality S γ α₀ hC hcirc)
    (haxioms : LQGMetricFieldAxioms S γ ξ α₀ hC hcirc)
    (hPS : P ≪ S) (hQS : Q ≪ S)
    (hAC : P.map (localFieldPairings α₀ hC (ball z ε)) ≪
      Q.map (localFieldPairings α₀ hC (ball z ε))) :
    ∃ K : ℕ,
      (∀ k, K ≤ k → ∃ A : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball z ε)] A ∧
        ∀ᵐ ω ∂(P + Q),
          (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' V M
            ((2 : ℝ)⁻¹ ^ k) z ↔ ω ∈ A)) ∧
      P.trim (hgff.fieldSigmaAlgebra_le α₀ (ball z ε)) ≪
        Q.trim (hgff.fieldSigmaAlgebra_le α₀ (ball z ε)) := by
  have hlim : Tendsto (fun k : ℕ => 6 * ((2 : ℝ)⁻¹ ^ k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 6
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds hε))
  refine ⟨K, ?_, fieldSigmaAlgebra_trim_absolutelyContinuous_of_pairing_law P Q α₀ hC _
    (hgff.fieldSigmaAlgebra_le α₀ _) hAC⟩
  intro k hk
  obtain ⟨A, hA, hAeq⟩ := @exists_local_lqg_pinchEvent_representative Ω mΩ S γ ξ α₀
    hC hcirc D μ U T Q' V hconfig M z ((2 : ℝ)⁻¹ ^ k) (by positivity)
    hγ hγ₂ hα hgff hμ hD hmloc haxioms
  refine ⟨A, (fieldSigmaAlgebra_mono α₀ hC (ball_subset_ball (le_of_lt (hK k hk)))) _ hA, ?_⟩
  exact ae_add_measure_iff.mpr ⟨hPS.ae_le hAeq, hQS.ae_le hAeq⟩


end HarmonicBalls
