import HarmonicBalls.Proofs.Sec11.PinchDominatingLaw
import HarmonicBalls.Steps.Sec11.PinchLocalDensityTransfer
import HarmonicBalls.Steps.Sec11.PinchCommonLocalIndicator

/-! # Rooted transfer from local comparisons

A fixed-root density estimate transfers to the rooted law using only local
absolute continuity and a common local representative at sufficiently small
scales. The comparison and representative hypotheses remain explicit.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

open Classical in
/-- Transfer fixed-root density through local comparisons and then through a
countably dominated rooted law. -/
theorem ae_ae_pinch_block_density_of_rooted_local_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (ν : ℕ → Measure Ω) (hμν : ∀ n, AEMeasurable μ (ν n))
    (hlocν : ∀ n, ∀ᵐ ω ∂(ν n), IsLocallyFiniteMeasure (μ ω))
    (hmetricν : ∀ n, ∀ᵐ ω ∂(ν n), IsEuclideanLengthMetric (D ω))
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M q : ℝ) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (R L : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ ν n)
    (hlocal : ∀ n, ∀ᵐ z ∂ρ n, ∃ (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
        (K : ℕ),
      (∀ k, K ≤ k → ∃ A : Set Ω, MeasurableSet[m] A ∧
        ∀ᵐ ω ∂(R n z + L n z),
          (pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
            ((2 : ℝ)⁻¹ ^ k) z ↔ ω ∈ A)) ∧
      (R n z).trim hm ≪ (L n z).trim hm)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(L n z), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ k) z}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ k) z}.ncard : ℝ) := by
  apply ae_ae_pinch_block_density_of_countably_dominated_rooted_law P hμ hloc hD hmetric
    ν hμν hlocν hmetricν hconfig M q w hw hpos hfin ρ shift hshift R hrooted hac hdom
  intro n
  filter_upwards [hlocal n, hfixed n] with z hz hf
  obtain ⟨m, hm, K, hE, hRL⟩ := hz
  obtain ⟨X, hX, hR, hL⟩ :=
    @exists_common_local_tail_indicators Ω mΩ (R n z) (L n z) m K
      (fun k ω => pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ k) z) hE
  exact @ae_eventually_block_density_of_local_absolutelyContinuous Ω mΩ (R n z) (L n z) m hm K X
    (fun k ω => pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ k) z)
    q hX hR hL hRL hf

#print axioms ae_ae_pinch_block_density_of_rooted_local_comparison

end HarmonicBalls
