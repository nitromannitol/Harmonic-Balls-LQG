import HarmonicBalls.Proofs.Sec11.PinchJointEventAE
import HarmonicBalls.Proofs.Sec11.PinchUnnormalizedKernel

/-! # Rooted transfer of strengthened pinch block densities

A common dominating law permits a single event representative to be used
under both the original and the fixed-root comparison laws. The rooted
comparison itself remains a hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-- A fixed-root block-density bound transfers to measure-typical points when
the original law and comparison laws are dominated by a common law under
which the metric and measure have the required measurable representatives.
The same deterministic rate is required at all localizations. -/
theorem ae_ae_internal_pinch_block_density_of_dominated_rooted_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (S : Measure Ω) (hPdom : P ≪ S)
    (hμS : AEMeasurable μ S) (hlocS : ∀ᵐ ω ∂S, IsLocallyFiniteMeasure (μ ω))
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetricS : ∀ᵐ ω ∂S, IsEuclideanLengthMetric (D ω))
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M q : ℝ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (R : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ S)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M (r k) z}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M (r k) z}.ncard : ℝ) := by
  obtain ⟨F, hF, hFae⟩ := exists_jointlyMeasurable_internal_pinch_block_density
    S hconfig M q r hr hD hmetricS hμS hlocS
  have hfixedF : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z), (ω, z) ∈ F := by
    intro n
    filter_upwards [hdom n, hfixed n] with z hdomz hfixedz
    filter_upwards [hdomz.ae_le hFae, hfixedz] with ω hω hz
    exact (hω z).2 hz
  have htarget : ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, (ω, z) ∈ F :=
    ae_ae_of_unnormalized_shiftedRootReferenceLaw P μ hμ hloc w hw hpos hfin
      ρ shift hshift R hF hrooted hac hfixedF
  filter_upwards [hPdom.ae_le hFae, htarget] with ω hω hz
  filter_upwards [hz] with z hz
  exact (hω z).1 hz

/-- Under the same dominated rooted comparison, an internal pinch-density
bound implies the block-density bound for the original pinch event. -/
theorem ae_ae_pinch_block_density_of_dominated_rooted_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (S : Measure Ω) (hPdom : P ≪ S)
    (hμS : AEMeasurable μ S) (hlocS : ∀ᵐ ω ∂S, IsLocallyFiniteMeasure (μ ω))
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetricS : ∀ᵐ ω ∂S, IsEuclideanLengthMetric (D ω))
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M q : ℝ) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (R : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ S)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ k) z}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ k) z}.ncard : ℝ) := by
  have hr (n : ℕ) : 0 < ((2 : ℝ)⁻¹ ^ n) := pow_pos (by norm_num) n
  have h := ae_ae_internal_pinch_block_density_of_dominated_rooted_law
    P hμ hloc S hPdom hμS hlocS hD hmetricS hconfig M q _ hr w hw hpos hfin
    ρ shift hshift R hrooted hac hdom hfixed
  filter_upwards [hPdom.ae_le hmetricS, h] with ω hmetric hω
  filter_upwards [hω] with z hz
  exact eventually_pinchPointEvent_block_ncard_of_internalBounds hmetric hz


end HarmonicBalls
