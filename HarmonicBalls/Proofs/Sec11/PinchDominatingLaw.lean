import HarmonicBalls.Proofs.Sec11.PinchRootedJointEvent
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! # Countable dominating laws for rooted comparison

A countable sum of comparison laws and the original law provides a common
law under which one can construct the event representative. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-- A countable family of laws has a common dominating law, preserving
almost-everywhere measurability and two almost-everywhere properties. -/
theorem exists_common_dominating_law
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) (ν : ℕ → Measure Ω) (f : Ω → A) (p q : Ω → Prop)
    (hfP : AEMeasurable f P) (hfν : ∀ n, AEMeasurable f (ν n))
    (hpP : ∀ᵐ ω ∂P, p ω) (hpν : ∀ n, ∀ᵐ ω ∂(ν n), p ω)
    (hqP : ∀ᵐ ω ∂P, q ω) (hqν : ∀ n, ∀ᵐ ω ∂(ν n), q ω) :
    ∃ S : Measure Ω, P ≪ S ∧ (∀ n, ν n ≪ S) ∧ AEMeasurable f S ∧
      (∀ᵐ ω ∂S, p ω) ∧ ∀ᵐ ω ∂S, q ω := by
  let S := P + Measure.sum ν
  have hP : P ≪ S := Measure.AbsolutelyContinuous.rfl.add_right _
  have hν (n : ℕ) : ν n ≪ S :=
    (Measure.absolutelyContinuous_sum_right n Measure.AbsolutelyContinuous.rfl).add_right' P
  refine ⟨S, hP, hν, ?_, ?_, ?_⟩
  · exact hfP.add_measure (aemeasurable_sum_measure_iff.mpr hfν)
  · exact ae_add_measure_iff.mpr ⟨hpP, Measure.ae_sum_iff.mpr hpν⟩
  · exact ae_add_measure_iff.mpr ⟨hqP, Measure.ae_sum_iff.mpr hqν⟩

/-- Rooted transfer when each root-dependent comparison law is dominated by
one member of a countable family. No common dominating law need be supplied. -/
theorem ae_ae_pinch_block_density_of_countably_dominated_rooted_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
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
    (hshift : ∀ n, Measurable (shift n)) (R : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ ν n)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z), ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ k) z}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ k) z}.ncard : ℝ) := by
  obtain ⟨S, hPS, hνS, hμS, hlocS, hmetricS⟩ := exists_common_dominating_law P ν μ
    (fun ω => IsLocallyFiniteMeasure (μ ω)) (fun ω => IsEuclideanLengthMetric (D ω))
    hμ hμν hloc hlocν hmetric hmetricν
  have hRS : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ S := by
    intro n
    filter_upwards [hdom n] with z hz
    exact hz.trans (hνS n)
  exact ae_ae_pinch_block_density_of_dominated_rooted_law P hμ hloc S hPS hμS hlocS
    hD hmetricS hconfig M q w hw hpos hfin ρ shift hshift R hrooted hac hRS hfixed


end HarmonicBalls
