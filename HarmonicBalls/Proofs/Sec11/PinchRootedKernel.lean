import HarmonicBalls.Proofs.Sec11.PinchRootedTransfer
import HarmonicBalls.Proofs.Sec8.MeasurableStartingAtoms
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Sampling kernels for weighted random measures

A measurable density preserves almost-everywhere measurability of a random
measure. Its normalized restriction therefore has a finite sampling kernel,
even when the original random measure is only almost-everywhere measurable.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-- Weighting by a fixed measurable density is measurable as a map on the
space of measures. -/
theorem measurable_measure_withDensity (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    Measurable (fun μ : Measure ℂ => μ.withDensity w) := by
  rw [Measure.measurable_measure]
  intro S hS
  simp only [withDensity_apply _ hS, ← lintegral_indicator hS]
  exact Measure.measurable_lintegral (hw.indicator hS)

/-- The normalized weighted restriction, using a measurable representative
of the weighted random measure. -/
noncomputable def weightedRestrictionKernel
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    Kernel Ω ℂ :=
  let ν : Ω → Measure ℂ := fun ω => (μ ω).withDensity w
  let hν : AEMeasurable ν P := (measurable_measure_withDensity w hw).comp_aemeasurable hμ
  (normalizedRestrictionKernel B hB).comap (hν.mk ν) hν.measurable_mk

instance weightedRestrictionKernel_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    IsFiniteKernel (weightedRestrictionKernel P μ hμ B hB w hw) := by
  unfold weightedRestrictionKernel
  infer_instance

/-- The kernel agrees almost surely with the desired normalized weighted
restriction, including on samples of zero or infinite weighted mass. -/
theorem ae_weightedRestrictionKernel_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    ∀ᵐ ω ∂P, weightedRestrictionKernel P μ hμ B hB w hw ω =
      normalizedRestriction ((μ ω).withDensity w) B := by
  let ν : Ω → Measure ℂ := fun ω => (μ ω).withDensity w
  have hν : AEMeasurable ν P := (measurable_measure_withDensity w hw).comp_aemeasurable hμ
  filter_upwards [hν.ae_eq_mk] with ω hω
  change normalizedRestriction (hν.mk ν ω) B = normalizedRestriction (ν ω) B
  rw [hω]

/-- The LQG measure of a whole-plane GFF admits the weighted sampling kernel
without an additional random-measure measurability hypothesis. -/
theorem IsWholePlaneGFF.exists_finiteKernel_ae_normalized_weighted_restriction
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    ∃ κ : Kernel Ω ℂ, IsFiniteKernel κ ∧
      ∀ᵐ ω ∂P, κ ω = normalizedRestriction ((μ ω).withDensity w) B := by
  let hm := h.aemeasurable_lqgMeasure hμ
  exact ⟨weightedRestrictionKernel P μ hm B hB w hw, inferInstance,
    ae_weightedRestrictionKernel_eq P μ hm B hB w hw⟩

/-- The canonical sampling kernels discharge the kernel-identification part
of rooted transfer on a countable cover. -/
theorem ae_ae_of_rooted_weighted_cover_of_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : ℕ → Set ℂ) (hB : ∀ n, MeasurableSet (B n))
    (hcover : ∀ z, ∃ n, z ∈ B n) (w : ℕ → ℂ → ℝ≥0∞)
    (hw : ∀ n, Measurable (w n))
    (hpos : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (B n), w n z ≠ 0)
    (hfin : ∀ n, ∀ᵐ ω ∂P, ((μ ω).withDensity (w n)) (B n) ≠ ∞)
    (ν : ℕ → Measure (Ω × ℂ))
    (hac : ∀ n, P ⊗ₘ (weightedRestrictionKernel P μ hμ (B n) (hB n) (w n) (hw n)) ≪ ν n)
    {p : Ω → ℂ → Prop} (hp : ∀ n, ∀ᵐ x ∂ν n, p x.1 x.2) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p ω z := by
  let κ : ℕ → Kernel Ω ℂ := fun n =>
    weightedRestrictionKernel P μ hμ (B n) (hB n) (w n) (hw n)
  have (n : ℕ) : IsSFiniteKernel (κ n) := inferInstance
  exact ae_ae_of_rooted_weighted_cover P μ κ B hB hcover w hw hpos hfin
    (fun n => ae_weightedRestrictionKernel_eq P μ hμ (B n) (hB n) (w n) (hw n)) ν hac hp

#print axioms measurable_measure_withDensity
#print axioms ae_weightedRestrictionKernel_eq
#print axioms ae_ae_of_rooted_weighted_cover_of_aemeasurable
#print axioms IsWholePlaneGFF.exists_finiteKernel_ae_normalized_weighted_restriction

end HarmonicBalls
