import HarmonicBalls.Proofs.Sec11.CorrectedPinchConditionalPositive
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstSecondNull

/-!
# Conditional growth chain for null-measurable inside events (Section 11, draft lines 447–513)

The growth chains `IsCorrectedPinchConfiguration.positive_wholePlane_first_second_of_growth`
(`Proofs/Sec11/CorrectedPinchFirstSecondGrowth.lean:13`) and
`IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth`
(`Proofs/Sec11/CorrectedPinchConditionalPositive.lean:13`) take the inside clause `hinside` with the strict
`MeasurableSet` in `m₀`. The producer `IsWholePlaneGFF.nullMeasurableSet_mass_internalDiam`
(`Proofs/Sec11/ConditionalCoreMeasurability.lean:26`) gives only `NullMeasurableSet`.

The null-measurable first-second chain `IsCorrectedPinchConfiguration.positive_wholePlane_first_second_null`
(`Proofs/Sec11/CorrectedPinchFirstSecondNull.lean:12`) already takes the null clause. This module adds the two
growth-form consumers with the null clause: the same proofs, with that consumer in place of the strict one. The
volume-growth input `LQGVolumeGrowthAllScalesStmt` and the full-support consequence are used exactly as in the
strict chain. The strict clause is therefore not needed in the raw-positivity route (point F2 of the status note).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Growth-form first-second positivity with the null-measurable inside clause. Same as
`IsCorrectedPinchConfiguration.positive_wholePlane_first_second_of_growth`
(`Proofs/Sec11/CorrectedPinchFirstSecondGrowth.lean:13`), with `hinside` in `NullMeasurableSet`. -/
theorem IsCorrectedPinchConfiguration.positive_wholePlane_first_second_of_growth_null
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ ξ γ α₀ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (M : ℝ)
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (hA : MeasurableSet[m] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ})
    (ha : @Measurable Ω ℝ≥0∞ m _ (fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ)))))
    (hb : @Measurable Ω ℝ≥0∞ m _ (fun ω =>
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6))
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  let : MeasurableSpace Ω := m₀
  exact h.positive_wholePlane_first_second_null hξ P hC hcirc 𝔇 μ h𝔇 hgff M m hm A hA
    hArep ha hb (ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth
      hgrowth hγ hγ₂ hα hgff hμ 3 (b := 6) (by norm_num)) hinside

#print axioms IsCorrectedPinchConfiguration.positive_wholePlane_first_second_of_growth_null

/-- Top-level pinch positivity with the null-measurable inside clause. Same as
`IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth`
(`Proofs/Sec11/CorrectedPinchConditionalPositive.lean:13`), with `hinside` in `NullMeasurableSet`. -/
theorem IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth_null
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ ξ γ α : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (M : ℝ) (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (hA : MeasurableSet[m] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ})
    (ha : @Measurable Ω ℝ≥0∞ m _ (fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ)))))
    (hb : @Measurable Ω ℝ≥0∞ m _ (fun ω =>
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6))
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
  let : MeasurableSpace Ω := m₀
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ₂ hα
    Ω P hC hcirc μ hgff hμ
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  exact h.positive_internal_pinch_of_open_first_second hξ P M hC hcirc 𝔇 μ h𝔇 hgff
    hμ hfull ψ hψ hψint
    (h.positive_wholePlane_first_second_of_growth_null hgrowth hξ hγ hγ₂ hα P hC hcirc
      𝔇 μ h𝔇 hgff hμ M m hm A hA hArep ha hb hinside)

#print axioms IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth_null

end HarmonicBalls
