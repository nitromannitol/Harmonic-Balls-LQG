import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.Steps.Sec11.PinchInternalDiam
import HarmonicBalls.FirstPass.S11an
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsConsequencesDerived
import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived
import HarmonicBalls.FirstPass.Phase2.DerivedInputs9
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-! # Local pinch certificates and conditional positivity -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter
open scoped ENNReal

/-- The internal diameter is unchanged by closing its endpoint set. -/
theorem IsEuclideanLengthMetric.internalDiam_closure_eq
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {δ : ℝ} (hδ : 0 < δ) (A : Set ℂ) :
    internalDiam D δ (closure A) = internalDiam D δ A := by
  have hnonneg (x y : ℂ) : 0 ≤ D x y := by
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  apply le_antisymm
  · unfold internalDiam at ⊢
    rw [thickening_closure]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    exact hD.internalMetric_le_internalDiam_of_mem_closure hnonneg isOpen_thickening
      (closure_subset_thickening hδ A) Subset.rfl hx hy
  · exact internalDiam_le_closure D δ A

/-- The second local certificate agrees with the open-endpoint version. -/
theorem pinchSecondEventLocal_iff_of_lengthMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {δ : ℝ} (hδ : 0 < δ)
    (μ : MeasureTheory.Measure ℂ) (U V : Set ℂ) (M : ℝ) :
    pinchSecondEventLocal μ D U V δ M ↔ pinchSecondEvent μ D U V δ M := by
  simp only [pinchSecondEventLocal, pinchSecondEvent, hD.internalDiam_closure_eq hδ V]

/-- The third local certificate agrees with the open-endpoint version. -/
theorem pinchThirdEventLocal_iff_of_lengthMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {δ : ℝ} (hδ : 0 < δ) (V W : Set ℂ) :
    pinchThirdEventLocal D V W δ ↔ pinchThirdEvent D V W δ := by
  simp only [pinchThirdEventLocal, pinchThirdEvent, hD.internalDiam_closure_eq hδ _]

/-- Conditional on positivity of the first two local certificates, the three
local certificates have positive probability for the field with insertion. -/
theorem pinchLocal_three_positive_conditional
    {U V W T Q' Q : Set ℂ} {δ γ α ξ M : ℝ}
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ) (hα : α < lqgQ γ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hDm : IsLQGMetricOfField P γ ξ α hC D)
    (h12 : 0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M}) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Q' Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧
      pinchThirdEventLocal (D ω) V W δ} := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    (S11ad.metric_locality_of_frozen lqgMetricFieldAxiomsUnivFrozen_derived γ ξ α hγ0 hγ2 hα
      Ω P hC hcirc D hGFF hDm).1
  obtain ⟨f, hf, hfC, hfc, hf0, hposS⟩ :=
    S11ad.exists_E3_shift_pos (γ := γ) hG D hmetric μ hξ h12 (fun _ h => h)
  obtain ⟨B, hB, hiff⟩ := S11an.pinchTriple_certificate
    lqgInternalMetricWeylAeMeasurableFrozen_derived
    MassFunctionalDerived.lqgMassFunctionalMeasurable_derived
    lqgMetricFieldAxiomsUnivFrozen_derived hG hγ0 hγ2 α hα Ω P hC hcirc D μ hGFF hDm hμ
  have hshift := S11an.hE3shift_of_frozen M
    S11aj.cameronMartinGFFReweighting_derived
    DerivedInputs9.cameronMartinGFFMutualAbsCont_derived
    weylScalingCompositionFrozen_holds lqgMetricFieldAxiomsUnivFrozen_derived
    (S11an.pinchTriple_stmt lqgInternalMetricWeylAeMeasurableFrozen_derived
      MassFunctionalDerived.lqgMassFunctionalMeasurable_derived
      lqgMetricFieldAxiomsUnivFrozen_derived hG hγ0 hγ2)
    hG hγ0 hγ2 hξ α hα P hC hcirc D μ hGFF hμ hDm
    (Section6.lqgMeasureWeylScaling Ω P γ α hC hcirc)
  obtain ⟨A, hAsub, _, hAp⟩ := cm_predicate_transfer
    DerivedInputs9.cameronMartinGFFMutualAbsCont_derived P hC hcirc hGFF f hfC hfc hf0
    (fun p : (ℂ → ℂ → ℝ) × Measure ℂ =>
      pinchFirstEventLocal p.1 W T Q' Q δ ∧ pinchSecondEventLocal p.2 p.1 U V δ M ∧
        pinchThirdEventLocal p.1 V W δ)
    (fun ω => (D ω, μ ω))
    (fun ω => (fun x y => (weylScaling (D ω) ξ f x y).toReal,
      (μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))))
    B hB (hiff.mono fun _ h => h.mp) (hshift f hf B hB hiff) hposS
  exact lt_of_lt_of_le hAp (measure_mono hAsub)

end HarmonicBalls
