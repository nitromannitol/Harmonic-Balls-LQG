import HarmonicBalls.Proofs.GFF.BonannoNormalizedVersion
import HarmonicBalls.Proofs.GFF.RandomContinuousShiftReconstruction
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate

/-! # Continuous shifts and circle averages

The distribution-valued GFF and circle-average results used here are due to
Leonardo Bonanno. The continuous shift may depend on the GFF. -/

noncomputable section
open MeasureTheory Filter
namespace HarmonicBalls

/-- The reconstructed GFF shifted by the actual continuous sample path. -/
def shiftedReconstructedGFF {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ)
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) : Ω → LQGMetric.DistC :=
  fun ω => reconstructedGFF hC ω + LQGMetric.ofCont (continuousShift f hf ω)

theorem IsWholePlaneGFF.measurable_shiftedReconstructedGFF
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) (hm : ∀ z, Measurable fun ω => f ω z) :
    Measurable (shiftedReconstructedGFF hC f hf) := by
  exact LQGMetric.measurable_addFun.comp
    (hh.measurable_reconstructedGFF.prodMk (measurable_continuousShift f hf hm))

/-- The witness for the continuous part is the original random function. -/
theorem IsWholePlaneGFF.shiftedReconstructedGFF_isGFFPlusCont
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) (hm : ∀ z, Measurable fun ω => f ω z) :
    LQGMetric.IsGFFPlusCont (shiftedReconstructedGFF hC f hf) P := by
  refine ⟨hh.measurable_shiftedReconstructedGFF f hf hm, continuousShift f hf,
    measurable_continuousShift f hf hm, ?_⟩
  have he : (fun ω => shiftedReconstructedGFF hC f hf ω -
      LQGMetric.ofCont (continuousShift f hf ω)) = reconstructedGFF hC := by
    funext ω
    exact add_sub_cancel_right _ _
  rw [he]
  exact hh.reconstructedGFF_normalized.1

/-- At a fixed positive circle, the shifted distribution has the expected average. -/
theorem IsWholePlaneGFF.ae_circleAvg_shiftedReconstructedGFF
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, LQGMetric.circleAvg (shiftedReconstructedGFF hC f hf ω) r z =
      hcirc ω r z + Real.circleAverage (f ω) z r := by
  filter_upwards [LQGMetric.CircleAvg.ae_tendsto_mollAvg
    hh.reconstructedGFF_normalized.1 z hr, hh.ae_circleAvg_reconstructedGFF hr z] with ω ⟨a, ha⟩ hc
  have ht : Tendsto (fun n => LQGMetric.CircleAvg.mollAvg
      (shiftedReconstructedGFF hC f hf ω - LQGMetric.ofCont (continuousShift f hf ω)) n z r)
      atTop (nhds a) := by
    simpa only [shiftedReconstructedGFF, add_sub_cancel_right] using ha
  have he := (LQGMetric.CircleAvg.circleAvg_eq_sub_ofCont_add ht).2
  simpa only [shiftedReconstructedGFF, add_sub_cancel_right, ← hc,
    continuousShift, ContinuousMap.coe_mk] using he

/-- Unit-circle centering subtracts the shifted field's own unit-circle average. -/
theorem IsWholePlaneGFF.ae_centered_circleAvg_shiftedReconstructedGFF
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, LQGMetric.circleAvg (shiftedReconstructedGFF hC f hf ω) r z -
        LQGMetric.circleAvg (shiftedReconstructedGFF hC f hf ω) 1 0 =
      hcirc ω r z + Real.circleAverage (f ω) z r - Real.circleAverage (f ω) 0 1 := by
  filter_upwards [hh.ae_circleAvg_shiftedReconstructedGFF f hf hr z,
    hh.ae_circleAvg_shiftedReconstructedGFF f hf one_pos 0,
    hh.ae_circleAvg_reconstructedGFF one_pos 0,
    hh.ae_circleAvg_one_zero_reconstructedGFF] with ω h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, zero_add]

#print axioms IsWholePlaneGFF.measurable_shiftedReconstructedGFF
#print axioms IsWholePlaneGFF.shiftedReconstructedGFF_isGFFPlusCont
#print axioms IsWholePlaneGFF.ae_circleAvg_shiftedReconstructedGFF
#print axioms IsWholePlaneGFF.ae_centered_circleAvg_shiftedReconstructedGFF
end HarmonicBalls
