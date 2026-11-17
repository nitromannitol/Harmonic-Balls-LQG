import HarmonicBalls.Proofs.GFF.DMSWholePlaneMarkedChainProved
import HarmonicBalls.FirstPass.S11i.Faithful

/-!
# Marked local field identity

The whole-plane marked identity projects to the field restricted to any set modulo additive constants, with the
marked point and the unnormalized Liouville measure retained.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- Restriction of a pairing functional to mean-zero test functions is measurable for the global pairing σ-algebra. -/
theorem measurable_localModConstField_pairing (U : Set ℂ) :
    Measurable[pairingMeasSpace] (fun T : (ℂ → ℝ) → ℝ =>
      localModConstField 0 (fun _ : Unit => T) U ()) := by
  let : MeasurableSpace ((ℂ → ℝ) → ℝ) := pairingMeasSpace
  refine Measurable.of_eval fun φ => ?_
  have hφ : IsTestFunction univ φ.1 := ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩
  have hm : Measurable[pairingMeasSpace] (fun T : (ℂ → ℝ) → ℝ => T φ.1) := by
    rw [measurable_iff_comap_le]
    exact le_iSup₂_of_le φ.1 hφ le_rfl
  simpa only [localModConstField, fieldPairing, zero_mul, sub_zero] using hm

/-- The ordinary whole-plane field, weighted by its Liouville measure on the unit disk, has the marked local law of
its logarithmically inserted field. The observable may depend jointly on the marked point and all mean-zero local
test pairings. -/
theorem IsWholePlaneGFF.lintegral_localModConstField_marked
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) (U : Set ℂ)
    (F : ModConstTestPairings U × ℂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, F (localModConstField 0 hC U ω, z) ∂(μ ω) ∂P =
      ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω,
        F (localModConstField 0 (fun _ : Unit => shiftedPairing γ z (hC ω)) U (), z) ∂P ∂volume := by
  have hΨ : Measurable[MeasurableSpace.prod pairingMeasSpace inferInstance]
      (fun p : ((ℂ → ℝ) → ℝ) × ℂ =>
        F (localModConstField 0 (fun _ : Unit => p.1) U (), p.2)) :=
    hF.comp (((measurable_localModConstField_pairing U).comp measurable_fst).prodMk measurable_snd)
  have h := stepM_holds P hγ0 hγ2 hC hcirc μ hG hμ
    (fun T z => F (localModConstField 0 (fun _ : Unit => T) U (), z)) hΨ
  calc
    _ = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω,
        F (localModConstField 0 (fun _ : Unit => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) U (), z)
        ∂P ∂volume := h
    _ = _ := by
      refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
      refine lintegral_congr_ae ?_
      filter_upwards [dmsShiftedPairing_ae_eq hG γ (le_of_lt (mem_ball_zero_iff.1 hz))] with ω hω
      rw [hω]
      rfl

end HarmonicBalls
