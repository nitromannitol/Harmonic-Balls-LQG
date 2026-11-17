import HarmonicBalls.Proofs.GFF.DMSActualRootedMarkedIdentity

/-!
# Marked local identity with an insertion

The ordinary marked identity applies to the actual field with a deterministic
logarithmic insertion, while retaining the ordinary Liouville measure and the
marked point.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- Insert the logarithmic singularity into the local mean-zero pairings. -/
def localLogInsertion (α : ℝ) (U : Set ℂ) (v : ModConstTestPairings U) :
    ModConstTestPairings U :=
  fun φ => v φ - α * ∫ x, φ.1 x * Real.log ‖x‖

/-- Logarithmic insertion is measurable on the local pairing space. -/
theorem measurable_localLogInsertion (α : ℝ) (U : Set ℂ) :
    Measurable (localLogInsertion α U) := by
  apply Measurable.of_eval
  intro φ
  exact (measurable_pi_apply φ).sub_const _

/-- The marked ordinary chaos law with the local field carrying an arbitrary
logarithmic insertion. The root and the unnormalized ordinary measure are retained. -/
theorem IsWholePlaneGFF.lintegral_inserted_localModConstField_marked
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) (U : Set ℂ)
    (F : ModConstTestPairings U × ℂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, F (localModConstField α hC U ω, z) ∂(μ ω) ∂P =
      ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω,
        F (localModConstField α (fun _ : Unit => shiftedPairing γ z (hC ω)) U (), z) ∂P ∂volume := by
  let G : ModConstTestPairings U × ℂ → ℝ≥0∞ :=
    fun p => F (localLogInsertion α U p.1, p.2)
  have hGm : Measurable G :=
    hF.comp (((measurable_localLogInsertion α U).comp measurable_fst).prodMk measurable_snd)
  have h := hG.lintegral_localModConstField_marked hγ0 hγ2 hμ U G hGm
  have hlocal (T : (ℂ → ℝ) → ℝ) :
      localLogInsertion α U (localModConstField 0 (fun _ : Unit => T) U ()) =
        localModConstField α (fun _ : Unit => T) U () := by
    funext φ
    simp [localLogInsertion, localModConstField, fieldPairing]
  have hlocalOmega (ω : Ω) :
      localLogInsertion α U (localModConstField 0 hC U ω) = localModConstField α hC U ω := by
    funext φ
    simp [localLogInsertion, localModConstField, fieldPairing]
  simpa only [G, hlocal, hlocalOmega] using h

end HarmonicBalls
