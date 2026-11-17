import HarmonicBalls.Proofs.GFF.DMSInsertedMarkedLocalTransfer
import HarmonicBalls.Proofs.Sec8.SingularTypicalPointTransfer
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# Marked local identity for a singular Liouville measure

The singular Weyl weight identifies the actual Liouville measure and transfers
its marked local identity from the ordinary measure.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The singular Liouville measure is the weighted ordinary measure. -/
theorem IsWholePlaneGFF.ae_singular_eq_weighted_regular_measure
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) :
    ∀ᵐ ω ∂P, μ ω = (ν ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hμnon := Section6.ae_origin_nonatomic_of_stronger_existence P γ α ((α + lqgQ γ) / 2)
    hγ hγ2 (by linarith) (by linarith) hC hcirc
    (lqgMeasureExistence_derived P γ _ hC hcirc) μ hh hμ
  have hνnon := Section6.ae_origin_nonatomic_of_stronger_existence P γ 0 (lqgQ γ / 2)
    hγ hγ2 (by linarith) (by linarith) hC hcirc
    (lqgMeasureExistence_derived P γ _ hC hcirc) ν hh hν
  filter_upwards [hh.ae_singular_weight_of_existing_regular_measure hμ hν, hμnon, hνnon]
    with ω hw hμ0 hν0
  let w : Measure ℂ := (ν ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))
  have hw0 : w {0} = 0 := (withDensity_absolutelyContinuous (ν ω) _) hν0
  have hμae : ∀ᵐ z ∂μ ω, z ∈ ({0} : Set ℂ)ᶜ := by simpa [ae_iff] using hμ0
  have hwae : ∀ᵐ z ∂w, z ∈ ({0} : Set ℂ)ᶜ := by simpa [ae_iff] using hw0
  rw [Measure.restrict_eq_self_of_ae_mem hμae, Measure.restrict_eq_self_of_ae_mem hwae] at hw
  exact hw

/-- The marked local field of the singular measure has the corresponding
weighted rooted law, retaining the unnormalized measure and marked point. -/
theorem IsWholePlaneGFF.lintegral_singular_inserted_localModConstField_marked
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) (U : Set ℂ)
    (F : ModConstTestPairings U × ℂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, F (localModConstField α hC U ω, z) ∂(μ ω) ∂P =
      ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖z‖ ^ (-(γ * α))) * ∫⁻ ω,
        F (localModConstField α (fun _ : Unit => shiftedPairing γ z (hC ω)) U (), z) ∂P ∂volume := by
  let ρ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))
  have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  let G : ModConstTestPairings U × ℂ → ℝ≥0∞ := fun p => ρ p.2 * F p
  have hG : Measurable G := (hρ.comp measurable_snd).mul hF
  have hmarked := hh.lintegral_inserted_localModConstField_marked (α := α) hγ hγ2 hν U G hG
  calc
    _ = ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, G (localModConstField α hC U ω, z) ∂(ν ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hh.ae_singular_eq_weighted_regular_measure hγ hγ2 hα hμ hν] with ω hω
      rw [hω]
      change (∫⁻ z in ball (0 : ℂ) 1, F (localModConstField α hC U ω, z)
        ∂((ν ω).withDensity ρ)) = _
      exact setLIntegral_withDensity_eq_setLIntegral_mul _ hρ
        (hF.comp (measurable_const.prodMk measurable_id)) measurableSet_ball
    _ = _ := by
      rw [hmarked]
      refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
      exact lintegral_const_mul' (ρ z) _ ENNReal.ofReal_ne_top

end HarmonicBalls
