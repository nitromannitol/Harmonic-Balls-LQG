import HarmonicBalls.Proofs.Sec11.PinchActualThirdProbability
import HarmonicBalls.Proofs.Sec11.PinchActualFirstTwoPositive

/-! # Positive probability of all three local pinch events -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- The three local pinch events have positive joint probability for the inserted
measure and metric of the same field. -/
theorem IsWholePlaneGFF.pinchLocal_three_positive
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α M δ : ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {U V W T Qprime Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hgeo : IsBufferedPinchGeometry U V W T Qprime Q δ)
    (hconfig : IsPinchPointProofConfiguration U V W T Qprime Q δ) :
    0 < P {ω | pinchFirstEventLocal (D ω) W T Qprime Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧
      pinchThirdEventLocal (D ω) V W δ} := by
  exact hh.pinchLocal_three_positive_of_first_two hμ hγ hγ₂ hα hD hgeo hconfig
    (hh.pinchLocal_first_two_positive hγ hγ₂ hα hμ hD hgeo)


/-- The local triple event contains a measurable set of positive probability. -/
theorem IsWholePlaneGFF.pinchLocal_three_exists_measurable_pos
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α M δ : ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {U V W T Qprime Q : Set ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α hC D)
    (hgeo : IsBufferedPinchGeometry U V W T Qprime Q δ)
    (hconfig : IsPinchPointProofConfiguration U V W T Qprime Q δ) :
    ∃ A ⊆ {ω | pinchFirstEventLocal (D ω) W T Qprime Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧
      pinchThirdEventLocal (D ω) V W δ}, MeasurableSet A ∧ 0 < P A := by
  have hDfield := hD
  obtain ⟨𝔇, h𝔇, _⟩ := hDfield
  have hξ := (isLQGMetric_xi_pos γ ξ 𝔇 hγ hγ₂ h𝔇).le
  let I := S11az.pinchCountSets V W T Qprime Q δ
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  let haxioms := lqgMetricFieldAxiomsUnivFrozen_derived Ω P γ ξ α hC hcirc
  obtain ⟨domain, pair, R, hR, _, _, hd, hlaw⟩ :=
    hh.exists_joint_smooth_shift_law_and_aemeasurable_for_pinch_coordinates
      hμ hγ hγ₂ hα hD haxioms hgeo I ψ hψ hψint hξ
  obtain ⟨_, _, hXm, _⟩ := hlaw ψ hψ
  let X := fun ω =>
    (localModConstPairings α hC (ball 0 7) ω, normalizedRestriction (μ ω) (ball 0 R),
      fun n => ENNReal.ofReal (Real.exp (ξ * (-hC ω ψ))) *
        internalMetric (D ω) (domain n) (pair n).1 (pair n).2)
  let F := (univ : Set (LocalZeroMeanTest (ball (0 : ℂ) 7) → ℝ)) ×ˢ
    pinchCoordinateEvent (U := U) I domain pair M
  have hE : MeasurableSet (univ : Set (LocalZeroMeanTest (ball (0 : ℂ) 7) → ℝ)) :=
    MeasurableSet.univ
  have hF : MeasurableSet F := hE.prod
    (measurableSet_pinchCoordinateEvent hgeo.isOpen_U.measurableSet I domain pair M)
  have hx := hh.ae_pinchCoordinateEvent_iff_localRule hμ hγ hγ₂ hα hD haxioms
    hgeo hR.1 I domain pair hd (fun ω => Real.exp (ξ * (-hC ω ψ)))
      (fun _ => Real.exp_pos _) M
  have heq : X ⁻¹' F =ᵐ[P] {ω | pinchFirstEventLocal (D ω) W T Qprime Q δ ∧
      pinchSecondEventLocal (μ ω) (D ω) U V δ M ∧
      pinchThirdEventLocal (D ω) V W δ} := by
    apply Filter.eventuallyEqSet_iff.mpr
    filter_upwards [hx] with ω hω
    simpa only [X, F, mem_preimage, mem_prod, mem_univ, true_and,
      S11m.LocalRule.pinchLocalRule] using hω
  have hn := (hXm.nullMeasurableSet_preimage hF).congr heq
  obtain ⟨A, hAsub, hA, hAe⟩ := hn.exists_measurable_subset_ae_eq
  refine ⟨A, hAsub, hA, ?_⟩
  rw [measure_congr hAe]
  exact hh.pinchLocal_three_positive hμ hγ hγ₂ hα hD hgeo hconfig

end HarmonicBalls
