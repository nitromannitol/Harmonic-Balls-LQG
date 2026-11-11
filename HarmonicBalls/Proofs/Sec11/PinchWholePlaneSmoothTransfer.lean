import HarmonicBalls.Proofs.Sec11.JointContinuousBaseMetricShiftBetween
import HarmonicBalls.Proofs.Sec11.PinchNormalizedObservableTransfer
import HarmonicBalls.Proofs.Sec11.PinchWeightedReferenceBall
import HarmonicBalls.Proofs.Sec11.CorrectedPinchOpenThirdShift

/-! # Transfer of the strengthened pinch event under smooth shifts

The joint smooth-shift decoder uses Leonardo Bonanno’s
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- A smooth shift of the whole-plane field cannot create a positive-probability
strengthened pinch event when the original event has probability zero. -/
theorem IsCorrectedPinchConfiguration.positive_internal_pinch_of_wholePlane_smooth_shift
    {U V W T Q' Q : Set ℂ} {δ ξ γ α : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ A : Set ℂ, IsOpen A → A.Nonempty → 0 < μ ω A)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (g : ℂ → ℝ) (hg : IsTestFunction univ g)
    (hp : 0 < P {ω | pinchPointEventWithInternalBounds
      ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * g x))))
      (𝔇 (addFunPairing (hC ω) g)) U T Q' Q M 1 0}) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
  obtain ⟨R, hR, F, hF, hdec⟩ := hgff.exists_joint_measure_continuous_baseMetric_shift_decoder_between
    hμ hfull (a := 6) (ε := 7) (by norm_num) (by norm_num) 𝔇 h𝔇 ψ hψ hψint
  let X := localModConstPairings 0 hC univ
  let Y := localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => hC ω φ.1 - 0 * ∫ x, φ.1 x * Real.log ‖x‖)
    exact (hgff.measurable_pairing φ.1 φ.2.1).sub_const _
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + ∫ x, g x * φ.1 x) -
      0 * ∫ x, φ.1 x * Real.log ‖x‖)
    exact ((hgff.measurable_pairing φ.1 φ.2.1).add_const _).sub_const _
  have hztest : IsTestFunction univ (fun _ => 0) := by
    exact ⟨contDiff_const, HasCompactSupport.zero, subset_univ _⟩
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hz := (hdec (fun _ => 0) hztest).1
  simp [hzero] at hz
  obtain ⟨hs, hac, _⟩ := hdec g hg
  have hw := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
    (fun _ => g) (fun _ => hg.1.continuous) (fun _ => measurable_const)
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ hω => hω.isLocallyFiniteMeasure
  have hball := ae_referenceBall_pos_finite P μ hfull hloc
  have hweighted := hgff.ae_weighted_referenceBall_pos_finite hμ hfull g hg.1.continuous
  have hRpos : 0 < R := by linarith [hR.1]
  have hXeq : ∀ᵐ ω ∂P, 0 < Real.exp (ξ * (-hC ω ψ)) ∧
      μ ω (ball 0 R) ≠ 0 ∧ μ ω (ball 0 R) ≠ ∞ ∧
      ((F ∘ X) ω).1 = normalizedRestriction (μ ω) (ball 0 R) ∧
      ∀ x y, ((F ∘ X) ω).2 (x,y) = Real.exp (ξ * (-hC ω ψ)) * 𝔇 (hC ω) x y := by
    filter_upwards [hz.1, hz.2, hw, hball] with ω hzm hzd hw hb
    refine ⟨Real.exp_pos _, (hb R hRpos).1, (hb R hRpos).2, hzm, ?_⟩
    intro x y
    have hn : 0 ≤ 𝔇 (hC ω) x y := by
      have ht := hw.1.triangle x y x
      rw [hw.1.self_eq_zero, hw.1.symm y x] at ht
      linarith
    change (F (localModConstPairings 0 hC univ ω)).2 (x,y) = _
    rw [hzd x y]
    rw [mul_neg]
    have hval : weylScaling (𝔇 (hC ω)) ξ (fun _ => 0) x y =
        ENNReal.ofReal (𝔇 (hC ω) x y) := by
      simpa only [Pi.zero_def] using hw.2.2.1 x y
    rw [hval, ENNReal.toReal_ofReal hn]
  have hYeq : ∀ᵐ ω ∂P, 0 < Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z))) ∧
      ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * g x)))) (ball 0 R) ≠ 0 ∧
      ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * g x)))) (ball 0 R) ≠ ∞ ∧
      ((F ∘ Y) ω).1 = normalizedRestriction
        ((μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * g x)))) (ball 0 R) ∧
      ∀ x y, ((F ∘ Y) ω).2 (x,y) =
        Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z))) * 𝔇 (addFunPairing (hC ω) g) x y := by
    filter_upwards [hs, hw, hweighted] with ω hs hw hb
    refine ⟨Real.exp_pos _, (hb R hRpos).1, (hb R hRpos).2, hs.1, ?_⟩
    intro x y
    have hn : 0 ≤ 𝔇 (addFunPairing (hC ω) g) x y := by
      have ht := hw.2.1.triangle x y x
      rw [hw.2.1.self_eq_zero, hw.2.1.symm y x] at ht
      linarith
    change (F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω)).2 (x,y) = _
    rw [hs.2 x y, ← hw.2.2.2.1 x y, ENNReal.toReal_ofReal hn]
  apply positive_pinchEvent_of_normalized_observable_ac P
    h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration M 0 (by norm_num)
    (B := ball 0 R) (by simpa using ball_subset_ball (le_of_lt hR.1))
    μ (fun ω => (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * g x))))
    (fun ω => 𝔇 (hC ω)) (fun ω => 𝔇 (addFunPairing (hC ω) g))
    (F ∘ X) (F ∘ Y) (hF.comp hX) (hF.comp hY)
    (fun ω => Real.exp (ξ * (-hC ω ψ)))
    (fun ω => Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z))))
    (hw.mono fun _ hw => hw.1) (hw.mono fun _ hw => hw.2.1) hXeq hYeq hac hp

/-- The joint first and second auxiliary events imply the strengthened pinch
    event for the original whole-plane field and measure. -/
theorem IsCorrectedPinchConfiguration.positive_internal_pinch_of_open_first_second
    {U V W T Q' Q : Set ℂ} {δ ξ γ α : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ A : Set ℂ, IsOpen A → A.Nonempty → 0 < μ ω A)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (hA : 0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M}) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
  obtain ⟨g, hg, _, _, _, hp⟩ :=
    h.exists_positive_open_first_internal_pinch_shift hξ P γ M hC hcirc 𝔇 μ h𝔇 hgff hA
  exact h.positive_internal_pinch_of_wholePlane_smooth_shift P M hC hcirc 𝔇 μ
    h𝔇 hgff hμ hfull ψ hψ hψint g hg hp

end HarmonicBalls
