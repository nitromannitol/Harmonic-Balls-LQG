import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstNormalizedTransfer
import HarmonicBalls.Proofs.Sec11.ContinuousBaseMetricShiftDecoder
import HarmonicBalls.Proofs.Sec11.SingularSmoothShiftPairing
import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift

/-! Transfer of the first pinch certificate under a smooth field shift.

The Cameron–Martin input uses Leonardo Bonanno’s
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- A deterministic smooth shift cannot create a positive-probability first
certificate when the unshifted certificate has probability zero. -/
theorem IsCorrectedPinchConfiguration.positive_open_first_of_wholePlane_smooth_shift
    {U V W T Q' Q : Set ℂ} {δ ξ γ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (g : ℂ → ℝ) (hg : IsTestFunction univ g)
    (hp : 0 < P {ω | correctedOpenFirstCertificate
      (𝔇 (addFunPairing (hC ω) g)) W T Q' Q δ}) :
    0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ} := by
  obtain ⟨F, hF, hFeq⟩ := hgff.exists_continuous_baseMetric_shift_decoder 𝔇 h𝔇 ψ hψ hψint
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
  have hac : P.map (F ∘ Y) ≪ P.map (F ∘ X) := by
    have hh := (hgff.singular_smooth_shift_modConst_pairing_laws hg 0 univ).1.map hF
    rw [Measure.map_map hF hY, Measure.map_map hF hX] at hh
    exact hh
  have hzero : (fun ω => addFunPairing (hC ω) (fun _ => 0)) = hC := by
    funext ω φ
    simp [addFunPairing]
  have hz := hFeq (fun _ => 0) continuous_const
  simp only [hzero, zero_mul, integral_zero, add_zero] at hz
  have hs := hFeq g hg.1.continuous
  have hw := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
    (fun _ => g) (fun _ => hg.1.continuous) (fun _ => measurable_const)
  have hn₀ : ∀ᵐ ω ∂P, 0 < Real.exp (ξ * (-hC ω ψ)) ∧ ∀ x y,
      (F ∘ X) ω (x,y) = Real.exp (ξ * (-hC ω ψ)) * 𝔇 (hC ω) x y := by
    filter_upwards [hz, hw] with ω hz hw
    refine ⟨Real.exp_pos _, ?_⟩
    intro x y
    have hn : 0 ≤ 𝔇 (hC ω) x y := by
      have ht := hw.1.triangle x y x
      rw [hw.1.self_eq_zero, hw.1.symm y x] at ht
      linarith
    change F (localModConstPairings 0 hC univ ω) (x,y) = _
    rw [hz x y]
    have hval : weylScaling (𝔇 (hC ω)) ξ (fun _ => 0) x y =
        ENNReal.ofReal (𝔇 (hC ω) x y) := by
      simpa only [Pi.zero_def] using hw.2.2.1 x y
    rw [hval, ENNReal.toReal_ofReal hn]
  have hn₁ : ∀ᵐ ω ∂P, 0 < Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z))) ∧ ∀ x y,
      (F ∘ Y) ω (x,y) = Real.exp (ξ * (-(hC ω ψ + ∫ z, g z * ψ z))) *
        𝔇 (addFunPairing (hC ω) g) x y := by
    filter_upwards [hs, hw] with ω hs hw
    refine ⟨Real.exp_pos _, ?_⟩
    intro x y
    have hn : 0 ≤ 𝔇 (addFunPairing (hC ω) g) x y := by
      have ht := hw.2.1.triangle x y x
      rw [hw.2.1.self_eq_zero, hw.2.1.symm y x] at ht
      linarith
    change F (localModConstPairings 0 (fun ω => addFunPairing (hC ω) g) univ ω) (x,y) = _
    rw [hs x y, ← hw.2.2.2.1 x y, ENNReal.toReal_ofReal hn]
  exact h.positive_open_first_of_normalized_ac P (fun ω => 𝔇 (hC ω))
    (fun ω => 𝔇 (addFunPairing (hC ω) g)) (F ∘ X) (F ∘ Y)
    (hF.comp hX) (hF.comp hY) (hw.mono fun _ hw => hw.1)
    (hw.mono fun _ hw => hw.2.1) _ _ hn₀ hn₁ hac hp

end HarmonicBalls
