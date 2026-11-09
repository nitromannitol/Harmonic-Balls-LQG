import HarmonicBalls.Defs.LQG
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Proposition 11.7, dilation of the LQG approximations (fp-S11c, owner n1)

FIRST-PASS NEW (deterministic). The approximation `ε^{γ²/2} e^{γ h_ε(z)} dz` of the LQG measure (paper eq:measure-lim,
line 396; `lqgApprox`, Defs/LQG.lean:46) is covariant under the dilation `z ↦ z/2` of the circle profile, up to a constant
(paper line 422: the first properties of the LQG measure are immediate from the definition). Precisely, with the
normalized dilation `h'_e(z) = h_e(z/2) - c` of the circle profile (`continuousCircleAffine (1/2) 0`, which subtracts the
value at `(1/2, 0)`):

`lqgApprox γ h' ε A = 4 · 2^{γ²/2} · e^{-γc} · lqgApprox γ h (ε/2) (σ⁻¹ A)`, with `σ w = 2w`.

The proof is the substitution `z = 2w` (`dz = 4 dw` on `ℂ`), i.e. `volume = 4 • map σ volume`.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- The push-forward of Lebesgue measure on `ℂ` under the dilation `w ↦ 2w` is `1/4` times Lebesgue measure. -/
lemma volume_map_two_smul :
    (volume : Measure ℂ).map (fun w : ℂ => (2 : ℝ) • w) = ENNReal.ofReal (1 / 4) • (volume : Measure ℂ) := by
  ext B hB
  rw [Measure.map_apply (measurable_const_smul (2 : ℝ)) hB, Measure.smul_apply, smul_eq_mul]
  rw [Measure.addHaar_preimage_smul volume (hr := (by norm_num : (2 : ℝ) ≠ 0)) B]
  rw [Complex.finrank_real_complex]
  norm_num

/-- Substitution `z = 2w` for lower integrals on `ℂ`: `∫ G dz = 4 ∫ G(2w) dw`. -/
lemma lintegral_eq_four_mul_comp_two_smul (G : ℂ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ z, G z = 4 * ∫⁻ w, G ((2 : ℝ) • w) := by
  have h4 : (volume : Measure ℂ) = ENNReal.ofReal 4 • (volume : Measure ℂ).map (fun w : ℂ => (2 : ℝ) • w) := by
    rw [volume_map_two_smul, smul_smul]
    rw [show ENNReal.ofReal 4 * ENNReal.ofReal (1 / 4) = 1 by
      rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num, one_smul]
  have hlhs : ∫⁻ z, G z = ∫⁻ z, G z ∂(ENNReal.ofReal 4 • (volume : Measure ℂ).map (fun w : ℂ => (2 : ℝ) • w)) := by
    rw [← h4]
  rw [hlhs, lintegral_smul_measure, lintegral_map hG (measurable_const_smul (2 : ℝ))]
  rw [ENNReal.ofReal_ofNat]
  rfl

/-- Dilation covariance of the LQG approximation: the normalized dilation `h'_e(z) = h_e(z/2) - c` of the circle profile
gives `lqgApprox γ h' ε = 4 · 2^{γ²/2} · e^{-γc} · (dilated lqgApprox γ h (ε/2))`. -/
theorem lqgApprox_dilate_eq (γ c ε : ℝ) (hε : ℝ → ℂ → ℝ) (hεpos : 0 < ε) (hmeas : Measurable (hε (ε / 2)))
    {A : Set ℂ} (hA : MeasurableSet A) :
    lqgApprox γ (fun e z => hε (e / 2) (z / 2) - c) ε A =
      ENNReal.ofReal (4 * 2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * c))) *
        lqgApprox γ hε (ε / 2) ((fun w : ℂ => (2 : ℝ) • w) ⁻¹' A) := by
  have hσ : Measurable (fun w : ℂ => (2 : ℝ) • w) := measurable_const_smul (2 : ℝ)
  have hA' : MeasurableSet ((fun w : ℂ => (2 : ℝ) • w) ⁻¹' A) := hA.preimage hσ
  have hpt : ∀ w : ℂ, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hε (ε / 2) (((2 : ℝ) • w) / 2) - c)))
      = ENNReal.ofReal (2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * c))) *
        ENNReal.ofReal ((ε / 2) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (ε / 2) w)) := by
    intro w
    have hdiv : ((2 : ℝ) • w) / 2 = w := by
      rw [Complex.real_smul]
      push_cast
      ring
    rw [hdiv, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.div_rpow hεpos.le (by norm_num : (0 : ℝ) ≤ 2)]
    have h2p : (2 : ℝ) ^ (γ ^ 2 / 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    have hexp : γ * (hε (ε / 2) w - c) = γ * hε (ε / 2) w + -(γ * c) := by ring
    rw [hexp, Real.exp_add]
    field_simp
  have hm1 : Measurable (fun z : ℂ => hε (ε / 2) (z / 2) - c) :=
    (hmeas.comp (measurable_id.div_const 2)).sub_const c
  have hm2 : Measurable (fun z : ℂ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hε (ε / 2) (z / 2) - c)))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hm1)))
  unfold lqgApprox
  rw [withDensity_apply _ hA, withDensity_apply _ hA']
  rw [← lintegral_indicator hA, ← lintegral_indicator hA', lintegral_eq_four_mul_comp_two_smul _ (hm2.indicator hA)]
  have hind : ∀ w : ℂ, A.indicator (fun z : ℂ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hε (ε / 2) (z / 2) - c))))
      ((2 : ℝ) • w) = ENNReal.ofReal (2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * c))) *
        ((fun w : ℂ => (2 : ℝ) • w) ⁻¹' A).indicator
          (fun w : ℂ => ENNReal.ofReal ((ε / 2) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (ε / 2) w))) w := by
    intro w
    by_cases hw : (2 : ℝ) • w ∈ A
    · have hw' : w ∈ (fun w : ℂ => (2 : ℝ) • w) ⁻¹' A := hw
      rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw']
      exact hpt w
    · have hw' : w ∉ (fun w : ℂ => (2 : ℝ) • w) ⁻¹' A := hw
      rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw', mul_zero]
  rw [lintegral_congr hind, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 ^ (γ ^ 2 / 2) by positivity)]
  rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 * 2 ^ (γ ^ 2 / 2) by positivity)]
  rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num), ENNReal.ofReal_ofNat]
  ring

/-- The same identity as a measure identity: the approximation of the normalized dilated profile is the push-forward of
the approximation of the profile under `w ↦ 2w`, times `4 · 2^{γ²/2} · e^{-γc}`. -/
theorem lqgApprox_dilate_map (γ c ε : ℝ) (hε : ℝ → ℂ → ℝ) (hεpos : 0 < ε) (hmeas : Measurable (hε (ε / 2))) :
    lqgApprox γ (fun e z => hε (e / 2) (z / 2) - c) ε =
      ENNReal.ofReal (4 * 2 ^ (γ ^ 2 / 2) * Real.exp (-(γ * c))) •
        (lqgApprox γ hε (ε / 2)).map (fun w : ℂ => (2 : ℝ) • w) := by
  ext A hA
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (measurable_const_smul (2 : ℝ)) hA]
  exact lqgApprox_dilate_eq γ c ε hε hεpos hmeas hA

end HarmonicBalls
