import HarmonicBalls.Proofs.Potential.BrownianSingularOccupation
import HarmonicBalls.Proofs.Potential.BrownianOccupationNearDiagonal
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Subcritical singularly weighted Brownian pair occupation

Inverse-power occupation controls near-diagonal pairs for all subcritical exponents.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

private theorem lintegral_indicator_holder {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (f : α → ℝ≥0∞)
    (hf : Measurable f) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (∫⁻ x, s.indicator f x ∂μ) ≤
      (μ s) ^ (1 - a) * (∫⁻ x, (f x) ^ (1 / a) ∂μ) ^ a := by
  classical
  let g : α → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hs
  have hp : (1 / (1 - a)).HolderConjugate (1 / a) := by
    rw [Real.holderConjugate_iff]
    refine ⟨?_, ?_⟩
    · rw [lt_div_iff₀ (by linarith : 0 < 1 - a)]
      linarith
    · have : 1 - a ≠ 0 := by linarith
      field_simp
      ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp hg.aemeasurable hf.aemeasurable
  have hg2 : (∫⁻ x, g x ^ (1 / (1 - a)) ∂μ) = μ s := by
    have heq : (fun x => g x ^ (1 / (1 - a))) = s.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ s <;> simp [g, hx, ha1]
    rw [heq, lintegral_indicator hs]
    simp
  rw [hg2] at h
  have hden : 1 - a ≠ 0 := by linarith
  have hpow : 1 / (1 / (1 - a)) = 1 - a := by field_simp
  have hpow' : 1 / (1 / a) = a := by field_simp
  rw [hpow, hpow'] at h
  convert h using 1
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s <;> simp [g, hx]

/-- A singularly weighted unit-time pair occupation bound for every exponent below two. -/
theorem planarBrownianMotion_ae_unit_singular_weighted_pair_subcritical_le (x z : ℂ) {q β : ℝ}
    (hq0 : 0 < q) (hq2 : q < 2) (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then
          (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) *
            (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) else 0) ∂(ν.prod ν)) ≤
          ENNReal.ofReal (C * r ^ (β * (2 - q) / (2 + q))) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let a : ℝ := 2*q/(q+2)
  have hqa : 0 < q+2 := by linarith
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by dsimp [a]; rw [div_lt_one hqa]; linarith
  have haexp : q * (1/a) = (q+2)/2 := by dsimp [a]; field_simp
  have hconst : 1-a = (2-q)/(2+q) := by dsimp [a]; field_simp; ring
  filter_upwards [planarBrownianMotion_ae_unit_pair_occupation_le x hβ0 hβ2,
    planarBrownianMotion_ae_unit_singular_occupation_lt_top x z
      (show 0 < (q+2)/2 by linarith) (show (q+2)/2 < 2 by linarith)] with b hb he
  obtain ⟨C, hC, hb⟩ := hb
  let w : ℝ≥0 → ℝ≥0∞ := fun t => (ENNReal.ofReal ‖b t - z‖) ^ (-q)
  let E := ∫⁻ t, (ENNReal.ofReal ‖b t - z‖) ^ (-((q+2)/2)) ∂ν
  have hE : E < ∞ := he
  have hw : Measurable w := by fun_prop
  refine ⟨C ^ (1-a) * (E.toReal + 1) ^ (2*a), by positivity, ?_⟩
  intro r hr
  let s : Set (ℝ≥0 × ℝ≥0) := {p | ‖b p.1 - b p.2‖ < r}
  have hs : MeasurableSet s := by
    have hc : Continuous (fun p : ℝ≥0 × ℝ≥0 => ‖b p.1 - b p.2‖) := by fun_prop
    exact (isOpen_lt hc continuous_const).measurableSet
  have hf : Measurable (fun p : ℝ≥0 × ℝ≥0 => w p.1 * w p.2) := by fun_prop
  have hp := lintegral_indicator_holder (ν.prod ν) s hs _ hf ha0 ha1
  have hsbound : (ν.prod ν) s ≤ ENNReal.ofReal (C * r ^ β) := by
    have h := hb r hr
    have hid : (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)) = (ν.prod ν) s := by
      rw [← lintegral_indicator_one hs]
      apply lintegral_congr
      intro p
      by_cases hp : ‖b p.1 - b p.2‖ < r <;> simp [s, hp]
    exact hid ▸ h
  have hsq : (∫⁻ p : ℝ≥0 × ℝ≥0, (w p.1 * w p.2) ^ (1/a) ∂(ν.prod ν)) = E * E := by
    have hweq : ∀ t, w t ^ (1/a) = (ENNReal.ofReal ‖b t - z‖) ^ (-((q+2)/2)) := by
      intro t
      rw [show w t = (ENNReal.ofReal ‖b t - z‖) ^ (-q) by rfl, ← ENNReal.rpow_mul]
      congr 1
      linarith [haexp]
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1/a), hweq]
    exact lintegral_prod_mul
      (f := fun t => (ENNReal.ofReal ‖b t - z‖) ^ (-((q+2)/2)))
      (g := fun t => (ENNReal.ofReal ‖b t - z‖) ^ (-((q+2)/2)))
      (by fun_prop) (by fun_prop)
  rw [hsq] at hp
  have hEbound : E ≤ ENNReal.ofReal (E.toReal + 1) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hE.ne]
    simp
  have hbound : (ν.prod ν) s ^ (1-a) * (E*E)^a ≤
      (ENNReal.ofReal (C * r ^ β)) ^ (1-a) *
        (ENNReal.ofReal (E.toReal + 1) * ENNReal.ofReal (E.toReal + 1))^a := by
    gcongr
  have hreal : (ENNReal.ofReal (C * r ^ β)) ^ (1-a) *
        (ENNReal.ofReal (E.toReal + 1) * ENNReal.ofReal (E.toReal + 1))^a =
      ENNReal.ofReal ((C ^ (1-a) * (E.toReal + 1) ^ (2*a)) *
        r ^ (β * (2-q)/(2+q))) := by
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (le_of_lt ha0),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity)]
    have hpow : a + a = 2*a := by ring
    have hβpow : β * (1-a) = β * (2-q)/(2+q) := by rw [hconst]; ring
    rw [hpow, hβpow]
    ring
  calc
    _ = ∫⁻ p, s.indicator (fun p => w p.1 * w p.2) p ∂(ν.prod ν) := by
      apply lintegral_congr
      intro p
      by_cases hp : ‖b p.1 - b p.2‖ < r <;> simp [s, hp, w]
    _ ≤ (ν.prod ν) s ^ (1-a) * (E*E)^a := hp
    _ ≤ _ := hbound
    _ = _ := hreal

end HarmonicBalls
