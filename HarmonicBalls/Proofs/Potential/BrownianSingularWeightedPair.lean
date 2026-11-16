import HarmonicBalls.Proofs.Potential.BrownianSingularOccupation
import HarmonicBalls.Proofs.Potential.BrownianOccupationNearDiagonal
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Singularly weighted Brownian pair occupation

Finite inverse-power occupation and near-diagonal pair bounds control the weighted pair integral.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

private theorem lintegral_indicator_le_holder {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s) (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x, s.indicator f x ∂μ) ≤
      (μ s) ^ (1 / 2 : ℝ) * (∫⁻ x, (f x) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  classical
  let g : α → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hs
  have hp : (2 : ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp hg.aemeasurable hf.aemeasurable
  have hg2 : (∫⁻ x, g x ^ (2 : ℝ) ∂μ) = μ s := by
    have heq : (fun x => g x ^ (2 : ℝ)) = s.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ s <;> simp [g, hx]
    rw [heq, lintegral_indicator hs]
    simp
  rw [hg2] at h
  convert h using 1
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s <;> simp [g, hx]

/-- Finite singular occupation and a near-diagonal pair bound control the singularly
weighted pair integral. -/
theorem planarBrownianMotion_ae_unit_singular_weighted_pair_le (x z : ℂ) {q β : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then
          (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) *
            (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) else 0) ∂(ν.prod ν)) ≤
          ENNReal.ofReal (C * r ^ (β / 2)) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [planarBrownianMotion_ae_unit_pair_occupation_le x hβ0 hβ2,
    planarBrownianMotion_ae_unit_singular_occupation_lt_top x z (show 0 < 2*q by linarith)
      (show 2*q < 2 by linarith)] with b hb he
  obtain ⟨C, hC, hb⟩ := hb
  let w : ℝ≥0 → ℝ≥0∞ := fun t => (ENNReal.ofReal ‖b t - z‖) ^ (-q)
  let E := ∫⁻ t, (ENNReal.ofReal ‖b t - z‖) ^ (-(2*q)) ∂ν
  have hE : E < ∞ := he
  have hw : Measurable w := by fun_prop
  refine ⟨Real.sqrt C * (E.toReal + 1), by positivity, ?_⟩
  intro r hr
  let s : Set (ℝ≥0 × ℝ≥0) := {p | ‖b p.1 - b p.2‖ < r}
  have hs : MeasurableSet s := by
    have hc : Continuous (fun p : ℝ≥0 × ℝ≥0 => ‖b p.1 - b p.2‖) := by fun_prop
    exact (isOpen_lt hc continuous_const).measurableSet
  have hf : Measurable (fun p : ℝ≥0 × ℝ≥0 => w p.1 * w p.2) := by fun_prop
  have hp := lintegral_indicator_le_holder (ν.prod ν) s hs _ hf
  have hsbound : (ν.prod ν) s ≤ ENNReal.ofReal (C * r ^ β) := by
    have h := hb r hr
    have hid : (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)) = (ν.prod ν) s := by
      rw [← lintegral_indicator_one hs]
      apply lintegral_congr
      intro p
      by_cases hp : ‖b p.1 - b p.2‖ < r <;> simp [s, hp]
    exact hid ▸ h
  have hsq : (∫⁻ p : ℝ≥0 × ℝ≥0, (w p.1 * w p.2) ^ (2 : ℝ) ∂(ν.prod ν)) = E * E := by
    have hweq : ∀ t, w t ^ (2 : ℝ) = (ENNReal.ofReal ‖b t - z‖) ^ (-(2*q)) := by
      intro t
      rw [show w t = (ENNReal.ofReal ‖b t - z‖) ^ (-q) by rfl, ← ENNReal.rpow_mul]
      congr 1
      ring
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), hweq]
    exact lintegral_prod_mul
      (f := fun t => (ENNReal.ofReal ‖b t - z‖) ^ (-(2*q)))
      (g := fun t => (ENNReal.ofReal ‖b t - z‖) ^ (-(2*q)))
      (by fun_prop) (by fun_prop)
  rw [hsq] at hp
  have h1 : (ν.prod ν) s ^ (1 / 2 : ℝ) ≤
      (ENNReal.ofReal (C * r ^ β)) ^ (1 / 2 : ℝ) := by gcongr
  have h2 : (E * E) ^ (1 / 2 : ℝ) = E := by
    calc
      (E * E) ^ (1 / 2 : ℝ) = (E ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by rw [ENNReal.rpow_two, pow_two]
      _ = E ^ ((2 : ℝ) * (1 / 2)) := (ENNReal.rpow_mul _ _ _).symm
      _ = E := by norm_num
  rw [h2] at hp
  have h3 : E ≤ ENNReal.ofReal (E.toReal + 1) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hE.ne]
    simp
  have h4 : (ENNReal.ofReal (C * r ^ β)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt C * r ^ (β / 2)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    rw [Real.mul_rpow (by positivity) (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    congr 2
    ring_nf
  calc
    _ = ∫⁻ p, s.indicator (fun p => w p.1 * w p.2) p ∂(ν.prod ν) := by
      apply lintegral_congr
      intro p
      by_cases hp : ‖b p.1 - b p.2‖ < r <;> simp [s, hp, w]
    _ ≤ (ν.prod ν) s ^ (1 / 2 : ℝ) * E := hp
    _ ≤ ENNReal.ofReal (Real.sqrt C * r ^ (β / 2)) * ENNReal.ofReal (E.toReal + 1) := by
      rw [← h4]
      exact mul_le_mul' h1 h3
    _ = ENNReal.ofReal (Real.sqrt C * (E.toReal + 1) * r ^ (β / 2)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end HarmonicBalls
