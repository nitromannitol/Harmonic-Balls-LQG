import HarmonicBalls.Proofs.Potential.BrownianSingularPairAnnealed
import HarmonicBalls.Proofs.Potential.BrownianPairOccupationBound
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! # Singular Brownian pair occupation

Hölder's inequality controls weighted near-diagonal occupation by a higher singular moment.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- A weighted near-diagonal occupation is bounded by a higher singular pair moment
and the unweighted near-diagonal occupation. -/
theorem planarBrownianMotion_unit_singular_pair_holder (x z : ℂ) {q q₂ : ℝ}
    (hq : 0 < q) (hqq : q < q₂) (r : ℝ) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
      (if ‖b p.1 - b p.2‖ < r then
        (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) *
          (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) else 0) ∂(ν.prod ν)
            ∂(planarBrownianMotion x)) ≤
    (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
      (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q₂) *
        (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q₂) ∂(ν.prod ν)
          ∂(planarBrownianMotion x)) ^ (q/q₂) *
    (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
      (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)
        ∂(planarBrownianMotion x)) ^ (1-q/q₂) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ := (planarBrownianMotion x).prod (ν.prod ν)
  let F : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) → ℝ≥0∞ := fun v =>
    (ENNReal.ofReal ‖v.1 v.2.1 - z‖) ^ (-q₂) *
      (ENNReal.ofReal ‖v.1 v.2.2 - z‖) ^ (-q₂)
  let E : Set (ContinuousPath ℂ × (ℝ≥0 × ℝ≥0)) :=
    {v | ‖v.1 v.2.1 - v.1 v.2.2‖ < r}
  have hE : MeasurableSet E := by
    apply isOpen_lt _ continuous_const |>.measurableSet
    fun_prop
  let G : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) → ℝ≥0∞ := E.indicator 1
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hG : Measurable G := measurable_const.indicator hE
  have ha : 0 < q/q₂ := div_pos hq (by linarith)
  have ha1 : q/q₂ < 1 := (div_lt_one (by linarith)).2 hqq
  have hq₂ : q₂ ≠ 0 := ne_of_gt (by linarith)
  have hrpow : -q₂ * (q/q₂) = -q := by field_simp
  have h := ENNReal.lintegral_mul_norm_pow_le (μ := μ) hF.aemeasurable hG.aemeasurable
    ha.le (sub_nonneg.mpr ha1.le) (show q/q₂ + (1-q/q₂) = 1 by ring)
  have hpoint (v : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0)) :
      F v ^ (q/q₂) * G v ^ (1-q/q₂) =
        if ‖v.1 v.2.1 - v.1 v.2.2‖ < r then
          (ENNReal.ofReal ‖v.1 v.2.1 - z‖) ^ (-q) *
            (ENNReal.ofReal ‖v.1 v.2.2 - z‖) ^ (-q) else 0 := by
    by_cases hv : v ∈ E
    · have hv' : ‖v.1 v.2.1 - v.1 v.2.2‖ < r := hv
      simp only [G, Set.indicator_of_mem hv, Pi.one_apply, ENNReal.one_rpow, mul_one, hv', ↓reduceIte]
      dsimp [F]
      rw [ENNReal.mul_rpow_of_nonneg _ _ ha.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hrpow]
    · have hv' : ¬ ‖v.1 v.2.1 - v.1 v.2.2‖ < r := hv
      simp [G, Set.indicator_of_notMem hv, hv', ENNReal.zero_rpow_of_pos (sub_pos.mpr ha1)]
  rw [show (∫⁻ v, F v ^ (q/q₂) * G v ^ (1-q/q₂) ∂μ) =
      ∫⁻ v, (if ‖v.1 v.2.1 - v.1 v.2.2‖ < r then
        (ENNReal.ofReal ‖v.1 v.2.1 - z‖) ^ (-q) *
          (ENNReal.ofReal ‖v.1 v.2.2 - z‖) ^ (-q) else 0) ∂μ by
        apply lintegral_congr; exact hpoint] at h
  have hm : Measurable (fun v : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) =>
      if ‖v.1 v.2.1 - v.1 v.2.2‖ < r then
        (ENNReal.ofReal ‖v.1 v.2.1 - z‖) ^ (-q) *
          (ENNReal.ofReal ‖v.1 v.2.2 - z‖) ^ (-q) else 0) := by
    convert (hF.pow_const (q/q₂)).mul (hG.pow_const (1-q/q₂)) using 1
    funext v; exact (hpoint v).symm
  rw [lintegral_prod _ hm.aemeasurable] at h
  rw [lintegral_prod _ hF.aemeasurable, lintegral_prod _ hG.aemeasurable] at h
  simpa [F, G, E, Set.indicator_apply, μ, ν] using h

/-- Expected singularly weighted pairs within distance `r` satisfy a power bound. -/
theorem planarBrownianMotion_unit_singular_pair_near_le (x z : ℂ) {q q₂ β : ℝ}
    (hq : 0 < q) (hqq : q < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ r : ℝ, 0 < r →
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then
          (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) *
            (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) else 0) ∂(ν.prod ν)
              ∂(planarBrownianMotion x)) ≤
        C * ENNReal.ofReal (r ^ (β * (1 - q/q₂))) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let K := ∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
    (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q₂) *
      (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q₂) ∂(ν.prod ν) ∂(planarBrownianMotion x)
  have hK : K < ∞ := planarBrownianMotion_unit_singular_pair_occupation_lt_top x z
    (by linarith) hq₂
  have ha : 0 < q/q₂ := div_pos hq (by linarith)
  have ha1 : q/q₂ < 1 := (div_lt_one (by linarith)).2 hqq
  have hp : 0 ≤ 1-q/q₂ := (sub_pos.mpr ha1).le
  obtain ⟨D, hD, hbound⟩ := planarBrownianMotion_unit_pair_occupation_le x hβ hβ₂
  refine ⟨K ^ (q/q₂) * (ENNReal.ofReal D) ^ (1-q/q₂), ?_, ?_⟩
  · exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ha.le hK.ne)
      (ENNReal.rpow_lt_top_of_nonneg hp ENNReal.ofReal_ne_top)
  · intro r hr
    calc
      _ ≤ K ^ (q/q₂) *
          (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
            (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)
              ∂(planarBrownianMotion x)) ^ (1-q/q₂) :=
        planarBrownianMotion_unit_singular_pair_holder x z hq hqq r
      _ ≤ K ^ (q/q₂) * (ENNReal.ofReal (D * r ^ β)) ^ (1-q/q₂) := by
        gcongr
        exact hbound r hr
      _ = (K ^ (q/q₂) * (ENNReal.ofReal D) ^ (1-q/q₂)) *
          ENNReal.ofReal (r ^ (β * (1-q/q₂))) := by
        rw [ENNReal.ofReal_mul hD.le, ENNReal.mul_rpow_of_nonneg _ _ hp,
          ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hr.le β) hp,
          ← Real.rpow_mul hr.le]
        ring

end HarmonicBalls
