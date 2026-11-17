import HarmonicBalls.Proofs.Potential.BrownianSingularOccupation

/-! # Annealed singular pair occupation

A subcritical square moment controls the expected singular pair occupation.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The singularly weighted unit-time pair occupation has finite expectation when
its squared weight is subcritical. -/
theorem planarBrownianMotion_unit_singular_pair_occupation_lt_top (x z : ℂ) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
      (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) *
        (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) ∂(ν.prod ν)
          ∂(planarBrownianMotion x)) < ∞ := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  let f : ContinuousPath ℂ → ℝ≥0 → ℝ≥0∞ := fun b t =>
    (ENNReal.ofReal ‖b t - z‖) ^ (-(2*q))
  have hf (b : ContinuousPath ℂ) : Measurable (f b) := by dsimp [f]; fun_prop
  have hi : (∫⁻ b, ∫⁻ t, f b t ∂ν ∂(planarBrownianMotion x)) < ∞ := by
    exact planarBrownianMotion_unit_singular_occupation_lt_top x z (by linarith) (by linarith)
  have hb (b : ContinuousPath ℂ) :
      (∫⁻ p : ℝ≥0 × ℝ≥0,
        (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) *
          (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) ∂(ν.prod ν)) ≤
      2 * (∫⁻ t, f b t ∂ν) := by
    calc
      _ ≤ ∫⁻ p : ℝ≥0 × ℝ≥0, f b p.1 + f b p.2 ∂(ν.prod ν) := by
        apply lintegral_mono
        intro p
        let a := (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q)
        let c := (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q)
        have ha : a*a = f b p.1 := by
          dsimp [a, f]
          rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          congr 1; ring
        have hc : c*c = f b p.2 := by
          dsimp [c, f]
          rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          congr 1; ring
        change a*c ≤ f b p.1 + f b p.2
        rcases le_total a c with h | h
        · calc
            a*c ≤ c*c := by gcongr
            _ = f b p.2 := hc
            _ ≤ f b p.1 + f b p.2 := le_add_self
        · calc
            a*c ≤ a*a := by gcongr
            _ = f b p.1 := ha
            _ ≤ f b p.1 + f b p.2 := le_self_add
      _ = 2 * (∫⁻ t, f b t ∂ν) := by
        change (∫⁻ p, (f b ∘ Prod.fst) p + (f b ∘ Prod.snd) p ∂(ν.prod ν)) = _
        rw [lintegral_add_left (hf b |>.comp measurable_fst)]
        rw [lintegral_prod _ (hf b |>.comp measurable_fst).aemeasurable,
          lintegral_prod _ (hf b |>.comp measurable_snd).aemeasurable]
        simp [hν, two_mul]
  calc
    _ ≤ ∫⁻ b, 2 * (∫⁻ t, f b t ∂ν) ∂(planarBrownianMotion x) := lintegral_mono hb
    _ = 2 * (∫⁻ b, ∫⁻ t, f b t ∂ν ∂(planarBrownianMotion x)) := by
      rw [lintegral_const_mul' _ _ (by norm_num)]
    _ < ∞ := ENNReal.mul_lt_top (by norm_num) hi

end HarmonicBalls
