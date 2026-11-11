import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG

/-!
# Lemma 11.7, translation of the rooted field (deterministic)

Circle averages commute with translations of the centre and of the function: for a function `g : ℂ → ℝ`,
`Real.circleAverage (fun u => g (u - z)) x r = Real.circleAverage g (x - z) r` (the circle `∂B_r(x)` is mapped to
`∂B_r(x - z)` by `u ↦ u - z`). This is the algebraic identity behind the translation of the rooted circle average
`h_r(w) - γ · average of log|· - z| over ∂B_r(w)` to the origin-rooted circle average of the translated field.
-/

open MeasureTheory Metric Complex

namespace HarmonicBalls.S11c

/-- Translation of the circle average: `average over ∂B_r(x) of g(· - z) = average over ∂B_r(x - z) of g`. -/
lemma circleAverage_sub_const (g : ℂ → ℝ) (x z : ℂ) (r : ℝ) :
    Real.circleAverage (fun u => g (u - z)) x r = Real.circleAverage g (x - z) r := by
  unfold Real.circleAverage
  congr 2
  funext θ
  simp only [circleMap]
  ring

/-- Constant shift of the regularized approximations: `ε^{γ²/2} e^{γ (h_ε - c)} dz = e^{-γc} · ε^{γ²/2} e^{γ h_ε} dz`
(Defs/LQG.lean:44, `lqgApprox`). -/
lemma lqgApprox_sub_const (γ : ℝ) (hε : ℝ → ℂ → ℝ) (c ε : ℝ) :
    lqgApprox γ (fun e w => hε e w - c) ε = ENNReal.ofReal (Real.exp (-(γ * c))) • lqgApprox γ hε ε := by
  unfold lqgApprox
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [show γ * (hε ε z - c) = γ * hε ε z + -(γ * c) by ring, Real.exp_add]
  ring

/-- The constant shift of an LQG limit: if `h_ε` converges vaguely to `m` (Defs/LQG.lean:53, `IsLQGLimit`), then
`h_ε - c` converges vaguely to `e^{-γc} m` (the approximations change by the factor `e^{-γc}`). Deterministic. -/
theorem isLQGLimit_sub_const {γ : ℝ} {hε : ℝ → ℂ → ℝ} {m : Measure ℂ} (h : IsLQGLimit γ hε m) (c : ℝ) :
    IsLQGLimit γ (fun ε w => hε ε w - c) (ENNReal.ofReal (Real.exp (-(γ * c))) • m) := by
  refine ⟨?_, ?_⟩
  · have hloc := h.isLocallyFiniteMeasure
    refine ⟨fun x => ?_⟩
    obtain ⟨o, xo, o_open, μo⟩ := m.exists_isOpen_measure_lt_top x
    refine ⟨o, o_open.mem_nhds xo, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top μo
  intro f hf hc
  have hr : (ENNReal.ofReal (Real.exp (-(γ * c)))).toReal = Real.exp (-(γ * c)) :=
    ENNReal.toReal_ofReal (Real.exp_pos _).le
  simp only [lqgApprox_sub_const, integral_smul_measure, hr, smul_eq_mul]
  exact (h.tendsto_integral f hf hc).const_mul _

end HarmonicBalls.S11c
