import Mathlib

/-! # Subcritical exponents for Liouville clock estimates

The truncated second moment estimate in Berestycki, *Diffusion in planar Liouville quantum gravity*,
Section 2, admits strictly positive decay exponents throughout the subcritical range.
-/

namespace HarmonicBalls

/-- A truncation level and an occupation exponent can be chosen to make both the thin- and
thick-point decay exponents positive. -/
theorem exists_clock_truncation_exponents {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ α d : ℝ, γ < α ∧ α < 2 * γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ ^ 2 + (2 * γ - α) ^ 2 / 2 ∧ 0 < (α - γ) ^ 2 / 2 := by
  have hchoose : ∃ α : ℝ, γ < α ∧ α < 2 * γ ∧
      0 < 2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2 := by
    by_cases h : γ < 1
    · refine ⟨3 * γ / 2, by linarith, by linarith, ?_⟩
      have hm := mul_pos hγ0 (sub_pos.mpr h)
      nlinarith
    · refine ⟨(γ + 2) / 2, by linarith, by linarith, ?_⟩
      have hm := mul_pos (sub_pos.mpr hγ2) (show 0 < 10 - γ by linarith)
      nlinarith
  obtain ⟨α, hγα, hα, he⟩ := hchoose
  let e : ℝ := 2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2
  have he0 : 0 < e := he
  have he2 : e < 2 := by
    have hm := mul_pos (show 0 < α - γ by linarith) (show 0 < 3 * γ - α by linarith)
    dsimp [e]
    nlinarith
  refine ⟨α, 2 - e / 2, hγα, hα, by linarith, by linarith, ?_, ?_⟩
  · dsimp [e] at *
    linarith
  · positivity

end HarmonicBalls
