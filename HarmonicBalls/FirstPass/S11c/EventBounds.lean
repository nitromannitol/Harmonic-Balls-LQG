import HarmonicBalls.FirstPass.S11c.ProbAssembly

/-!
# Proposition 11.10, the numerical bounds of the probability step (fp-S11c, owner n1)

FIRST-PASS NEW (bookkeeping). In the probability step of the printed proof of `lemma:mass-diam` (paper lines 3091-3112) the
piece event and the exterior event have complements of measure at most `δ`, where `δ = p₀ / 16` and `p₀ = P(8c < μ(S₁))` is
independent of the level `N`. The quantitative class choice gives `p₀ ≤ 4 P(X_i)`. Two elementary consequences are used:
the inequality `2 δ < P(X_i)` (so the four-fold intersection has positive probability), and the conversion of the exterior
bound `1 - δ < P(B)` to the form `ofReal (1 - δ) ≤ P(B)` used by `prob_compl_le_ofReal_of_le`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls

/-- If `p₀ ≤ 4 X` with `0 < p₀ < ∞`, then `2 · ofReal (p₀ / 16) < X`. -/
lemma two_mul_ofReal_lt_of_quarter {p₀ X : ℝ≥0∞} (hp₀ : 0 < p₀) (hp₀t : p₀ ≠ ⊤) (hX : p₀ ≤ 4 * X) :
    2 * ENNReal.ofReal (p₀.toReal / 16) < X := by
  have hx : 0 < p₀.toReal := ENNReal.toReal_pos hp₀.ne' hp₀t
  have e1 : (4 : ℝ≥0∞) * (2 * ENNReal.ofReal (p₀.toReal / 16)) = ENNReal.ofReal (p₀.toReal / 2) := by
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  have hlt : ENNReal.ofReal (p₀.toReal / 2) < p₀ := by
    conv_rhs => rw [← ENNReal.ofReal_toReal hp₀t]
    exact (ENNReal.ofReal_lt_ofReal_iff hx).2 (by linarith)
  have h4 : (4 : ℝ≥0∞) * (2 * ENNReal.ofReal (p₀.toReal / 16)) < 4 * X := by
    rw [e1]
    exact lt_of_lt_of_le hlt hX
  by_contra hc
  have hc' : X ≤ 2 * ENNReal.ofReal (p₀.toReal / 16) := not_lt.1 hc
  have h5 : 4 * X ≤ 4 * (2 * ENNReal.ofReal (p₀.toReal / 16)) := by gcongr
  exact lt_irrefl _ (lt_of_lt_of_le h4 h5)

/-- A bound `1 - ofReal δ < P(B)` gives `ofReal (1 - δ) ≤ P(B)`, for `0 ≤ δ`. -/
lemma ofReal_one_sub_le_of_one_sub_lt {δ : ℝ} {x : ℝ≥0∞} (hδ : 0 ≤ δ) (h : 1 - ENNReal.ofReal δ < x) :
    ENNReal.ofReal (1 - δ) ≤ x := by
  have e : ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
    rw [ENNReal.ofReal_sub 1 hδ, ENNReal.ofReal_one]
  rw [e]
  exact h.le

end HarmonicBalls
