import HarmonicBalls.Draft.Section11

/-!
# Threshold inequalities for the second pinch event

Deterministic part of Lemma 11.16 (`lemma:second-event-proof`, paper lines 3697-3725). If the internal diameter of `V`
is at most `c₁/2`, the crossing distance `D(∂B_δ, ∂B_{2δ})` is at least `c₁`, the annulus Green potential times `M` is at
most `c₂`, and `μ(U) > 2c₂`, then the second pinch event `Ẽ₂(M)` holds (`pinchSecondEvent`, `Draft/Section11.lean:102`).
No probability and no measurability is used here.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Threshold form of the second event `Ẽ₂(M)` (`pinchSecondEvent`): the strict inequalities of `Ẽ₂(M)` follow from the
non-strict diameter bound `diam^δ(V) ≤ c₁/2`, the separation `c₁ ≤ D(∂B_δ, ∂B_{2δ})`, the bound `M S ≤ c₂` and the mass
bound `μ(U) > 2c₂`, because `c₁/2 < c₁` and `c₂ < 2c₂` with `c₁, c₂ > 0`. -/
theorem pinchSecondEvent_of_thresholds {μ : Measure ℂ} {D : ℂ → ℂ → ℝ} {U V : Set ℂ} {δ M c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hdiam : internalDiam D δ V ≤ ENNReal.ofReal (c₁ / 2))
    (hsep : c₁ ≤ setDist D (sphere 0 δ) (sphere 0 (2 * δ)))
    (hS : ENNReal.ofReal M * annulusGreenPotentialSup μ 0 3 6 ≤ ENNReal.ofReal c₂)
    (hmass : ENNReal.ofReal (2 * c₂) < μ U) :
    pinchSecondEvent μ D U V δ M := by
  unfold pinchSecondEvent
  refine ⟨?_, ?_⟩
  · have h1 : ENNReal.ofReal (c₁ / 2) < ENNReal.ofReal c₁ :=
      (ENNReal.ofReal_lt_ofReal_iff hc₁).2 (by linarith)
    exact lt_of_le_of_lt hdiam (h1.trans_le (ENNReal.ofReal_le_ofReal hsep))
  · have h2 : ENNReal.ofReal c₂ < ENNReal.ofReal (2 * c₂) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    exact lt_of_le_of_lt hS (h2.trans hmass)

end HarmonicBalls
