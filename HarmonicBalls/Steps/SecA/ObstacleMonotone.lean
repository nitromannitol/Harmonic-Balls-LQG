import HarmonicBalls.Steps.SecA.Basic

/-!
# Lemma A.3 (lemma:appendix-monotonicity, line 3731): carving of the proof

`ObstacleMonotoneStmt` (Draft/SectionA.lean): `t₁ ≤ t₂` implies `Λ_{t₁} ⊆ Λ_{t₂}`. The printed proof
(lines 3734-3765) shows `v_{t₁} ≤ v_{t₂}` by checking that `s̃ := ṽ_{t₂} + (t₂ - t₁) G_{B_1}(0,·)` lies in `S̃(t₁)`
(line 3763). Stated for a general radius `R > 0` and pole `z ∈ B_R`: `ObstacleMonotoneGeneral`.

**Minor gap (GRAPH.md, A.3).** For `t₁ < t₂`, `s̃` has a `+∞` pole at `z`, so it is not continuous on the closed
ball and not in `S̃(t₁) ⊆ C(closedBall)`, contrary to line 3763. Repair (Step 1): the truncation `min (s̃, M)`, with
`M ≥ max q_{B_R}` and value `M` at the pole, is continuous (`s̃ → +∞` at `z`), superharmonic, and `≥ β_{t₁}`
(`β_{t₁} ≤ q_{B_R} ≤ M` and `β_{t₁} = β_{t₂} + (t₂ - t₁) G ≤ s̃`), so it lies in `S̃(t₁)` and is `≤ s̃` off the pole.

## Steps (difficulty in brackets)

* `ObstacleMonotoneStep1` — the truncated competitor: for `t₁ < t₂` some `w ∈ S̃(t₁)` satisfies
  `w ≤ ṽ_{t₂} + (t₂ - t₁) G_{B_R}(z,·)` on the closed ball off the pole. [medium, 1-2 rounds]

## The reduction (proved)

`obstacleMonotoneGeneral_of_steps`: minimality of `ṽ_{t₁}` gives `v_{t₁} ≤ v_{t₂}` off the pole (the case
`t₁ = t₂` is trivial), hence `Λ_{t₁} ⊆ Λ_{t₂}` (the pole lies in both by definition).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Lemma A.3 for a general radius `R > 0` and pole `z ∈ B_R` (the paper's case is `R = 1`, `z = 0`), with the
monotonicity of the odometer in `t` (line 3736) as a first conjunct. -/
def ObstacleMonotoneGeneral : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ t₂ →
    (∀ x ∈ closedBall (0 : ℂ) R, x ≠ z → shiftedOdometer μ R z t₁ x ≤ shiftedOdometer μ R z t₂ x) ∧
    nonCoincidenceSet μ R z t₁ ⊆ nonCoincidenceSet μ R z t₂

/-- **Lemma A.3, Step 1 (the competitor of lines 3743-3763, truncated at the pole).** For `0 < t₁ < t₂` there is
`w ∈ S̃(t₁)` with `w ≤ ṽ_{t₂} + (t₂ - t₁) G_{B_R}(z,·)` on the closed ball off the pole. Printed competitor:
`s̃ = ṽ_{t₂} + (t₂ - t₁) G_{B_R}(z,·)`, which is not in `S̃(t₁)` (pole at `z`, see the module docstring). Repair:
`w = min (s̃, M)` off the pole and `w(z) = M`, for `M ≥ max_{closedBall} q_{B_R}`. Continuity: Lemma A.1
(`ṽ_{t₂}` continuous), Prop 2.3 (`G_{B_R}(z,·)` continuous off the pole, `→ +∞` at the pole,
`ObstacleTendstoAtBotStep`). Superharmonicity: `s̃` is superharmonic on `B_R \ {z}` (`G_{B_R}(z,·)` harmonic
there), the minimum of two superharmonic functions is superharmonic, `w` is constant near `z`, and
superharmonicity is local (AG01 §3.2); pass between the distributional and the classical notions with
`SuperharmonicOfLaplacianLEStep` and `LaplacianLEOfSuperharmonicStep`. Obstacle: `β_{t₁} ≤ q_{B_R} ≤ M` and
`β_{t₁} = β_{t₂} + (t₂ - t₁) G ≤ s̃`. Uses: Lemma A.1 (general form), Prop 2.3,
`GreenPotentialBallContinuousStep`. Difficulty: medium (1-2 rounds). -/
def ObstacleMonotoneStep1 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ < t₂ →
    ∃ w ∈ shiftedSupersolutions μ R z t₁, ∀ x ∈ closedBall (0 : ℂ) R, x ≠ z →
      w x ≤ shiftedLeastSupersolution μ R z t₂ x + (t₂ - t₁) * greenFunction (ball 0 R) z x

/-- **Lemma A.3, general radius and pole, from its step.** -/
theorem obstacleMonotoneGeneral_of_steps (h1 : ObstacleMonotoneStep1) : ObstacleMonotoneGeneral := by
  intro μ hμ R βm βp hR hV z hz t₁ t₂ ht₁ ht₁₂
  have hodo : ∀ x ∈ closedBall (0 : ℂ) R, x ≠ z →
      shiftedOdometer μ R z t₁ x ≤ shiftedOdometer μ R z t₂ x := by
    intro x hx hxz
    rcases ht₁₂.lt_or_eq with hlt | heq
    · obtain ⟨w, hw, hwle⟩ := h1 μ hμ R βm βp hR hV z hz t₁ t₂ ht₁ hlt
      have := (shiftedLeastSupersolution_le hw hx hxz).trans (hwle x hx hxz)
      simp only [shiftedOdometer, obstacle]
      linarith
    · subst heq
      exact le_rfl
  refine ⟨hodo, fun x hx => ⟨hx.1, ?_⟩⟩
  by_cases hxz : x = z
  · exact Or.inl hxz
  · right
    have h₁ : obstacle μ R z t₁ x < shiftedLeastSupersolution μ R z t₁ x := hx.2.resolve_left hxz
    have h₂ := hodo x (ball_subset_closedBall hx.1) hxz
    simp only [shiftedOdometer] at h₂
    linarith

/-- The general form of Lemma A.3 gives the printed statement (`R = 1`, `z = 0`). -/
theorem obstacleMonotone_of_general (h : ObstacleMonotoneGeneral) : ObstacleMonotoneStmt :=
  fun μ hμ βm βp hV t₁ t₂ ht₁ ht₁₂ => (h μ hμ 1 βm βp one_pos hV 0 (mem_ball_self one_pos) t₁ t₂ ht₁ ht₁₂).2

/-- **Lemma A.3 from its step.** -/
theorem obstacleMonotone_of_steps (h1 : ObstacleMonotoneStep1) : ObstacleMonotoneStmt :=
  obstacleMonotone_of_general (obstacleMonotoneGeneral_of_steps h1)

end HarmonicBalls
