import HarmonicBalls.Proofs.Sec6.GreenMono

/-! # Green-potential bounds over a compact family of annuli -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- Enlarging an annulus at both its boundaries increases its Green-potential
supremum. -/
theorem annulusGreenPotentialSup_mono (μ : Measure ℂ) (x₀ : ℂ)
    {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    annulusGreenPotentialSup μ x₀ a b ≤ annulusGreenPotentialSup μ x₀ a' b' := by
  have hsub : annulus x₀ a b ⊆ annulus x₀ a' b' := by
    intro x hx
    exact ⟨ball_subset_ball hb hx.1, fun hx' => hx.2 (closedBall_subset_closedBall ha hx')⟩
  have hmeas : MeasurableSet (annulus x₀ a b) :=
    isOpen_ball.measurableSet.diff measurableSet_closedBall
  unfold annulusGreenPotentialSup
  refine iSup₂_le fun x hx => le_iSup₂_of_le x (hsub hx) ?_
  calc
    (∫⁻ y in annulus x₀ a b,
        (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ b) x y)) ∂μ) ≤
      ∫⁻ y in annulus x₀ a b,
        (if y = x then ∞ else ENNReal.ofReal (greenFunction (ball x₀ b') x y)) ∂μ := by
          refine setLIntegral_mono' hmeas fun y hy => ?_
          by_cases hyx : y = x
          · simp only [hyx, ↓reduceIte, le_refl]
          · simp only [hyx, ↓reduceIte]
            exact ENNReal.ofReal_le_ofReal
              (greenFunction_mono (ball_subset_ball hb) isBounded_ball hx.1 hy.1 (Ne.symm hyx))
    _ ≤ _ := lintegral_mono_set hsub

/-- Every size-annulus Green supremum with radius in `[1/2,1]` lies between
those of two fixed annuli. -/
theorem annulusGreenPotentialSup_bounds_on_dyadic_phases (μ : Measure ℂ)
    {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    annulusGreenPotentialSup μ 0 (1 / 4) 1 ≤
        annulusGreenPotentialSup μ 0 (s / 4) (2 * s) ∧
      annulusGreenPotentialSup μ 0 (s / 4) (2 * s) ≤
        annulusGreenPotentialSup μ 0 (1 / 8) 2 := by
  constructor
  · apply annulusGreenPotentialSup_mono <;> linarith [hs.1, hs.2]
  · apply annulusGreenPotentialSup_mono <;> linarith [hs.1, hs.2]


/-- Two fixed annular masses and Green suprema bound the size ratio uniformly
across all phases in `[1/2,1]`. -/
theorem annulusGreenPotentialRatio_bounds_on_dyadic_phases (μ : Measure ℂ)
    {s : ℝ} (hs : s ∈ Icc (1 / 2 : ℝ) 1) :
    annulusGreenPotentialSup μ 0 (1 / 4) 1 / μ (annulus 0 (1 / 8) 2) ≤
        annulusGreenPotentialSup μ 0 (s / 4) (2 * s) / μ (annulus 0 (s / 4) (2 * s)) ∧
      annulusGreenPotentialSup μ 0 (s / 4) (2 * s) / μ (annulus 0 (s / 4) (2 * s)) ≤
        annulusGreenPotentialSup μ 0 (1 / 8) 2 / μ (annulus 0 (1 / 4) 1) := by
  have hsmall : annulus (0 : ℂ) (1 / 4) 1 ⊆ annulus 0 (s / 4) (2 * s) := by
    intro x hx
    exact ⟨ball_subset_ball (by linarith [hs.1]) hx.1,
      fun h => hx.2 (closedBall_subset_closedBall (by linarith [hs.2]) h)⟩
  have hlarge : annulus (0 : ℂ) (s / 4) (2 * s) ⊆ annulus 0 (1 / 8) 2 := by
    intro x hx
    exact ⟨ball_subset_ball (by linarith [hs.2]) hx.1,
      fun h => hx.2 (closedBall_subset_closedBall (by linarith [hs.1]) h)⟩
  obtain ⟨hlo, hhi⟩ := annulusGreenPotentialSup_bounds_on_dyadic_phases μ hs
  exact ⟨ENNReal.div_le_div hlo (measure_mono hlarge),
    ENNReal.div_le_div hhi (measure_mono hsmall)⟩

end HarmonicBalls.Section6
