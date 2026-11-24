import HarmonicBalls.Proofs.Potential.LQGApproxNearInsertionPower
import HarmonicBalls.Proofs.Potential.LQGApproxAwayInsertion

/-!
# Conditional compact-center bounds for singular approximations

An ordinary compact-center power bound combines with the insertion bound to
control singular approximation masses at every center.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- A common ordinary power bound and the insertion estimate give a bound for
all centers. The displayed logarithmic factor accounts for centers approaching
the insertion and remains uniform over dyadic smoothing scales. -/
theorem ae_singular_approximant_all_center_bound_of_ordinary_power
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hr : 0 < r) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ)
    (R : ℝ) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∃ C β r₀ : ℝ, 0 < C ∧ 0 < β ∧ 0 < r₀ ∧
        ∀ C₁ κ : ℝ, (∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ,
          0 ≤ s → s ≤ 1 → lqgApprox γ (hcirc ω) (dyadicScale k) (ball z s) ≤
            ENNReal.ofReal (C₁ * s ^ κ)) →
        ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 < s → s ≤ r₀ → s ≤ 1 →
          s ≤ s ^ a / 2 →
          lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
            max (ENNReal.ofReal (C * s ^ β))
              (ENNReal.ofReal (Real.exp (γ * (|α| *
                (|Real.log (s ^ a / 2)| + |Real.log (max 1 (R + 1))|)))) *
                  ENNReal.ofReal (C₁ * s ^ κ)) := by
  filter_upwards [ae_singular_approximant_near_origin_rpow_ball_power
    hh hγ hγ2 hαQ hδ hr hρ hrρ] with ω hω
  intro a ha ha1
  obtain ⟨C, β, r₀, hC, hβ, hr₀, hnear⟩ := hω a ha ha1
  refine ⟨C, β, r₀, hC, hβ, hr₀, ?_⟩
  intro C₁ κ hord k z hz s hs hsr hs1 hssep
  by_cases h : ‖z‖ ≤ s ^ a
  · exact (hnear k z s hs hsr h).trans (le_max_left _ _)
  · have hd : 0 < s ^ a / 2 := by positivity
    have heps : 0 < dyadicScale k := by unfold dyadicScale; positivity
    have heps1 : dyadicScale k ≤ 1 := by
      unfold dyadicScale
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hb : ∀ ε ∈ Set.range dyadicScale, 0 < ε → ε ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ R →
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          lqgApprox γ (hcirc ω) ε (ball z t) ≤ ENNReal.ofReal (C₁ * t ^ κ) := by
      intro ε he _ _ w hw t ht ht1
      obtain ⟨j, hj⟩ := he
      subst ε
      exact hord j w hw t ht ht1
    have hfar := singular_approximant_ball_le_of_ordinary (α := α) (d := s ^ a / 2)
      hγ.le hd (hcirc ω) (Set.range dyadicScale) hb (dyadicScale k) ⟨k, rfl⟩
      heps heps1 z (by linarith [lt_of_not_ge h]) hz s hs.le hs1 hssep
    exact hfar.trans (le_max_right _ _)

end HarmonicBalls
