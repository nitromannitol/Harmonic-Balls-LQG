import HarmonicBalls.Defs.LBM

/-! # Uniqueness of the Liouville clock

The uniform convergence in probability specifying the clock determines it
simultaneously at all times, almost surely under the path law.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- Two clocks for the same approximations agree at every time almost surely. -/
theorem IsLQGClock.ae_eq {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ hε x F)
    (hG : IsLQGClock planarBrownianMotion γ hε x G) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ t, F b t = G b t := by
  classical
  let μ := planarBrownianMotion x
  have hzero (T : ℝ≥0) (ε : ℝ) (hεpos : 0 < ε) :
      μ {b | ∃ t ≤ T, ε ≤ |F b t - G b t|} = 0 := by
    let A : ℕ → Set (ContinuousPath ℂ) := fun k =>
      {b | ∃ t ≤ T, ε / 2 ≤ |lqgClockApprox γ hε (dyadicScale k) b t - F b t|}
    let B : ℕ → Set (ContinuousPath ℂ) := fun k =>
      {b | ∃ t ≤ T, ε / 2 ≤ |lqgClockApprox γ hε (dyadicScale k) b t - G b t|}
    have hbound (k : ℕ) : μ {b | ∃ t ≤ T, ε ≤ |F b t - G b t|} ≤ μ (A k) + μ (B k) := by
      calc
        _ ≤ μ (A k ∪ B k) := measure_mono (by
          intro b ⟨t, ht, he⟩
          by_contra hn
          have ha : |lqgClockApprox γ hε (dyadicScale k) b t - F b t| < ε / 2 := by
            by_contra h; exact hn (Or.inl ⟨t, ht, le_of_not_gt h⟩)
          have hb : |lqgClockApprox γ hε (dyadicScale k) b t - G b t| < ε / 2 := by
            by_contra h; exact hn (Or.inr ⟨t, ht, le_of_not_gt h⟩)
          have hab := abs_sub_le (F b t) (lqgClockApprox γ hε (dyadicScale k) b t) (G b t)
          have ha' : |F b t - lqgClockApprox γ hε (dyadicScale k) b t| < ε / 2 := by
            rwa [abs_sub_comm]
          linarith)
        _ ≤ μ (A k) + μ (B k) := measure_union_le _ _
    have ht : Tendsto (fun k => μ (A k) + μ (B k)) atTop (𝓝 0) := by
      simpa only [zero_add] using (hF T (ε / 2) (by positivity)).add (hG T (ε / 2) (by positivity))
    exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds ht (Filter.Eventually.of_forall hbound)) bot_le
  have hae (n m : ℕ) : ∀ᵐ b ∂μ, ¬ ∃ t ≤ (n : ℝ≥0),
      (1 / (m + 1 : ℝ)) ≤ |F b t - G b t| := by
    rw [ae_iff]
    simpa only [not_not] using hzero (n : ℝ≥0) (1 / (m + 1 : ℝ)) (by positivity)
  have hall : ∀ᵐ b ∂μ, ∀ n m : ℕ, ¬ ∃ t ≤ (n : ℝ≥0),
      (1 / (m + 1 : ℝ)) ≤ |F b t - G b t| := by
    simp only [ae_all_iff]
    exact hae
  filter_upwards [hall] with b hb
  intro t
  by_contra hne
  have hpos : 0 < |F b t - G b t| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
  have htn : t ≤ (n : ℝ≥0) := by exact_mod_cast hn
  exact hb n m ⟨t, htn, le_of_lt hm⟩

end HarmonicBalls
