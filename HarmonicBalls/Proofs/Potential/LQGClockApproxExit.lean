import HarmonicBalls.Defs.LBM
import HarmonicBalls.Proofs.Sec6.CompactHittingStopping

/-! # Clock approximation at Brownian exit

Locally uniform convergence in probability passes to the finite exit time of a
bounded open domain.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- The dyadic clock approximations converge in probability at Brownian exit. -/
theorem IsLQGClock.tendsto_measure_clockApprox_exitTime
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} {D : Set ℂ}
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hD : IsOpen D) (hbounded : Bornology.IsBounded D) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun k : ℕ => planarBrownianMotion x
      {b | η ≤ |lqgClockApprox γ hε (dyadicScale k) b
        (ContinuousPath.exitTime D b).toNNReal - F b (ContinuousPath.exitTime D b).toNNReal|})
      atTop (𝓝 0) := by
  let μ := planarBrownianMotion x
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime D
  let A : ℕ → Set (ContinuousPath ℂ) := fun n => {b | (n : ℝ≥0∞) < τ b}
  have hanti : Antitone A := by
    intro n m hnm b hb
    change (m : ℝ≥0∞) < τ b at hb
    change (n : ℝ≥0∞) < τ b
    exact lt_of_le_of_lt (by exact_mod_cast hnm) hb
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := A)
    (fun n => (measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime D hD)).nullMeasurableSet)
    hanti ⟨0, measure_ne_top μ _⟩
  have hzero : μ (⋂ n, A n) = 0 := by
    apply measure_mono_null (t := {b | ¬ τ b < ∞})
    · intro b hb hfin
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin.ne
      exact (not_lt_of_ge hn.le) (Set.mem_iInter.mp hb n)
    · exact ae_iff.1 (Section6.ae_planarBrownian_exitTime_bounded_lt_top x hbounded)
  rw [hzero] at hlim
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 hlim _ he2).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (hclock (n : ℝ≥0) η hη) _ he2] with k hk
  calc
    μ {b | η ≤ |lqgClockApprox γ hε (dyadicScale k) b (τ b).toNNReal - F b (τ b).toNNReal|}
        ≤ μ (A n) + μ {b | ∃ t ≤ (n : ℝ≥0),
          η ≤ |lqgClockApprox γ hε (dyadicScale k) b t - F b t|} := by
            apply (measure_mono ?_).trans (measure_union_le _ _)
            intro b hb
            by_cases h : (n : ℝ≥0∞) < τ b
            · exact Or.inl h
            · right
              refine ⟨(τ b).toNNReal, ?_, hb⟩
              have ht : τ b ≠ ∞ := ne_top_of_le_ne_top (by simp) (not_lt.mp h)
              simpa using (ENNReal.toNNReal_le_toNNReal ht (ENNReal.natCast_ne_top n)).2 (not_lt.mp h)
    _ ≤ e / 2 + e / 2 := add_le_add hn hk
    _ = e := ENNReal.add_halves e

end HarmonicBalls
