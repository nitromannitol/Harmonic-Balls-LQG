import HarmonicBalls.Proofs.Potential.LBMUniformDomainExit

/-! # Uniform convergence in probability of enclosed-domain exit times

The full dyadic sequence approximates time-changed exit times in probability,
uniformly over open domains contained in a fixed ball.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- Dyadic clock approximations converge in probability uniformly over open
    domains contained in a fixed ball around the starting point. -/
theorem IsLQGClock.tendsto_measure_uniform_clockApprox_lbmExitTime_enclosed_domains
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock planarBrownianMotion γ hε x F)
    (hF : ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F b))
    (R η : ℝ) (hη : 0 < η) :
    Tendsto (fun k : ℕ => planarBrownianMotion x
      {b | ∃ D : Set ℂ, IsOpen D ∧ D ⊆ Metric.ball x R ∧
        η ≤ |lqgClockApprox γ hε (dyadicScale k) b
          (ContinuousPath.exitTime D b).toNNReal - (lbmExitTime F D b).toReal|})
      atTop (𝓝 0) := by
  let μ := planarBrownianMotion x
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime (Metric.ball x R)
  let A : ℕ → Set (ContinuousPath ℂ) := fun n => {b | (n : ℝ≥0∞) < τ b}
  have hanti : Antitone A := by
    intro n m hnm b hb
    change (m : ℝ≥0∞) < τ b at hb
    change (n : ℝ≥0∞) < τ b
    exact lt_of_le_of_lt (by exact_mod_cast hnm) hb
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := A)
    (fun n => (measurableSet_lt measurable_const
      (ContinuousPath.measurable_exitTime _ Metric.isOpen_ball)).nullMeasurableSet)
    hanti ⟨0, measure_ne_top μ _⟩
  have hzero : μ (⋂ n, A n) = 0 := by
    apply measure_mono_null (t := {b | ¬ τ b < ∞})
    · intro b hb hfin
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin.ne
      exact (not_lt_of_ge hn.le) (Set.mem_iInter.mp hb n)
    · exact ae_iff.1 (Section6.ae_planarBrownian_exitTime_bounded_lt_top x
        (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball x R)))
  rw [hzero] at hlim
  have hnull : μ {b | ¬ IsTimeChangeClock (F b)} = 0 := ae_iff.1 hF
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 hlim _ he2).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (hclock (n : ℝ≥0) η hη) _ he2] with k hk
  change μ (A n) ≤ e / 2 at hn
  change μ {b | ∃ t ≤ (n : ℝ≥0),
    η ≤ |lqgClockApprox γ hε (dyadicScale k) b t - F b t|} ≤ e / 2 at hk
  calc
    μ {b | ∃ D : Set ℂ, IsOpen D ∧ D ⊆ Metric.ball x R ∧
        η ≤ |lqgClockApprox γ hε (dyadicScale k) b
          (ContinuousPath.exitTime D b).toNNReal - (lbmExitTime F D b).toReal|}
        ≤ μ {b | ¬ IsTimeChangeClock (F b)} +
            (μ (A n) + μ {b | ∃ t ≤ (n : ℝ≥0),
              η ≤ |lqgClockApprox γ hε (dyadicScale k) b t - F b t|}) := by
      calc
        _ ≤ μ ({b | ¬ IsTimeChangeClock (F b)} ∪ (A n ∪ {b | ∃ t ≤ (n : ℝ≥0),
            η ≤ |lqgClockApprox γ hε (dyadicScale k) b t - F b t|})) := by
          apply measure_mono
          intro b ⟨D, hD, hsub, hb⟩
          by_cases hf : IsTimeChangeClock (F b)
          · right
            by_cases ht : (n : ℝ≥0∞) < τ b
            · exact Or.inl ht
            · right
              have hle : ContinuousPath.exitTime D b ≤ τ b := ContinuousPath.exitTime_mono hsub b
              have hτ : τ b ≠ ∞ := ne_top_of_le_ne_top (by simp) (not_lt.mp ht)
              have hfin : ContinuousPath.exitTime D b ≠ ∞ := ne_top_of_le_ne_top hτ hle
              have heq : (lbmExitTime F D b).toReal = F b (ContinuousPath.exitTime D b).toNNReal := by
                rw [lbmExitTime_eq_clockValue hD hf hfin]
                have hnneg : 0 ≤ F b (ContinuousPath.exitTime D b).toNNReal := by
                  simpa only [hf.map_zero] using hf.strictMono.monotone
                    (show (0 : ℝ≥0) ≤ (ContinuousPath.exitTime D b).toNNReal from bot_le)
                simp [hnneg]
              refine ⟨(ContinuousPath.exitTime D b).toNNReal, ?_, ?_⟩
              · have ht' : ContinuousPath.exitTime D b ≤ (n : ℝ≥0∞) := hle.trans (not_lt.mp ht)
                simpa using (ENNReal.toNNReal_le_toNNReal hfin (ENNReal.natCast_ne_top n)).2 ht'
              · simpa only [heq] using hb
          · exact Or.inl hf
        _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ e / 2 + e / 2 := by simpa only [hnull, zero_add] using add_le_add hn hk
    _ = e := ENNReal.add_halves e

end HarmonicBalls
