import HarmonicBalls.Proofs.Sec5.NoEntryTopology

/-! # Propagation of the no-entry property by mass continuity -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- An increasing family of sets of mass `s` cannot suddenly contain a set
of positive measure if, at every time, that set is either wholly contained
or disjoint. -/
theorem disjoint_at_later_time_of_mass_continuity
    {μ : Measure ℂ} {A : ℝ → Set ℂ} {B : Set ℂ} {a t : ℝ}
    (hB : MeasurableSet B) (hpos : 0 < μ B) (ha : 0 < a) (hat : a ≤ t)
    (hmono : MonotoneOn A (Ioi 0))
    (hmass : ∀ s : ℝ, 0 < s → μ (A s) = ENNReal.ofReal s)
    (hdich : ∀ s : ℝ, 0 < s → s ≤ t → B ⊆ A s ∨ Disjoint B (A s))
    (hstart : Disjoint B (A a)) : Disjoint B (A t) := by
  by_contra hdis
  rcases hdich t (lt_of_lt_of_le ha hat) le_rfl with hBt | hdis'
  · have hfinA : μ (A t) ≠ ⊤ := by
      rw [hmass t (lt_of_lt_of_le ha hat)]
      exact ENNReal.ofReal_ne_top
    have hfin : μ B ≠ ⊤ := ne_top_of_le_ne_top hfinA (measure_mono hBt)
    let d : ℝ := (μ B).toReal
    have hd : 0 < d := ENNReal.toReal_pos hpos.ne' hfin
    obtain ⟨n, hn⟩ := exists_nat_gt (max 1 ((t - a) / d))
    have hnpos : (0 : ℝ) < n := lt_trans (by norm_num) (lt_of_le_of_lt (le_max_left _ _) hn)
    have hgap : (t - a) / (n : ℝ) < d := by
      have := lt_of_le_of_lt (le_max_right 1 ((t - a) / d)) hn
      rw [div_lt_iff₀ hd] at this
      apply (div_lt_iff₀ hnpos).2
      nlinarith
    let step : ℝ := (t - a) / n
    have hstep : 0 ≤ step := div_nonneg (sub_nonneg.mpr hat) hnpos.le
    have hstepn : (n : ℝ) * step = t - a := by
      dsimp [step]
      field_simp
    have htimes : ∀ j : ℕ, j ≤ n → a ≤ a + j * step ∧ a + j * step ≤ t := by
      intro j hj
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
      constructor
      · nlinarith [mul_nonneg (Nat.cast_nonneg j) hstep]
      · nlinarith [mul_le_mul_of_nonneg_right hjn hstep]
    have hseq : ∀ j : ℕ, j ≤ n → Disjoint B (A (a + j * step)) := by
      intro j
      induction j with
      | zero =>
          intro _
          simpa using hstart
      | succ j ih =>
          intro hj
          have hj' : j ≤ n := Nat.le_trans (Nat.le_succ j) hj
          have hprev := ih hj'
          have hprevtime := htimes j hj'
          have hnexttime := htimes (j + 1) hj
          have hprevpos : 0 < a + (j : ℝ) * step := lt_of_lt_of_le ha hprevtime.1
          have hnextpos : 0 < a + (↑(j + 1) : ℝ) * step := lt_of_lt_of_le ha hnexttime.1
          rcases hdich _ hnextpos hnexttime.2 with hsub | hnext
          · have hle : μ (A (a + (j : ℝ) * step)) + μ B ≤
                μ (A (a + (↑(j + 1) : ℝ) * step)) :=
              measure_add_le_of_disjoint_entry hB hprev.symm
                (hmono hprevpos hnextpos (by push_cast; nlinarith)) hsub
            rw [hmass _ hprevpos, hmass _ hnextpos] at hle
            have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
            rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hfin,
              ENNReal.toReal_ofReal hprevpos.le, ENNReal.toReal_ofReal hnextpos.le] at hreal
            change a + (j : ℝ) * step + d ≤ a + (↑(j + 1) : ℝ) * step at hreal
            push_cast at hreal
            nlinarith
          · exact hnext
    have hend := hseq n le_rfl
    have heq : a + (n : ℝ) * step = t := by linarith
    rw [heq] at hend
    exact hdis hend
  · exact hdis hdis'

/-- The no-entry step in Proposition 5.6, including initial avoidance and
propagation by mass continuity. -/
theorem harmonicBallNoEntry : HarmonicBallNoEntryStep := by
  intro μ hpos Λ A z hΛ hA hbound t ht x r hr haway
  let _ : μ.IsOpenPosMeasure := hpos
  obtain ⟨a, ha, hat, hstart⟩ :=
    exists_disjoint_time_of_cluster_boundary hΛ hA hbound ht hr haway
  apply disjoint_at_later_time_of_mass_continuity isOpen_ball.measurableSet
    (isOpen_ball.measure_pos μ ⟨x, mem_ball_self hr⟩) ha hat hA.2.monotoneOn hA.2.measure_eq
    ?_ hstart
  intro s hs hst
  apply IsPreconnected.subset_or_disjoint_of_disjoint_frontier isPreconnected_ball
    (hA.2.isRegularOpen s hs).isOpen
  apply Set.disjoint_left.2
  intro y hy hyfront
  exact haway hy (closure_mono (hΛ.1.monotoneOn hs ht hst) (hbound s hs hyfront))

universe u

/-- Proposition 5.6 from Lemmas 9.3 and 9.4 and full support of the LQG
measure. -/
theorem uniquenessHarmonicBalls_of_boundary_and_fullSupport
    (h93 : HarmonicBallBoundarySubsetStmt.{u}) (h94 : RegularOpenEqOfAEEqStmt.{u})
    (hfull : LQGMeasureFullSupportStmt.{u}) : UniquenessHarmonicBallsStmt.{u} :=
  uniquenessHarmonicBalls_of_steps harmonicBallNoEntry h93 h94 hfull

end HarmonicBalls
