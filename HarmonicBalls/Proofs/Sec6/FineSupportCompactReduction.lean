import HarmonicBalls.Proofs.Sec6.ShrinkingBrownianExit

/-! # Compact reduction for fine support

A locally full-mass Borel set contains a countable increasing union of compact
sets with the same local mass. Instantaneous hitting of the union then implies
instantaneous hitting of the original set.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess
open scoped ENNReal Topology

/-- A Borel set of full mass in a finite-mass ball has a compact exhaustion
whose union also has full mass in that ball. -/
theorem exists_compact_union_of_local_full_mass {μ : Measure ℂ} {E : Set ℂ}
    (hE : MeasurableSet E) {x : ℂ} {ε : ℝ}
    (hfinite : μ (Metric.ball x ε) ≠ ∞)
    (hfull : μ (Metric.ball x ε \ E) = 0) :
    ∃ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) ∧ Monotone K ∧
      (∀ n, K n ⊆ E ∩ Metric.ball x ε) ∧
      μ (Metric.ball x ε \ ⋃ n, K n) = 0 := by
  have hfin : μ (E ∩ Metric.ball x ε) ≠ ∞ :=
    ne_top_of_le_ne_top hfinite (measure_mono inter_subset_right)
  obtain ⟨K, L, hK, hsub, hL, hmono, hLK, hmass⟩ :=
    compact_full_mass_of_summable_exceptions
      (hE.inter Metric.isOpen_ball.measurableSet) hfin (fun _ => ∅)
      (fun _ => MeasurableSet.empty) (by simp)
  refine ⟨L, hL, hmono, ?_, ?_⟩
  · intro n
    exact (hLK n).trans (by simpa using hsub n)
  · apply measure_mono_null _ (show μ ((Metric.ball x ε \ E) ∪
        ((E ∩ Metric.ball x ε) \ ⋃ n, L n)) = 0 from ?_)
    · intro y hy
      by_cases hyE : y ∈ E
      · exact Or.inr ⟨⟨hyE, hy.1⟩, hy.2⟩
      · exact Or.inl ⟨hy.1, hyE⟩
    · have hu := measure_union_le (μ := μ) (Metric.ball x ε \ E)
        ((E ∩ Metric.ball x ε) \ ⋃ n, L n)
      rw [hfull, hmass, add_zero] at hu
      exact le_zero_iff.mp hu

/-- Instantaneous hitting passes from a subset to the containing set. -/
theorem ae_instant_hit_of_subset {x : ℂ} {F E : Set ℂ} (hFE : F ⊆ E)
    (hF : ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Fᶜ ω = 0) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0 := by
  filter_upwards [hF] with ω hω
  apply le_antisymm _ bot_le
  calc
    ContinuousPath.exitTime Eᶜ ω ≤ ContinuousPath.exitTime Fᶜ ω :=
      ContinuousPath.exitTime_mono (compl_subset_compl.mpr hFE) ω
    _ = 0 := hω

/-- To establish fine support at a point it suffices to prove instant hitting
for full-mass increasing compact unions in each sufficiently small ball. -/
theorem ae_instant_hit_of_compact_unions {μ : Measure ℂ} {x : ℂ} {ε : ℝ}
    (hfinite : μ (Metric.ball x ε) ≠ ∞)
    (hcompact : ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      μ (Metric.ball x ε \ ⋃ n, K n) = 0 →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0)
    {E : Set ℂ} (hE : MeasurableSet E) (hfull : μ (Metric.ball x ε \ E) = 0) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0 := by
  obtain ⟨K, hK, hmono, hsub, hmass⟩ :=
    exists_compact_union_of_local_full_mass hE hfinite hfull
  apply ae_instant_hit_of_subset _ (hcompact K hK hmono hmass)
  exact iUnion_subset fun n => (hsub n).trans inter_subset_left

/-- Recurring positive lower bounds for pre-exit hitting probabilities imply
fine support, provided positive instant-hit probability is almost sure. -/
theorem ae_instant_hit_of_recurrent_lower_bounds
    {μ : Measure ℂ} {x : ℂ} {ε : ℝ}
    (hfinite : μ (Metric.ball x ε) ≠ ∞)
    {r R : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (hranti : Antitone r)
    (hrec : ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N, a ≤ R n)
    (hbound : ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      μ (Metric.ball x ε \ ⋃ n, K n) = 0 →
      ∀ᶠ n in atTop, ENNReal.ofReal (R n) ≤ planarBrownianMotion x
        {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
          ContinuousPath.exitTime (Metric.ball x (r n)) ω})
    (hzeroOne : ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      0 < planarBrownianMotion x {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0} →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0)
    {E : Set ℂ} (hE : MeasurableSet E) (hfull : μ (Metric.ball x ε \ E) = 0) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0 := by
  obtain ⟨a, ha, hrec⟩ := hrec
  apply ae_instant_hit_of_compact_unions hfinite ?_ hE hfull
  intro K hK hmono hmass
  apply hzeroOne K hK hmono
  have hfreq : ∃ᶠ n in atTop, ENNReal.ofReal a ≤ planarBrownianMotion x
      {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime (Metric.ball x (r n)) ω} := by
    have hf : ∃ᶠ n in atTop, a ≤ R n := frequently_atTop.mpr hrec
    exact (hf.and_eventually (hbound K hK hmono hmass)).mono
      (fun n hn => (ENNReal.ofReal_le_ofReal hn.1).trans hn.2)
  have hp := le_instant_hit_probability_of_frequently_le_exitTime x K hK hr hranti
    (ENNReal.ofReal a) hfreq
  exact (ENNReal.ofReal_pos.mpr ha).trans_le hp

end HarmonicBalls.Section6
