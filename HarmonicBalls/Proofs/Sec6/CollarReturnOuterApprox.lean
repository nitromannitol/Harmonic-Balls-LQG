import HarmonicBalls.Proofs.Sec6.CollarReturnProbability

/-! # Collar returns with varying outer domains

If both exit times converge to the same finite limit, a continuous path
cannot return to a closed core separated from the limiting exit position.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess
open scoped ENNReal NNReal Topology

/-- A path cannot return to a closed core between two exit times converging to
the same finite exit time whose exit position is outside the core. -/
theorem eventually_no_core_return_of_exitTime_tendsto
    (D A : ℕ → Set ℂ) (U C : Set ℂ) (hC : IsClosed C) (ω : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime U ω ≠ ∞)
    (hexit : ω ((ContinuousPath.exitTime U ω).toNNReal) ∉ C)
    (hD : Tendsto (fun n => ContinuousPath.exitTime (D n) ω) atTop
      (𝓝 (ContinuousPath.exitTime U ω)))
    (hA : Tendsto (fun n => ContinuousPath.exitTime (A n) ω) atTop
      (𝓝 (ContinuousPath.exitTime U ω))) :
    ∀ᶠ n in atTop, ¬ ∃ t : ℝ≥0,
      ContinuousPath.exitTime (D n) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (A n) ω ∧ ω t ∈ C := by
  classical
  let τ := ContinuousPath.exitTime U ω
  let t : ℕ → ℝ≥0 := fun n =>
    if h : ∃ s : ℝ≥0, ContinuousPath.exitTime (D n) ω ≤ (s : ℝ≥0∞) ∧
      (s : ℝ≥0∞) < ContinuousPath.exitTime (A n) ω ∧ ω s ∈ C
    then Classical.choose h else τ.toNNReal
  have hτ : (τ.toNNReal : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hfin
  let l : ℕ → ℝ≥0∞ := fun n => min (ContinuousPath.exitTime (D n) ω) τ
  let u : ℕ → ℝ≥0∞ := fun n => max (ContinuousPath.exitTime (A n) ω) τ
  have hl : Tendsto l atTop (𝓝 τ) := by simpa [l, τ] using hD.min (tendsto_const_nhds : Tendsto (fun _ : ℕ => τ) atTop (𝓝 τ))
  have hu : Tendsto u atTop (𝓝 τ) := by simpa [u, τ] using hA.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => τ) atTop (𝓝 τ))
  have htlo (n : ℕ) : l n ≤ (t n : ℝ≥0∞) := by
    dsimp [t]
    split
    · rename_i h
      exact (min_le_left _ _).trans (Classical.choose_spec h).1
    · rw [hτ]; exact min_le_right _ _
  have hthi (n : ℕ) : (t n : ℝ≥0∞) ≤ u n := by
    dsimp [t]
    split
    · rename_i h
      exact (Classical.choose_spec h).2.1.le.trans (le_max_left _ _)
    · rw [hτ]; exact le_max_right _ _
  have htlim : Tendsto (fun n => (t n : ℝ≥0∞)) atTop (𝓝 τ) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu htlo hthi
  have htlim' : Tendsto t atTop (𝓝 τ.toNNReal) := by
    simpa only [Function.comp_def, ENNReal.toNNReal_coe] using
      (ENNReal.tendsto_toNNReal hfin).comp htlim
  have hnot : ∀ᶠ n in atTop, ω (t n) ∉ C :=
    (ω.continuous.continuousAt.tendsto.comp htlim') (hC.isOpen_compl.mem_nhds hexit)
  filter_upwards [hnot] with n hn
  intro h
  apply hn
  dsimp [t]
  rw [dite_eq_left h]
  exact (Classical.choose_spec h).2.2


/-- Exit times decrease to the exit time of an intersection along a decreasing
sequence of arbitrary domains. -/
theorem tendsto_exitTime_antitone_iInter
    {A : ℕ → Set ℂ} (hanti : Antitone A) (ω : ContinuousPath ℂ) :
    Tendsto (fun n => ContinuousPath.exitTime (A n) ω) atTop
      (𝓝 (ContinuousPath.exitTime (⋂ n, A n) ω)) := by
  have hinf : (⨅ n, ContinuousPath.exitTime (A n) ω) =
      ContinuousPath.exitTime (⋂ n, A n) ω := by
    apply le_antisymm
    · rw [ContinuousPath.le_exitTime_iff]
      intro t ht
      have hn : ∃ n, ω t ∉ A n := by simpa only [mem_iInter, not_forall] using ht
      obtain ⟨n, hn⟩ := hn
      exact (iInf_le (fun n => ContinuousPath.exitTime (A n) ω) n).trans
        (ContinuousPath.exitTime_le_of_notMem (A n) ω t hn)
    · exact le_iInf fun n => ContinuousPath.exitTime_mono (iInter_subset A n) ω
  rw [← hinf]
  exact tendsto_atTop_iInf fun n m hnm => ContinuousPath.exitTime_mono (hanti hnm) ω

/-- If the outer exit times converge almost surely to the exit time of the
union, the probability of returning to an interior closed core tends to zero.
The outer-exit convergence is an explicit hypothesis. -/
theorem tendsto_core_return_probability_of_outer_exitTime_tendsto
    {D A : ℕ → Set ℂ} (hDopen : ∀ n, IsOpen (D n)) (hDmono : Monotone D)
    (hAopen : ∀ n, IsOpen (A n)) (hbounded : Bornology.IsBounded (⋃ n, D n))
    {C : Set ℂ} (hC : IsClosed C) (hCA : C ⊆ ⋃ n, D n)
    {x : ℂ} (hx : x ∈ ⋃ n, D n)
    (houter : ∀ᵐ ω ∂planarBrownianMotion x,
      Tendsto (fun n => ContinuousPath.exitTime (A n) ω) atTop
        (𝓝 (ContinuousPath.exitTime (⋃ n, D n) ω))) :
    Tendsto (fun n => planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (D n) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (A n) ω ∧ ω t ∈ C}) atTop (𝓝 0) := by
  let E : ℕ → Set (ContinuousPath ℂ) := fun n => {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (D n) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (A n) ω ∧ ω t ∈ C}
  have hmeas : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_core_return (hAopen n) (hDopen n) hC
  have hae : ∀ᵐ ω ∂planarBrownianMotion x, ∀ᶠ n in atTop, ω ∉ E n := by
    filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hbounded,
      ae_planarBrownianMotion_eval_zero x, houter] with ω hfin hstart houterω
    have hfront := ContinuousPath.coordinate_exitTime_mem_frontier (⋃ n, D n)
      (isOpen_iUnion hDopen) ω (hstart ▸ hx) hfin.ne
    have hexit : ω ((ContinuousPath.exitTime (⋃ n, D n) ω).toNNReal) ∉ C := by
      intro hc
      exact (disjoint_frontier_iff_isOpen.mpr (isOpen_iUnion hDopen)).le_bot ⟨hfront, hCA hc⟩
    exact eventually_no_core_return_of_exitTime_tendsto D A (⋃ n, D n) C hC ω hfin.ne hexit
      (tendsto_exitTime_open_iUnion hDopen hDmono ω) houterω
  have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (μ := planarBrownianMotion x) (As := E) (A := ∅) atTop MeasurableSet.empty hmeas
    (by filter_upwards [hae] with ω hω; filter_upwards [hω] with n hn; simpa using hn)
  simpa [E] using hlim


/-- For a decreasing outer approximation of the closure, boundary regularity
reduces enlarged-domain return decay to equality of the open and closed exit
times. -/
theorem tendsto_core_return_probability_of_regular_boundary
    {D A : ℕ → Set ℂ} (hDopen : ∀ n, IsOpen (D n)) (hDmono : Monotone D)
    (hAopen : ∀ n, IsOpen (A n)) (hAanti : Antitone A)
    (hinter : (⋂ n, A n) = closure (⋃ n, D n))
    (hbounded : Bornology.IsBounded (⋃ n, D n))
    {C : Set ℂ} (hC : IsClosed C) (hCA : C ⊆ ⋃ n, D n)
    {x : ℂ} (hx : x ∈ ⋃ n, D n)
    (hregular : ∀ᵐ ω ∂planarBrownianMotion x,
      ContinuousPath.exitTime (closure (⋃ n, D n)) ω =
        ContinuousPath.exitTime (⋃ n, D n) ω) :
    Tendsto (fun n => planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (D n) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (A n) ω ∧ ω t ∈ C}) atTop (𝓝 0) := by
  apply tendsto_core_return_probability_of_outer_exitTime_tendsto
    hDopen hDmono hAopen hbounded hC hCA hx
  filter_upwards [hregular] with ω hω
  have h := tendsto_exitTime_antitone_iInter hAanti ω
  simpa only [hinter, hω] using h

end HarmonicBalls.Section6
