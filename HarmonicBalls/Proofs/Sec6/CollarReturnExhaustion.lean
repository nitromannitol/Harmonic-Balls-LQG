import HarmonicBalls.Proofs.Sec6.ExitTimeExhaustion
import HarmonicBalls.Proofs.Sec6.CollarAvoidanceComparison

/-! # Returns to a closed core along an exhaustion -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess
open scoped ENNReal NNReal Topology

/-- Along an open exhaustion, a continuous path whose finite exit position is
outside a closed core eventually cannot return to the core between the two
exit times. -/
theorem eventually_no_core_return_of_open_exhaustion
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    {C : Set ℂ} (hC : IsClosed C) (ω : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime (⋃ n, D n) ω ≠ ∞)
    (hexit : ω ((ContinuousPath.exitTime (⋃ n, D n) ω).toNNReal) ∉ C) :
    ∀ᶠ n in atTop, ¬ ∃ t : ℝ≥0,
      ContinuousPath.exitTime (D n) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (⋃ n, D n) ω ∧ ω t ∈ C := by
  classical
  let τ := ContinuousPath.exitTime (⋃ n, D n) ω
  let t : ℕ → ℝ≥0 := fun n =>
    if h : ∃ s : ℝ≥0, ContinuousPath.exitTime (D n) ω ≤ (s : ℝ≥0∞) ∧
      (s : ℝ≥0∞) < τ ∧ ω s ∈ C then Classical.choose h else τ.toNNReal
  have hτ : (τ.toNNReal : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hfin
  have htlo (n : ℕ) : ContinuousPath.exitTime (D n) ω ≤ (t n : ℝ≥0∞) := by
    dsimp [t]
    split
    · rename_i h
      exact (Classical.choose_spec h).1
    · rw [hτ]
      exact ContinuousPath.exitTime_mono (subset_iUnion D n) ω
  have hthi (n : ℕ) : (t n : ℝ≥0∞) ≤ τ := by
    dsimp [t]
    split
    · rename_i h
      exact (Classical.choose_spec h).2.1.le
    · rw [hτ]
  have htlim : Tendsto (fun n => (t n : ℝ≥0∞)) atTop (𝓝 τ) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_exitTime_open_iUnion hopen hmono ω) tendsto_const_nhds htlo hthi
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


/-- Brownian motion started in the bounded union eventually has no return to
an interior closed core after exiting any domain containing the corresponding
exhaustion member. The conclusion holds simultaneously for all such domains. -/
theorem ae_eventually_no_core_return_of_open_exhaustion
    {D : ℕ → Set ℂ} (hopen : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    (hbounded : Bornology.IsBounded (⋃ n, D n))
    {C : Set ℂ} (hC : IsClosed C) (hCA : C ⊆ ⋃ n, D n)
    {x : ℂ} (hx : x ∈ ⋃ n, D n) :
    ∀ᵐ ω ∂planarBrownianMotion x, ∀ᶠ n in atTop, ∀ B : Set ℂ, D n ⊆ B →
      ¬ ∃ t : ℝ≥0, ContinuousPath.exitTime B ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (⋃ n, D n) ω ∧ ω t ∈ C := by
  filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hbounded,
    ae_planarBrownianMotion_eval_zero x] with ω hfin hstart
  have hfront := ContinuousPath.coordinate_exitTime_mem_frontier (⋃ n, D n)
    (isOpen_iUnion hopen) ω (hstart ▸ hx) hfin.ne
  have hexit : ω ((ContinuousPath.exitTime (⋃ n, D n) ω).toNNReal) ∉ C := by
    intro hc
    exact (disjoint_frontier_iff_isOpen.mpr (isOpen_iUnion hopen)).le_bot ⟨hfront, hCA hc⟩
  filter_upwards [eventually_no_core_return_of_open_exhaustion hopen hmono hC ω hfin.ne hexit]
    with n hn B hDB hreturn
  obtain ⟨t, htB, htA, htC⟩ := hreturn
  exact hn ⟨t, (ContinuousPath.exitTime_mono hDB ω).trans htB, htA, htC⟩

end HarmonicBalls.Section6
