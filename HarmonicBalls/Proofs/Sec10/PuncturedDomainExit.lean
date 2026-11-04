import HarmonicBalls.Proofs.Sec10.PoleAvoidingGoodAnnulusDecay

/-! # Exit events for a puncture separated from the starting component -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6 MarkovProcess
open scoped ENNReal

/-- If the puncture is outside the closure of an open set `Y`, a path starting
in `Y` cannot exit the punctured domain before it leaves `Y` solely by reaching
the puncture. Thus the two exit-before-hitting events coincide pathwise. -/
theorem exit_punctured_before_hit_iff
    {A Y : Set ℂ} {z : ℂ} (hA : IsOpen A) (hY : IsOpen Y)
    (hYA : Y ⊆ A) (hzY : z ∉ closure Y)
    (p : ContinuousPath ℂ) (hp : p 0 ∈ Y) :
    ContinuousPath.exitTime (A \ {z}) p ≤ hittingTime ((A \ {z}) \ Y) p ↔
      ContinuousPath.exitTime A p ≤ hittingTime (A \ Y) p := by
  rw [← exitTime_le_exitTime_iff_le_hittingTime_sdiff,
    ← exitTime_le_exitTime_iff_le_hittingTime_sdiff]
  have hYsub : Y ⊆ A \ {z} := by
    intro x hx
    refine ⟨hYA hx, ?_⟩
    intro h
    have hxz : x = z := by simpa using h
    exact hzY (hxz ▸ subset_closure hx)
  have hmono : ContinuousPath.exitTime Y p ≤ ContinuousPath.exitTime (A \ {z}) p :=
    ContinuousPath.exitTime_mono hYsub p
  constructor
  · intro h
    by_contra hn
    have hlt : ContinuousPath.exitTime Y p < ContinuousPath.exitTime A p := lt_of_not_ge hn
    have heq : ContinuousPath.exitTime (A \ {z}) p = ContinuousPath.exitTime Y p := le_antisymm h hmono
    have hfin : ContinuousPath.exitTime Y p ≠ ⊤ := ne_of_lt (hlt.trans_le le_top)
    have hyfront := ContinuousPath.coordinate_exitTime_mem_frontier Y hY p hp hfin
    have hafin : ContinuousPath.exitTime (A \ {z}) p ≠ ⊤ := by simpa [heq] using hfin
    have hafront := ContinuousPath.coordinate_exitTime_mem_frontier (A \ {z})
      (hA.sdiff isClosed_singleton) p (hYsub hp) hafin
    have hmem : p ((ContinuousPath.exitTime Y p).toNNReal) ∈ A := by
      apply ContinuousPath.mem_of_lt_exitTime
      simpa [ENNReal.coe_toNNReal hfin] using hlt
    have hnot : p ((ContinuousPath.exitTime Y p).toNNReal) ∉ A \ {z} := by
      rw [hA.sdiff isClosed_singleton |>.frontier_eq] at hafront
      simpa [heq] using hafront.2
    have hz : p ((ContinuousPath.exitTime Y p).toNNReal) = z := by
      by_contra hne
      exact hnot ⟨hmem, by simpa using hne⟩
    exact hzY (hz ▸ frontier_subset_closure hyfront)
  · intro h
    exact (ContinuousPath.exitTime_mono sdiff_subset p).trans h

/-- Removing a point outside a connected component leaves that component
unchanged. -/
theorem connectedComponentIn_sdiff_singleton_eq
    {S : Set ℂ} {x z : ℂ} (hx : x ∈ S)
    (hz : z ∉ connectedComponentIn S x) :
    connectedComponentIn (S \ {z}) x = connectedComponentIn S x := by
  apply Subset.antisymm (connectedComponentIn_mono x sdiff_subset)
  apply isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hx)
  intro y hy
  exact ⟨connectedComponentIn_subset S x hy, by
    intro hyz
    have hyz' : y = z := by simpa using hyz
    exact hz (hyz' ▸ hy)⟩

/-- A puncture outside the closure of `Y` introduces no new boundary points
relevant to `Y`. -/
theorem frontier_puncture_inter_closure_subset
    (A Y : Set ℂ) (z : ℂ) (hz : z ∉ closure Y) :
    frontier (A \ {z}) ∩ closure Y ⊆ frontier A ∩ closure Y := by
  intro x hx
  refine ⟨?_, hx.2⟩
  have h := frontier_inter_subset A ({z}ᶜ) (by simpa [sdiff_eq] using hx.1)
  rcases h with h | h
  · exact h.1
  · have hxz : x = z := by
      have : x ∈ frontier ({z} : Set ℂ) := by simpa only [frontier_compl] using h.2
      have : x ∈ ({z} : Set ℂ) := by simpa using (frontier_subset_closure this)
      simpa using this
    exact (hz (hxz ▸ hx.2)).elim

/-- Removing a separated puncture preserves the Brownian exit-before-hitting
probability for paths started in the open set. -/
theorem planarBrownianMotion_exit_puncture_eq
    {A Y : Set ℂ} {z x : ℂ} (hA : IsOpen A) (hY : IsOpen Y)
    (hYA : Y ⊆ A) (hzY : z ∉ closure Y) (hx : x ∈ Y) :
    planarBrownianMotion x {p | ContinuousPath.exitTime (A \ {z}) p ≤
      hittingTime ((A \ {z}) \ Y) p} =
    planarBrownianMotion x {p | ContinuousPath.exitTime A p ≤ hittingTime (A \ Y) p} := by
  apply measure_congr
  filter_upwards [ae_planarBrownianMotion_eval_zero x] with p hp
  exact propext (exit_punctured_before_hit_iff hA hY hYA hzY p (hp ▸ hx))

end HarmonicBalls
