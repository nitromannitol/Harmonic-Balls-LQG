import HarmonicBalls.Proofs.Sec6.CompactFullMass
import MarkovProcess.Path.Exhaustion
import MarkovProcess.Killed.Kernel

/-! # Avoidance of compact sets before exit

Pathwise exit-time identities and continuity of probability for the compact
sets used in the good-annulus contradiction.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess
open scoped ENNReal Topology

/-- The first entry time into a union is the infimum of the entry times. -/
theorem exitTime_compl_iUnion {ι : Type*} (K : ι → Set ℂ) (ω : ContinuousPath ℂ) :
    ContinuousPath.exitTime (⋃ i, K i)ᶜ ω =
      ⨅ i, ContinuousPath.exitTime (K i)ᶜ ω := by
  apply le_antisymm
  · apply le_iInf
    intro i
    apply ContinuousPath.exitTime_mono
    intro x hx hxi
    exact hx (mem_iUnion.mpr ⟨i, hxi⟩)
  · rw [ContinuousPath.le_exitTime_iff]
    intro t ht
    have ht' : ω t ∈ ⋃ i, K i := by simpa using ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht'
    exact (iInf_le (fun i => ContinuousPath.exitTime (K i)ᶜ ω) i).trans
      (ContinuousPath.exitTime_le_of_notMem (K i)ᶜ ω t (by simpa using hi))

/-- Avoiding a countable union before exiting a domain is equivalent to
avoiding each member before exit. -/
theorem avoid_iUnion_before_exit (U : Set ℂ) (K : ℕ → Set ℂ) :
    {ω : ContinuousPath ℂ | ContinuousPath.exitTime U ω ≤
        ContinuousPath.exitTime (⋃ n, K n)ᶜ ω} =
      ⋂ n, {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime (K n)ᶜ ω} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter, exitTime_compl_iUnion, le_iInf_iff]

/-- Staying in a set until exit entails avoidance of any disjoint set. -/
theorem stay_subset_avoid_before_exit (U Y K : Set ℂ) (hKY : Disjoint K Y) :
    {ω : ContinuousPath ℂ | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Y ω} ⊆
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω} := by
  intro ω hω
  apply hω.trans (ContinuousPath.exitTime_mono ?_ ω)
  intro z hz hzk
  exact (disjoint_left.mp hKY hzk) hz

/-- For compact obstacles the avoidance event is Borel. -/
theorem measurableSet_avoid_before_exit {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) :
    MeasurableSet {ω : ContinuousPath ℂ |
      ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω} := by
  exact measurableSet_le (ContinuousPath.measurable_exitTime U hU)
    (ContinuousPath.measurable_exitTime Kᶜ hK.isClosed.isOpen_compl)

/-- Avoidance probabilities for increasing compact obstacles converge to the
avoidance probability for their union. -/
theorem tendsto_avoidance_probability_iUnion {U : Set ℂ} (hU : IsOpen U)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n)) (hmono : Monotone K)
    (x : ℂ) :
    Tendsto (fun n => planarBrownianMotion x
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime (K n)ᶜ ω})
      atTop (𝓝 (planarBrownianMotion x
        {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime (⋃ n, K n)ᶜ ω})) := by
  rw [avoid_iUnion_before_exit]
  apply tendsto_measure_iInter_atTop
  · intro n
    exact (measurableSet_avoid_before_exit hU (hK n)).nullMeasurableSet
  · intro m n hmn ω hω
    exact hω.trans (ContinuousPath.exitTime_mono (compl_subset_compl.mpr (hmono hmn)) ω)
  · exact ⟨0, measure_ne_top _ _⟩

/-- The compact avoidance probability is measurable as a function of the
Brownian starting point. -/
theorem measurable_avoidance_probability {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsCompact K) :
    Measurable (fun x : ℂ => planarBrownianMotion x
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω}) := by
  exact (Measure.measurable_coe (measurableSet_avoid_before_exit hU hK)).comp
    planarBrownianMotion.measurable

/-- If the obstacle is hit at time zero and exit takes positive time almost
surely, its avoidance probability is zero. -/
theorem avoidance_probability_eq_zero_of_instant_hit {U E : Set ℂ} (x : ℂ)
    (hE : ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    (hU : ∀ᵐ ω ∂(planarBrownianMotion x), 0 < ContinuousPath.exitTime U ω) :
    planarBrownianMotion x {ω | ContinuousPath.exitTime U ω ≤
      ContinuousPath.exitTime Eᶜ ω} = 0 := by
  have ha : ∀ᵐ ω ∂(planarBrownianMotion x), ¬ (ContinuousPath.exitTime U ω ≤
      ContinuousPath.exitTime Eᶜ ω) := by
    filter_upwards [hE, hU] with ω hωE hωU havoid
    rw [hωE] at havoid
    exact (not_le_of_gt hωU) havoid
  simpa only [not_not] using ae_iff.mp ha

/-- A Brownian path started inside an open set exits at a positive time. -/
theorem ae_planarBrownianMotion_exitTime_pos {U : Set ℂ} (hU : IsOpen U)
    {x : ℂ} (hx : x ∈ U) :
    ∀ᵐ ω ∂(planarBrownianMotion x), 0 < ContinuousPath.exitTime U ω := by
  filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω hω
  apply (ContinuousPath.exitTime_pos_iff U hU ω).mpr
  simpa only [hω] using hx

/-- If Brownian motion hits the union instantly, the compact avoidance
probabilities tend to zero for every starting point inside the domain. -/
theorem tendsto_avoidance_probability_zero_of_instant_hit
    {U : Set ℂ} (hU : IsOpen U) (K : ℕ → Set ℂ)
    (hK : ∀ n, IsCompact (K n)) (hmono : Monotone K) {x : ℂ} (hx : x ∈ U)
    (hE : ∀ᵐ ω ∂(planarBrownianMotion x),
      ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0) :
    Tendsto (fun n => planarBrownianMotion x
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime (K n)ᶜ ω}) atTop (𝓝 0) := by
  have hzero := avoidance_probability_eq_zero_of_instant_hit x hE
    (ae_planarBrownianMotion_exitTime_pos hU hx)
  simpa only [hzero] using tendsto_avoidance_probability_iUnion hU K hK hmono x

end HarmonicBalls.Section6
