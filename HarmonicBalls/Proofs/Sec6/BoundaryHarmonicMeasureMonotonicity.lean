import HarmonicBalls.Proofs.Sec6.FiniteBoundaryPoleSeparation
import HarmonicBalls.Proofs.Sec6.SubmartingaleHarmonicMeasure

/-! # Harmonic measure under removal away from a component -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology

/-- If the boundary of the smaller domain meets the component's closure only
on the boundary of the larger domain, an exit through the smaller boundary
while staying in the component is also an exit through the larger boundary. -/
theorem exitTime_le_of_frontier_subset
    {A A' Y : Set ℂ} (hA : IsOpen A) (hA' : IsOpen A') (hY : IsOpen Y)
    (hYA' : Y ⊆ A') (hfront : frontier A' ∩ closure Y ⊆ frontier A)
    (ω : ContinuousPath ℂ) (hstart : ω 0 ∈ Y)
    (hfin : ContinuousPath.exitTime Y ω ≠ ⊤)
    (hle : ContinuousPath.exitTime A' ω ≤ ContinuousPath.exitTime Y ω) :
    ContinuousPath.exitTime A ω ≤ ContinuousPath.exitTime Y ω := by
  have heq : ContinuousPath.exitTime A' ω = ContinuousPath.exitTime Y ω :=
    le_antisymm hle (ContinuousPath.exitTime_mono hYA' ω)
  have hfrontA' := ContinuousPath.coordinate_exitTime_mem_frontier A' hA' ω
    (hYA' hstart) (by rw [heq]; exact hfin)
  rw [heq] at hfrontA'
  have hfrontY := ContinuousPath.coordinate_exitTime_mem_frontier Y hY ω hstart hfin
  have hfrontA := hfront ⟨hfrontA', frontier_subset_closure hfrontY⟩
  have hnot : ω ((ContinuousPath.exitTime Y ω).toNNReal) ∉ A := by
    rw [hA.frontier_eq] at hfrontA
    exact hfrontA.2
  simpa only [ENNReal.coe_toNNReal hfin] using
    ContinuousPath.exitTime_le_of_notMem A ω ((ContinuousPath.exitTime Y ω).toNNReal) hnot

/-- The corresponding harmonic-measure event has no larger probability for
the smaller domain. -/
theorem harmonicMeasure_mono_of_frontier_subset
    {A A' Y : Set ℂ} (hA : IsOpen A) (hA' : IsOpen A') (hY : IsOpen Y)
    (hYb : Bornology.IsBounded Y) (hYA' : Y ⊆ A')
    (hfront : frontier A' ∩ closure Y ⊆ frontier A)
    {x : ℂ} (hx : x ∈ Y) :
    planarBrownianMotion x {ω | ContinuousPath.exitTime A' ω ≤ hittingTime (A' \ Y) ω} ≤
      planarBrownianMotion x {ω | ContinuousPath.exitTime A ω ≤ hittingTime (A \ Y) ω} := by
  apply measure_mono_ae
  filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hYb,
    ae_planarBrownianMotion_eval_zero x] with ω hfin hstart hω
  apply (exitTime_le_exitTime_iff_le_hittingTime_sdiff ω).mp
  apply exitTime_le_of_frontier_subset hA hA' hY hYA' hfront ω (hstart ▸ hx) hfin.ne
  exact (exitTime_le_exitTime_iff_le_hittingTime_sdiff ω).mpr hω

end HarmonicBalls.Section6
