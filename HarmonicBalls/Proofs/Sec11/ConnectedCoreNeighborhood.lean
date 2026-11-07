import HarmonicBalls.Proofs.Sec11.IntermediateSquareCore
import LatticeProb.Topology.ConnectedThickening

/-! # Connected neighborhoods of compact cores -/

namespace HarmonicBalls
open Set Metric

/-- A compact connected planar core has a connected open neighborhood whose
closure is compact and lies inside any prescribed open neighborhood. -/
theorem exists_connected_precompact_neighborhood {C U : Set ℂ}
    (hC : IsCompact C) (hconn : IsConnected C) (hU : IsOpen U)
    (hCU : C ⊆ U) :
    ∃ V : Set ℂ, IsOpen V ∧ IsConnected V ∧ C ⊆ V ∧
      IsCompact (closure V) ∧ closure V ⊆ U := by
  obtain ⟨r, hr, hrU⟩ := hC.exists_cthickening_subset_open hU hCU
  refine ⟨thickening r C, isOpen_thickening,
    LatticeProb.Topology.isConnected_thickening hconn hr,
    self_subset_thickening hr C, ?_, ?_⟩
  · exact hC.cthickening.of_isClosed_subset isClosed_closure
      (closure_thickening_subset_cthickening r C)
  · exact (closure_thickening_subset_cthickening r C).trans hrU

end HarmonicBalls
