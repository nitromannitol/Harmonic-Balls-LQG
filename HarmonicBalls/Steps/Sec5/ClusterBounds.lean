import HarmonicBalls.Draft.Section5
import HarmonicBalls.Draft.Section7
import HarmonicBalls.Draft.Section8
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# Cluster bounds in Section 5

The proof of Proposition 5.1 at lines 2101–2102 of the corrected paper uses
Proposition 7.1 at a fixed radius and the high-probability estimate at dyadic
scales. Proposition 5.3 is Proposition 8.1 with the quantifiers reordered.
These reductions keep the Section 7 and 8 results explicit as hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Proposition 5.1 from Proposition 7.1. -/
theorem clusterUpperBound_of_steps (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) :
    ClusterUpperBoundStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have h := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ (1 / 2) (by norm_num)
  filter_upwards [h.ae_eventually_dyadic] with ω hω
  obtain ⟨n, hn⟩ := hω.exists
  refine ⟨(2 : ℝ)⁻¹ ^ n, by positivity, ?_⟩
  intro z hz t ht htT x hx
  have hxz := hn t ⟨ht, htT.le⟩ z hz hx
  rw [mem_ball] at hxz hz ⊢
  have hdist := dist_triangle x z (0 : ℂ)
  rw [dist_zero_right, dist_zero_right] at hdist
  rw [dist_zero_right]
  norm_num at hxz hz
  linarith

/-- Proposition 5.3 from Proposition 8.1. -/
theorem clusterBoundaryMeasureZero_of_steps (h81 : BoundaryMeasureZeroOfCompactClusterStmt.{u}) :
    ClusterBoundaryMeasureZeroStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [h81 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro z hz t ht hcompact
  exact hω t ht z hz hcompact

end HarmonicBalls
