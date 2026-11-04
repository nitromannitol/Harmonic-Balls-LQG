import HarmonicBalls.Proofs.Sec10.PoleAvoidingTruncation
import HarmonicBalls.Proofs.Sec6.Assembly

/-! # Inner-ball avoidance for a pole-avoiding local component -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6

/-- If a component of an open connected set restricted to a disc omits a
point of the original set, then its failure to meet a surrounding annulus
forces it to miss the inner closed disc. -/
theorem component_inter_closedBall_eq_empty_of_point_not_mem
    {L : Set ℂ} {z x₀ : ℂ} {ρ d : ℝ} (hopen : IsOpen L)
    (hconn : IsPreconnected L) (hzL : z ∈ L) {Λ : Set ℂ}
    (hΛ : Λ ∈ connectedComponentsIn (L ∩ ball x₀ ρ)) (hzΛ : z ∉ Λ)
    (hd : d ∈ Ioo (ρ / 2) ρ)
    (hempty : Λ ∩ annulus x₀ (ρ / 2) d = ∅) : Λ ∩ closedBall x₀ (ρ / 2) = ∅ := by
  obtain ⟨y, -, rfl⟩ := hΛ
  set F := L ∩ ball x₀ ρ with hF
  set C := connectedComponentIn F y with hCdef
  by_contra hne
  obtain ⟨x, hxC, hxB⟩ := nonempty_iff_ne_empty.2 hne
  have hFo : IsOpen F := hopen.inter isOpen_ball
  have hCo : IsOpen C := hFo.connectedComponentIn
  have hCsub : C ⊆ F := connectedComponentIn_subset F y
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hnotA : ∀ w ∈ C, w ∉ annulus x₀ (ρ / 2) d := fun w hw hwA =>
    (eq_empty_iff_forall_notMem.1 hempty) w ⟨hw, hwA⟩
  set m := (ρ / 2 + d) / 2 with hm
  have hm1 : ρ / 2 < m := by rw [hm]; linarith [hd.1]
  have hm2 : m < d := by rw [hm]; linarith [hd.1]
  have hCm : C ⊆ closedBall x₀ (ρ / 2) := by
    have hsplit : C ⊆ ball x₀ m ∪ (closedBall x₀ m)ᶜ := by
      intro w hw
      by_cases h : dist w x₀ < m
      · exact Or.inl h
      · refine Or.inr fun hc => hnotA w hw ⟨mem_ball.2 ?_, fun hc' => ?_⟩
        · have := mem_closedBall.1 hc; linarith
        · have := mem_closedBall.1 hc'; linarith
    have hleft := IsPreconnected.subset_left_of_subset_union isOpen_ball isClosed_closedBall.isOpen_compl
      (disjoint_compl_right_iff_subset.2 ball_subset_closedBall) hsplit
      ⟨x, hxC, mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hxB) hm1)⟩ hCpre
    intro w hw
    have h1 := mem_ball.1 (hleft hw)
    by_contra h2
    exact hnotA w hw ⟨mem_ball.2 (by linarith), h2⟩
  have hclC : closure C ⊆ closedBall x₀ (ρ / 2) := closure_minimal hCm isClosed_closedBall
  have hCL : L ⊆ C ∪ (closure C)ᶜ := by
    intro w hwL
    by_cases hw : w ∈ closure C
    · left
      have hwB : w ∈ ball x₀ ρ := mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 (hclC hw)) (by linarith [hd.1, hd.2]))
      have hwF : w ∈ F := ⟨hwL, hwB⟩
      obtain ⟨v, hvW, hvC⟩ := mem_closure_iff.1 hw _ hFo.connectedComponentIn (mem_connectedComponentIn hwF)
      have e1 : connectedComponentIn F w = connectedComponentIn F v := connectedComponentIn_eq hvW
      have e2 : connectedComponentIn F y = connectedComponentIn F v := connectedComponentIn_eq hvC
      rw [hCdef, e2, ← e1]
      exact mem_connectedComponentIn hwF
    · exact Or.inr hw
  have hLC := IsPreconnected.subset_left_of_subset_union hCo isClosed_closure.isOpen_compl
    (disjoint_compl_right_iff_subset.2 subset_closure) hCL ⟨x, (hCsub hxC).1, hxC⟩ hconn
  exact hzΛ (hLC hzL)

/-- The inner-ball step for a local cluster component, without a restriction
on the pole's position relative to the disc. -/
theorem pole_avoiding_component_inter_closedBall_eq_empty
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {x₀ : ℂ} {ρ d : ℝ} {Λ : Set ℂ}
    (hΛ : Λ ∈ connectedComponentsIn (cluster μ 1 z t ∩ ball x₀ ρ)) (hzΛ : z ∉ Λ)
    (hd : d ∈ Ioo (ρ / 2) ρ)
    (hempty : Λ ∩ annulus x₀ (ρ / 2) d = ∅) : Λ ∩ closedBall x₀ (ρ / 2) = ∅ := by
  obtain ⟨hopen, hconn, -⟩ := cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ zero_lt_one hV hz ht
  exact component_inter_closedBall_eq_empty_of_point_not_mem hopen hconn.isPreconnected
    (mem_cluster_iff.mpr ⟨hz, Or.inl rfl⟩) hΛ hzΛ hd hempty

end HarmonicBalls
