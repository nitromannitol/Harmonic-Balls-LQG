import HarmonicBalls.Proofs.Sec10.LocalHoleAnnuli

/-! # Sparse annular crossing containment and holes

Even at a dense set of centers and a sparse sequence of radii at each
center, crossing containment for one component rules out all others.
-/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter

universe u

/-- Every point in a complementary hole has a positive scale below which
every annulus of radii `r` and `2 * r` gives a whole-annulus obstruction. -/
theorem complementary_hole_fixed_ratio_all_small
    {G U V : Set ℂ} (hGV : Disjoint G V) (hUV : Disjoint U V)
    (hV : IsOpen V) {w : ℂ} (hw : w ∈ V ∩ ball (0 : ℂ) 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      closure (annulus w r (2 * r)) ⊆ V ∩ ball 0 1 ∧
      crossingComponents (Uᶜ ∩ annulus w r (2 * r)) w r (2 * r) = {annulus w r (2 * r)} ∧
      crossingComponents (G ∩ annulus w r (2 * r)) w r (2 * r) = ∅ ∧
      Disjoint (closure (annulus w r (2 * r))) (frontier U) := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp (hV.inter isOpen_ball) w hw
  refine ⟨ε / 2, by positivity, ?_⟩
  intro r hr hrε
  have hr2 : r < 2 * r := by linarith
  have hball : closedBall w (2 * r) ⊆ V ∩ ball (0 : ℂ) 1 :=
    (closedBall_subset_ball (by linarith)).trans hεsub
  have hcl : closure (annulus w r (2 * r)) ⊆ V ∩ ball (0 : ℂ) 1 := by
    apply (closure_minimal ?_ isClosed_closedBall).trans hball
    intro a ha
    exact ball_subset_closedBall ha.1
  have hcross := complementary_hole_crossing_is_whole_annulus hGV hUV hV w hr hr2
    (hball.trans inter_subset_left)
  exact ⟨hcl, hcross.1, hcross.2.1, hcross.2.2.2⟩

/-- If crossing containment holds at arbitrarily small annuli of radii
`r` and `2 * r` around a dense set of centers in the unit disk, the chosen
component is the entire complement of the closure. -/
theorem compl_closure_eq_of_dense_sparse_crossing_containment
    {G U D : Set ℂ} (hD : Dense D) (hGne : G.Nonempty) (hGdisk : closure G ⊆ ball 0 1)
    (hU : U ∈ connectedComponentsIn (closure G)ᶜ)
    (hcontain : ∀ w ∈ D ∩ ball (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 0 < r ∧ r < ε ∧
        (closure (annulus w r (2 * r)) ⊆ ball 0 1 →
        ∀ C ∈ crossingComponents (Uᶜ ∩ annulus w r (2 * r)) w r (2 * r),
          ∃ C' ∈ crossingComponents (G ∩ annulus w r (2 * r)) w r (2 * r), C' ⊆ C)) :
    (closure G)ᶜ = U := by
  classical
  obtain ⟨p, hp, rfl⟩ := hU
  let K := closure G
  let U := connectedComponentIn Kᶜ p
  have hKne : K.Nonempty := hGne.mono subset_closure
  have hUsub : U ⊆ Kᶜ := connectedComponentIn_subset _ _
  apply Subset.antisymm
  · intro y hy
    by_contra hyU
    let V := connectedComponentIn Kᶜ y
    have hyV : y ∈ V := mem_connectedComponentIn hy
    have hVopen : IsOpen V := isClosed_closure.isOpen_compl.connectedComponentIn
    have hVsub : V ⊆ Kᶜ := connectedComponentIn_subset _ _
    have hGV : Disjoint G V := by
      rw [disjoint_left]
      intro x hxG hxV
      exact hVsub hxV (subset_closure hxG)
    have hUV : Disjoint U V := by
      rw [disjoint_left]
      intro x hxU hxV
      have heq : U = V := (connectedComponentIn_eq hxU).trans (connectedComponentIn_eq hxV).symm
      rw [← heq] at hyV
      exact hyU hyV
    obtain ⟨x, hxV, hxK⟩ := closure_component_compl_inter_nonempty
      (K := K) isClosed_closure hKne hy
    have hxball : x ∈ ball (0 : ℂ) 1 := hGdisk hxK
    obtain ⟨q, hqball, hqV⟩ := mem_closure_iff.mp hxV _ isOpen_ball hxball
    obtain ⟨w, hwD, hwV, hwball⟩ := hD.exists_mem_open (hVopen.inter isOpen_ball)
      ⟨q, hqV, hqball⟩
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (hVopen.inter isOpen_ball) w ⟨hwV, hwball⟩
    obtain ⟨r, hr, hrδ, hcross⟩ := hcontain w ⟨hwD, hwball⟩ (δ / 2) (by positivity)
    have hr2 : r < 2 * r := by linarith
    have hball : closedBall w (2 * r) ⊆ V ∩ ball (0 : ℂ) 1 :=
      (closedBall_subset_ball (by linarith)).trans hδsub
    have hanncl : closure (annulus w r (2 * r)) ⊆ ball (0 : ℂ) 1 := by
      apply (closure_minimal ?_ isClosed_closedBall).trans (hball.trans inter_subset_right)
      intro a ha
      exact ball_subset_closedBall ha.1
    have hhole := complementary_hole_crossing_is_whole_annulus hGV hUV hVopen w hr hr2
      (hball.trans inter_subset_left)
    have hann : annulus w r (2 * r) ∈
        crossingComponents (Uᶜ ∩ annulus w r (2 * r)) w r (2 * r) := by
      rw [hhole.1]
      exact mem_singleton _
    obtain ⟨C, hC, _⟩ := hcross hanncl _ hann
    rw [hhole.2.1] at hC
    simp at hC
  · exact hUsub

/-- Sparse crossing containment for one component forces connectedness of
the closed cluster complement. -/
theorem isConnected_compl_closure_of_dense_sparse_crossing_containment
    {G U D : Set ℂ} (hD : Dense D) (hGne : G.Nonempty) (hGdisk : closure G ⊆ ball 0 1)
    (hU : U ∈ connectedComponentsIn (closure G)ᶜ)
    (hcontain : ∀ w ∈ D ∩ ball (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 0 < r ∧ r < ε ∧
        (closure (annulus w r (2 * r)) ⊆ ball 0 1 →
        ∀ C ∈ crossingComponents (Uᶜ ∩ annulus w r (2 * r)) w r (2 * r),
          ∃ C' ∈ crossingComponents (G ∩ annulus w r (2 * r)) w r (2 * r), C' ⊆ C)) :
    IsConnected (closure G)ᶜ := by
  have heq := compl_closure_eq_of_dense_sparse_crossing_containment hD hGne hGdisk hU hcontain
  obtain ⟨p, hp, rfl⟩ := hU
  rw [heq]
  exact isConnected_connectedComponentIn_iff.mpr hp

/-- For any measure, sparse crossing containment on a dense set of centers
forces a compactly contained cluster to have no complementary holes. -/
theorem cluster_compl_closure_connected_of_dense_sparse_crossing_containment
    (μ : Measure ℂ) {z : ℂ} {t : ℝ} (hz : z ∈ ball (0 : ℂ) 1)
    (hcl : closure (cluster μ 1 z t) ⊆ ball 0 1) {U D : Set ℂ}
    (hD : Dense D) (hU : U ∈ connectedComponentsIn (closure (cluster μ 1 z t))ᶜ)
    (hcontain : ∀ w ∈ D ∩ ball (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 0 < r ∧ r < ε ∧
        (closure (annulus w r (2 * r)) ⊆ ball 0 1 →
        ∀ C ∈ crossingComponents (Uᶜ ∩ annulus w r (2 * r)) w r (2 * r),
          ∃ C' ∈ crossingComponents (cluster μ 1 z t ∩ annulus w r (2 * r)) w r (2 * r),
            C' ⊆ C)) :
    IsConnected (closure (cluster μ 1 z t))ᶜ :=
  isConnected_compl_closure_of_dense_sparse_crossing_containment hD
    ⟨z, self_mem_cluster hz⟩ hcl hU hcontain

end HarmonicBalls
