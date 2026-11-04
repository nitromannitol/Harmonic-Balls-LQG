import HarmonicBalls.Proofs.Sec10.ComplementaryHoleCrossing
import HarmonicBalls.Proofs.Sec10.ComplementComponents
import HarmonicBalls.Proofs.Sec6.HarnackIteration

/-!
# An annular obstruction to crossing containment

The following deterministic model satisfies the topological hypotheses used
in the proof of Lemma 10.5 but fails its crossing conclusion. It makes no
assertion that the model is an LQG cluster.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- An open connected set compactly contained in the unit disk can have a
complementary component with connected complement and compactly contained
frontier for which crossing containment fails. -/
theorem exists_annular_hole_crossing_obstruction :
    ∃ G U : Set ℂ, IsOpen G ∧ IsConnected G ∧ closure G ⊆ ball 0 1 ∧
      U ∈ connectedComponentsIn (closure G)ᶜ ∧ IsConnected Uᶜ ∧
      closure (frontier U) ⊆ ball 0 1 ∧
      ∃ (w : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧
        closure (annulus w r R) ⊆ ball 0 1 ∧
        ∃ C ∈ crossingComponents (Uᶜ ∩ annulus w r R) w r R,
          ¬ ∃ C' ∈ crossingComponents (G ∩ annulus w r R) w r R, C' ⊆ C := by
  let G : Set ℂ := annulus 0 (1 / 2) (3 / 4)
  let K : Set ℂ := closure G
  let U : Set ℂ := connectedComponentIn Kᶜ 2
  let V : Set ℂ := ball 0 (1 / 2)
  have hGo : IsOpen G := isOpen_ball.sdiff isClosed_closedBall
  have hGne : G.Nonempty := by
    refine ⟨((5 / 8 : ℝ) : ℂ), ?_⟩
    norm_num [G, annulus, mem_ball, mem_closedBall, dist_zero_right, Complex.norm_real]
  have hGc : IsConnected G := ⟨hGne, Section6.isPreconnected_annulus 0 (by norm_num) _⟩
  have hKunit : K ⊆ ball 0 1 := by
    have hKbound : K ⊆ closedBall 0 (3 / 4) :=
      closure_minimal (fun _ hx => ball_subset_closedBall hx.1) isClosed_closedBall
    exact hKbound.trans (closedBall_subset_ball (by norm_num))
  have hVdisK : Disjoint V K := by
    have hKout : K ⊆ Vᶜ := by
      apply closure_minimal _ isOpen_ball.isClosed_compl
      intro x hx hxV
      exact hx.2 (ball_subset_closedBall hxV)
    exact disjoint_left.mpr (fun x hxV hxK => hKout hxK hxV)
  have h2 : (2 : ℂ) ∈ Kᶜ := by
    intro h
    have := hKunit h
    norm_num [mem_ball, dist_zero_right] at this
  have hU : U ∈ connectedComponentsIn Kᶜ := ⟨2, h2, rfl⟩
  have hUc : IsConnected Uᶜ :=
    isConnected_compl_component_compl isClosed_closure hGc.closure
  have hfront : closure (frontier U) ⊆ ball 0 1 := by
    apply (closure_minimal ?_ isClosed_closure).trans hKunit
    have h := frontier_connectedComponentIn_subset_frontier (F := Kᶜ)
      (show IsOpen Kᶜ from isClosed_closure.isOpen_compl) (2 : ℂ)
    rw [frontier_compl] at h
    exact h.trans isClosed_closure.frontier_subset
  have h0U : (0 : ℂ) ∉ U := by
    intro h0
    have h2U : (2 : ℂ) ∈ U := mem_connectedComponentIn h2
    obtain ⟨q, hqU, hqdist⟩ := isPreconnected_connectedComponentIn.intermediate_value
      h0 h2U (continuous_id.dist continuous_const).continuousOn
      (show dist (0 : ℂ) 0 ≤ (5 / 8 : ℝ) ∧ (5 / 8 : ℝ) ≤ dist (2 : ℂ) 0 by norm_num)
    change dist q 0 = (5 / 8 : ℝ) at hqdist
    have hqG : q ∈ G := by
      change q ∈ ball (0 : ℂ) (3 / 4) \ closedBall 0 (1 / 2)
      rw [mem_sdiff, mem_ball, mem_closedBall, not_le, hqdist]
      norm_num
    exact (connectedComponentIn_subset Kᶜ 2 hqU) (subset_closure hqG)
  have hUV : Disjoint U V := by
    rw [disjoint_left]
    intro x hxU hxV
    have hVK : V ⊆ Kᶜ := fun _ hx => disjoint_left.mp hVdisK hx
    have hVsub : V ⊆ connectedComponentIn Kᶜ 0 :=
      (isConnected_ball (show (0 : ℝ) < 1 / 2 by norm_num)).isPreconnected.subset_connectedComponentIn
        (mem_ball_self (by norm_num)) hVK
    have h0V : (0 : ℂ) ∈ connectedComponentIn Kᶜ 0 := hVsub (mem_ball_self (by norm_num))
    have heq : U = connectedComponentIn Kᶜ 0 :=
      (connectedComponentIn_eq hxU).trans (connectedComponentIn_eq (hVsub hxV)).symm
    exact h0U (heq ▸ h0V)
  have hGV : Disjoint G V := by
    rw [disjoint_left]
    intro x hxG hxV
    exact hxG.2 (ball_subset_closedBall hxV)
  have hVdisk : (V ∩ ball (0 : ℂ) 1).Nonempty :=
    ⟨0, mem_ball_self (by norm_num), mem_ball_self (by norm_num)⟩
  exact ⟨G, U, hGo, hGc, hKunit, hU, hUc, hfront,
    complementary_open_hole_obstructs_crossing_containment hGV hUV isOpen_ball hVdisk⟩

end HarmonicBalls
