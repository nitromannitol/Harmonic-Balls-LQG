import HarmonicBalls.Proofs.Sec10.FrontierNoIsolatedPoints
import Mathlib.Topology.MetricSpace.Perfect

/-!
# Perfect complementary frontiers

Complementary cluster frontiers are perfect. In every neighborhood of a
frontier point they contain a continuous injective image of Cantor space.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- A closed set with no isolated points is perfect. -/
theorem perfect_of_no_isolated_points {S : Set ℂ} (hclosed : IsClosed S)
    (hacc : ∀ p ∈ S, ∀ r : ℝ, 0 < r → ∃ q ∈ S, q ∈ ball p r ∧ q ≠ p) :
    Perfect S := by
  refine ⟨hclosed, preperfect_iff_nhds.mpr ?_⟩
  intro p hp V hV
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨q, hqS, hqball, hqne⟩ := hacc p hp r hr
  exact ⟨q, ⟨hrV hqball, hqS⟩, hqne⟩

/-- Every neighborhood of a point of a perfect planar set contains a
continuous injective image of Cantor space lying in the set. -/
theorem Perfect.exists_cantor_in_ball {S : Set ℂ} (hS : Perfect S)
    {p : ℂ} (hp : p ∈ S) {r : ℝ} (hr : 0 < r) :
    ∃ f : (ℕ → Bool) → ℂ, range f ⊆ S ∩ ball p r ∧
      Continuous f ∧ Function.Injective f := by
  let T := closure (ball p (r / 2) ∩ S)
  have hT : Perfect T := (hS.acc.open_inter isOpen_ball).perfect_closure
  have hTne : T.Nonempty := ⟨p, subset_closure ⟨mem_ball_self (half_pos hr), hp⟩⟩
  have hTS : T ⊆ S := closure_minimal inter_subset_right hS.closed
  have hTb : T ⊆ ball p r := by
    have hTcb : T ⊆ closedBall p (r / 2) :=
      closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
    exact hTcb.trans (closedBall_subset_ball (half_lt_self hr))
  obtain ⟨f, hf, hcont, hinj⟩ := hT.exists_nat_bool_injection hTne
  exact ⟨f, hf.trans (subset_inter hTS hTb), hcont, hinj⟩

/-- Almost surely, the frontier of every complementary component of a
compactly contained cluster is perfect, and locally contains Cantor space.
Only the volume-growth input is assumed. -/
theorem ae_cluster_frontier_perfect
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      (frontier U).Nonempty ∧ Perfect (frontier U) ∧
      ∀ p ∈ frontier U, ∀ r : ℝ, 0 < r →
        ∃ f : (ℕ → Bool) → ℂ, range f ⊆ frontier U ∩ ball p r ∧
          Continuous f ∧ Function.Injective f := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_frontier_no_isolated_points hI2 γ hγ hγ2 α₀ hα
    Ω P hC hcirc μ hGFF hμ,
    clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω hgeom hcluster
  intro t ht z hz hcl U hU
  have hperfect := perfect_of_no_isolated_points isClosed_frontier (hω t ht z hz hcl U hU)
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hc := hcluster t 1 ht zero_lt_one z hz
  obtain ⟨v, hv, hUeq⟩ := hU
  have hUs : U ⊆ (closure (cluster (μ ω) 1 z t))ᶜ := by
    rw [← hUeq]
    exact connectedComponentIn_subset _ _
  have hUne : U ≠ univ := by
    obtain ⟨x, hx⟩ := hc.2.1.nonempty
    intro heq
    have hxU : x ∈ U := by rw [heq]; exact mem_univ x
    exact hUs hxU (subset_closure hx)
  have hnonempty : (frontier U).Nonempty := nonempty_frontier_iff.mpr ⟨hg.2.1.nonempty, hUne⟩
  exact ⟨hnonempty, hperfect, fun _ hp _ hr => Perfect.exists_cantor_in_ball hperfect hp hr⟩

end HarmonicBalls
