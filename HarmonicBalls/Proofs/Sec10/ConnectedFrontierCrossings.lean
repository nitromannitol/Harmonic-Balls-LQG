import HarmonicBalls.Proofs.Sec10.IntermediateFrontierCrossings
import HarmonicBalls.Proofs.Sec10.IrreducibleTwoSidedConnected
import HarmonicBalls.Proofs.Sec10.ClosedCrossingContinuum
import HarmonicBalls.Proofs.Sec10.ContinuumBoundaryBumping

/-!
# Connected frontier crossings

A compact connected set crossing an annulus has a single component of its
intersection with the annulus that crosses both boundary circles. Consequently,
multiple crossings of an open set force a frontier component to cross whenever
the frontier is compact and connected.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- A compact connected crossing yields a crossing component in the outer ball. -/
theorem IsConnected.exists_ball_component_crossing_of_compact
    {F : Set ℂ} (hF : IsConnected F) (hFc : IsCompact F)
    (w : ℂ) {r R : ℝ} (hrR : r < R) (hcross : CrossesAnnulus F w r R) :
    (crossingComponents (F ∩ ball w R) w r R).Nonempty := by
  obtain ⟨⟨x, hxcl, hxr⟩, ⟨y, hycl, hyR⟩⟩ := hcross
  have hxF : x ∈ F := hFc.isClosed.closure_eq ▸ hxcl
  have hyF : y ∈ F := hFc.isClosed.closure_eq ▸ hycl
  have hxball : x ∈ ball w R := mem_ball.mpr (by rw [mem_sphere.mp hxr]; exact hrR)
  have hout : (F \ ball w R).Nonempty := by
    refine ⟨y, hyF, ?_⟩
    intro hy
    have h := mem_ball.mp hy
    rw [mem_sphere.mp hyR] at h
    exact lt_irrefl R h
  obtain ⟨q, hqcl, _, hqout⟩ :=
    IsConnected.closure_component_inter_open_meets_compl hF hFc isOpen_ball hout ⟨hxF, hxball⟩
  have hqR : q ∈ sphere w R := by
    have hqle : dist q w ≤ R := by
      have hsub : connectedComponentIn (F ∩ ball w R) x ⊆ closedBall w R :=
        fun _ ha => ball_subset_closedBall (connectedComponentIn_subset _ x ha).2
      exact mem_closedBall.mp (closure_minimal hsub isClosed_closedBall hqcl)
    have hqge : R ≤ dist q w := le_of_not_gt (fun h => hqout (mem_ball.mpr h))
    exact mem_sphere.mpr (le_antisymm hqle hqge)
  refine ⟨connectedComponentIn (F ∩ ball w R) x, ⟨x, ⟨hxF, hxball⟩, rfl⟩, ?_⟩
  exact ⟨⟨x, subset_closure (mem_connectedComponentIn ⟨hxF, hxball⟩), hxr⟩,
    ⟨q, hqcl, hqR⟩⟩

/-- A compact connected crossing contains an annular crossing component,
without requiring the whole continuum to lie in the outer closed ball. -/
theorem IsConnected.exists_annular_component_crossing_of_compact
    {F : Set ℂ} (hF : IsConnected F) (hFc : IsCompact F)
    (w : ℂ) {r R : ℝ} (hrR : r < R) (hcross : CrossesAnnulus F w r R) :
    (crossingComponents (F ∩ annulus w r R) w r R).Nonempty := by
  obtain ⟨C, hC⟩ := IsConnected.exists_ball_component_crossing_of_compact hF hFc w hrR hcross
  obtain ⟨D, hD, _⟩ := closed_ball_crossing_contains_annular_crossing_of_compact_continuum
    hFc.isClosed w hrR (fun K hKc hK hKball hKcross =>
      IsConnected.exists_annular_component_crossing hK hKc w hrR hKball hKcross) hC
  exact ⟨D, hD⟩

/-- Multiple crossings force an annular crossing component of the frontier
when that frontier is a compact continuum. -/
theorem frontier_component_crosses_of_multiple_crossingComponents
    {G : Set ℂ} (hG : IsOpen G) (hFc : IsCompact (frontier G))
    (hF : IsConnected (frontier G)) {w : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hcount : 1 < (crossingComponents (G ∩ ball w R) w r R).encard) :
    (crossingComponents (frontier G ∩ annulus w r R) w r R).Nonempty := by
  exact IsConnected.exists_annular_component_crossing_of_compact hF hFc w hrR
    (frontier_crosses_of_multiple_crossingComponents hG hr hrR hcount)

/-- For a compactly contained cluster with connected frontier, an excess of
crossings forces one annular frontier component to cross both circles. -/
theorem ae_excess_contained_crossings_force_frontier_component
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b : ℝ, b < 1 → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 b →
        IsConnected (frontier (cluster (μ ω) 1 z t)) →
        (⌈1 / α⌉₊ : ℕ∞) <
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard →
        ‖w‖ ≤ (b + 1) / 2 ∧ dist z w ≤ ρ + ρ / 50 ∧
        (crossingComponents (frontier (cluster (μ ω) 1 z t) ∩
          annulus w (ρ / 3) (2 * ρ)) w (ρ / 3) (2 * ρ)).Nonempty := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_excess_contained_crossings_meet_every_intermediate_sphere hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hbound
  intro b hb
  filter_upwards [hbound b hb,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hbound hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hbound w hw
  have hρpos : 0 < ρ := hε.trans_le hρ.1
  refine ⟨ρ, hρ, ?_⟩
  intro z hz t ht hcl hconnected hexcess
  obtain ⟨hwnear, hznear, hcross, _⟩ := hρbound z hz t ht hcl hexcess
  have hcompact : IsCompact (frontier (cluster (μ ω) 1 z t)) :=
    (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset isClosed_frontier
      (fun p hp => ball_subset_closedBall (hcl (frontier_subset_closure hp)))
  exact ⟨hwnear, hznear,
    IsConnected.exists_annular_component_crossing_of_compact hconnected hcompact w
      (by linarith) hcross⟩

end HarmonicBalls
