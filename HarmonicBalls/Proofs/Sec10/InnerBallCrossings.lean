import HarmonicBalls.Proofs.Sec10.UniformPoleNeighborhood

/-!
# Crossing components and an inner ball

If a set contains a ball extending beyond the inner circle, every annular
crossing component meets that ball and hence all such components coincide.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- If `G` contains a ball about the crossing center which extends beyond the
inner circle and stays inside the outer crossing ball, there is at most one
crossing component. -/
theorem encard_crossingComponents_le_one_of_inner_ball
    {G : Set ℂ} {w : ℂ} {r s R : ℝ} (hs : 0 < s) (hrs : r < s) (hsR : s ≤ R)
    (hball : ball w s ⊆ G) :
    (crossingComponents (G ∩ ball w R) w r R).encard ≤ 1 := by
  let F := G ∩ ball w R
  have hballF : ball w s ⊆ F := fun x hx => ⟨hball hx, ball_subset_ball hsR hx⟩
  have hwball : w ∈ ball w s := mem_ball_self hs
  have hballcomp : ball w s ⊆ connectedComponentIn F w :=
    (isConnected_ball hs).isPreconnected.subset_connectedComponentIn hwball hballF
  have hsub : crossingComponents F w r R ⊆ {connectedComponentIn F w} := by
    intro C hC
    obtain ⟨p, hpC, hps⟩ := hC.2.1
    have hpball : p ∈ ball w s := mem_ball.mpr ((mem_sphere.mp hps).trans_lt hrs)
    obtain ⟨v, hvball, hvC⟩ := mem_closure_iff.mp hpC _ isOpen_ball hpball
    have hvcomp : v ∈ connectedComponentIn F w := hballcomp hvball
    obtain ⟨x, hx, rfl⟩ := hC.1
    simpa only [mem_singleton_iff] using (connectedComponentIn_eq hvC).trans (connectedComponentIn_eq hvcomp).symm
  exact (Set.encard_mono hsub).trans (by simp)

/-- A ball around the pole gives the one-crossing estimate as soon as it
extends beyond the inner crossing circle. -/
theorem encard_crossingComponents_le_one_of_pole_ball
    {G : Set ℂ} {z w : ℂ} {δ ρ : ℝ} (hρ : 0 < ρ)
    (hδ : dist w z + ρ / 3 < δ) (hball : ball z δ ⊆ G) :
    (crossingComponents (G ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ 1 := by
  let s : ℝ := min ((δ - dist w z + ρ / 3) / 2) (2 * ρ)
  have hρs : ρ / 3 < s := by dsimp [s]; apply lt_min <;> linarith
  have hs : 0 < s := by linarith
  have hsR : s ≤ 2 * ρ := min_le_right _ _
  have hsδ : s + dist w z < δ := by
    have h := min_le_left ((δ - dist w z + ρ / 3) / 2) (2 * ρ)
    dsimp [s]
    linarith
  apply encard_crossingComponents_le_one_of_inner_ball hs hρs hsR
  intro x hx
  apply hball
  rw [mem_ball] at hx ⊢
  have ht := dist_triangle x w z
  linarith

/-- Under volume growth, a common pole ball controls every crossing whose
inner circle lies strictly within that ball, uniformly over poles on a
compact subdisc and masses above a positive threshold. -/
theorem ae_near_pole_crossings_of_inner_circle
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b t₀ : ℝ, b < 1 → 0 < t₀ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ ≤ b → ∀ t : ℝ, t₀ ≤ t →
      ∀ w : ℂ, ∀ ρ : ℝ, 0 < ρ → dist w z + ρ / 3 < δ →
      (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
        (2 * ρ)).encard ≤ 1 := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_uniform_pole_neighborhood_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα
    Ω P hC hcirc μ hGFF hμ] with ω hω
  intro b t₀ hb ht₀
  obtain ⟨δ, hδ, hpole⟩ := hω b t₀ hb ht₀
  exact ⟨δ, hδ, fun z hz t ht w ρ hρ hdist =>
    encard_crossingComponents_le_one_of_pole_ball hρ hdist (hpole z hz t ht)⟩

end HarmonicBalls
