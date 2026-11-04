import HarmonicBalls.Proofs.Sec10.CompactPoleConfinement

/-!
# Boundary-strip crossings at small mass

For poles in a fixed subdisc, sufficiently small clusters stay uniformly
away from any prescribed outer strip. The mass threshold depends on the
strip and the pole subdisc, but not on the crossing radius.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Uniform confinement around poles in any fixed proper subdisc. -/
theorem ae_compact_poles_uniform_confinement
    (hvolume : LiouvilleVolumeGrowthStmt.{u}) (hconnected : ClusterOpenLaplacianStmt.{u})
    (hmass : ClusterConservationOfMassStmt.{u}) (hHarnack : HarnackTypeEstimateStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b r : ℝ, b < 1 → 0 < r → ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) b,
        closure (cluster (μ ω) 1 z t) ⊆ ball z r := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hdpos : ∀ n, 0 < d n := by intro n; dsimp [d]; positivity
  have hcount : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 - d n),
        closure (cluster (μ ω) 1 z t) ⊆ ball z (d n / 4) := by
    intro n
    have hprob := cluster_confinement_polyHighProb_of_margin hvolume hconnected hmass hHarnack
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ (1 - d n) (d n / 2)
      (by positivity) (by linarith [hdpos n])
    filter_upwards [hprob.ae_eventually_dyadic] with ω hω
    obtain ⟨k, hk⟩ := hω.exists
    refine ⟨(2 : ℝ)⁻¹ ^ k, by positivity, ?_⟩
    intro t ht z hz
    have hrad : d n / 2 / 2 = d n / 4 := by ring
    simpa only [hrad] using (hk t ht z hz)
  filter_upwards [ae_all_iff.mpr hcount] with ω hω
  intro b r hb hr
  have hsmall : 0 < min (1 - b) r := lt_min (by linarith) hr
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hsmall
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hdn : d n < min (1 - b) r := by
    dsimp [d]
    exact lt_of_le_of_lt (one_div_le_one_div_of_le hden (by linarith)) hn
  have hdb : d n < 1 - b := hdn.trans_le (min_le_left _ _)
  have hdr : d n < r := hdn.trans_le (min_le_right _ _)
  obtain ⟨T, hT, hbound⟩ := hω n
  refine ⟨T, hT, ?_⟩
  intro t ht z hz
  have hz' : z ∈ ball (0 : ℂ) (1 - d n) := ball_subset_ball (by linarith) hz
  exact (hbound t ht z hz').trans (ball_subset_ball (by linarith [hdpos n]))

/-- For poles in a fixed subdisc, a fixed outer strip has no crossings at
any sufficiently small crossing radius and any sufficiently small mass. -/
theorem ae_boundary_strip_empty_crossings_of_small_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hvolume : LiouvilleVolumeGrowthStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b c : ℝ, b < c → c < 1 → ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) b,
      ∀ w : ℂ, c ≤ ‖w‖ → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ (c - b) / 8 →
        crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ) = ∅ := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_compact_poles_uniform_confinement hvolume (clusterOpenLaplacian_proved hI2)
    (clusterConservationOfMass_proved hI2) (harnackTypeEstimateStmt_of_component h6)
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro b c hbc hc
  obtain ⟨T, hT, hconf⟩ := hω b ((c - b) / 4) (by linarith) (by linarith)
  refine ⟨T, hT, ?_⟩
  intro t ht z hz w hw ρ hρ hρsmall
  have hempty : cluster (μ ω) 1 z t ∩ ball w (2 * ρ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxz : dist x z < (c - b) / 4 := mem_ball.mp (hconf t ht z hz (subset_closure hx.1))
    have hzb : dist z 0 < b := mem_ball.mp hz
    have hxw : dist x w < 2 * ρ := mem_ball.mp hx.2
    have htri := dist_triangle w x (0 : ℂ)
    have htri' := dist_triangle x z (0 : ℂ)
    rw [dist_comm w x, dist_zero_right] at htri
    linarith
  rw [hempty]
  simp [crossingComponents, connectedComponentsIn]

end HarmonicBalls
