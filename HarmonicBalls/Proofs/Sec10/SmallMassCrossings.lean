import HarmonicBalls.Proofs.Sec10.CompactCenterCrossings
import HarmonicBalls.Proofs.Sec7.ClusterUpperBound

/-!
# Small-mass annular crossings

A cluster confined to a ball of radius `r / 2` cannot cross an annulus with
radii `ρ / 3` and `2ρ` for `ρ ≥ r`. Proposition 7.1 then gives, at each
prescribed scale, a positive mass threshold uniform over poles in `B(0,1/2)`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- A set confined to a sufficiently small ball has no annular crossing
components at a larger scale. -/
theorem crossingComponents_eq_empty_of_closure_subset_ball
    {G : Set ℂ} {z w : ℂ} {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    (hG : closure G ⊆ ball z (r / 2)) :
    crossingComponents (G ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro C hC
  obtain ⟨p, hp, rfl⟩ := hC.1
  have hCsub : connectedComponentIn (G ∩ ball w (2 * ρ)) p ⊆ G :=
    (connectedComponentIn_subset _ _).trans inter_subset_left
  have hcl := (closure_mono hCsub).trans hG
  obtain ⟨⟨x, hxC, hxS⟩, ⟨y, hyC, hyS⟩⟩ := hC.2
  have hxz : dist x z < r / 2 := mem_ball.mp (hcl hxC)
  have hyz : dist y z < r / 2 := mem_ball.mp (hcl hyC)
  have hxw : dist x w = ρ / 3 := mem_sphere.mp hxS
  have hyw : dist y w = 2 * ρ := mem_sphere.mp hyS
  have hxy := dist_triangle x z y
  have hyx := dist_triangle y x w
  rw [dist_comm z y] at hxy
  rw [dist_comm y x] at hyx
  linarith

/-- For each fixed small scale, Proposition 7.1 gives a positive mass
threshold below which every cluster with pole in the half-disc has zero
crossings, simultaneously for every crossing center and larger radius. -/
theorem ae_small_mass_crossings_eq_empty_at_scale
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ r ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ w : ℂ, ∀ ρ : ℝ, r ≤ ρ →
        crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ) = ∅ := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ r hr
  have hprob := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ r hr
  filter_upwards [hprob.ae_eventually_dyadic] with ω hω
  obtain ⟨k, hk⟩ := hω.exists
  refine ⟨(2 : ℝ)⁻¹ ^ k, by positivity, ?_⟩
  intro t ht z hz w ρ hρ
  exact crossingComponents_eq_empty_of_closure_subset_ball hr.1 hρ (hk t ht z hz)

/-- Almost surely the small-mass no-crossing estimate holds at every positive
scale, with the mass threshold depending on that scale. -/
theorem ae_small_mass_crossings_eq_empty_all_scales
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ w : ℂ, ∀ ρ : ℝ, r ≤ ρ →
        crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ) = ∅ := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hcount : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ w : ℂ, ∀ ρ : ℝ,
      1 / ((n : ℝ) + 2) ≤ ρ →
        crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ) = ∅ := by
    intro n
    apply ae_small_mass_crossings_eq_empty_at_scale h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
    constructor
    · positivity
    · apply (div_lt_one (by positivity)).2
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  filter_upwards [ae_all_iff.mpr hcount] with ω hω
  intro r hr
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
  obtain ⟨T, hT, hbound⟩ := hω n
  refine ⟨T, hT, ?_⟩
  intro t ht z hz w ρ hρ
  apply hbound t ht z hz w ρ
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hcomp : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
    exact one_div_le_one_div_of_le hden (by linarith)
  exact hcomp.trans (hn.le.trans hρ)

/-- For crossing centers in the quarter-disc, sufficiently small mass needs
no restriction on the pole. The mass threshold can depend on the scale. -/
theorem ae_quarter_disc_crossings_for_small_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ T : ℝ, 0 < T ∧
      ∀ w ∈ ball (0 : ℂ) (1 / 4) \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t ∈ Ioc (0 : ℝ) T,
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hcross⟩ := ae_eventually_localized_crossings_exact_radius hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hcross α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_small_mass_crossings_eq_empty_all_scales h71 γ α₀ hγ hγ2 hα₀
      Ω P hC hcirc μ hGFF hμ] with ω hcross hsmall
  filter_upwards [hcross, (eventually_lt_nhds (show (0 : ℝ) < (1 / 8 : ℝ) ^ 2 by positivity)).filter_mono
      nhdsWithin_le_nhds, (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hcross hε hεpos
  change 0 < ε at hεpos
  have hsqrt : Real.sqrt ε < (1 / 8 : ℝ) := by
    have hs := Real.sqrt_lt_sqrt hεpos.le hε
    simpa using hs
  obtain ⟨T, hT, hTbound⟩ := hsmall ε hεpos
  refine ⟨T, hT, ?_⟩
  intro w hw
  have hw1 : w ∈ ball (0 : ℂ) 1 := (ball_subset_ball (by norm_num)) hw.1
  obtain ⟨ρ, hρ, hρbound⟩ := hcross w ⟨hw1, hw.2⟩
  have hwsmall : dist w 0 < (1 / 4 : ℝ) := mem_ball.mp hw.1
  have hboundary : dist w 0 + 2 * ρ < 1 := by linarith [hρ.2]
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht
  by_cases hz : z ∈ ball (0 : ℂ) (1 / 2)
  · rw [hTbound t ht z hz w ρ hρ.1]
    simp
  · by_cases hz1 : z ∈ ball (0 : ℂ) 1
    · have hzfar : (1 / 2 : ℝ) ≤ dist z 0 := by
        exact le_of_not_gt (fun h => hz (mem_ball.mpr h))
      have hzw : 2 * ρ < dist z w := by
        have htri := dist_triangle z w (0 : ℂ)
        linarith [hρ.2]
      exact hρbound z hz1 t ht.1 hboundary hzw
    · rw [cluster_eq_empty_of_pole_not_mem hz1 ht.1.le]
      have hempty : crossingComponents ((∅ : Set ℂ) ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro C hC
        obtain ⟨x, hx, _⟩ := hC.1
        exact hx.1
      rw [hempty]
      simp

end HarmonicBalls
