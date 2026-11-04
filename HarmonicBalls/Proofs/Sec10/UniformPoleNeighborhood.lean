import HarmonicBalls.Proofs.Sec4.ClusterLowerBound
import HarmonicBalls.Proofs.Sec10.PositiveMassCrossings

/-!
# Uniform pole neighborhoods on compact subdiscs

The logarithmic Green-function lower bound is uniform when poles stay in a
fixed compact subdisc. Together with the bounded Green potential this gives a
uniform neighborhood of all poles for masses above a positive threshold.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- The Green function diverges uniformly near poles in a fixed subdisc. -/
theorem exists_uniform_le_greenFunction_near_poles {b : ℝ} (hb : b < 1) (K : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 - b ∧
      ∀ z : ℂ, ‖z‖ ≤ b → ∀ x : ℂ, 0 < ‖x - z‖ → ‖x - z‖ < ε →
        K ≤ greenFunction (ball 0 1) z x := by
  let ρ : ℝ := (1 - b) / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have he : 0 < Real.exp (-(2 * Real.pi * K)) := Real.exp_pos _
  refine ⟨min (ρ / 2) (ρ * Real.exp (-(2 * Real.pi * K))),
    lt_min (half_pos hρ) (mul_pos hρ he), ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by dsimp [ρ]; linarith)
  intro z hz x hx0 hxε
  have hxρ2 : ‖x - z‖ < ρ / 2 := hxε.trans_le (min_le_left _ _)
  have hxe : ‖x - z‖ < ρ * Real.exp (-(2 * Real.pi * K)) := hxε.trans_le (min_le_right _ _)
  have hsub : closedBall x ρ ⊆ ball (0 : ℂ) 1 := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball_zero_iff]
    calc ‖y‖ = ‖(y - x) + (x - z) + z‖ := by congr 1; ring
      _ ≤ ‖y - x‖ + ‖x - z‖ + ‖z‖ := norm_add₃_le
      _ < 1 := by dsimp [ρ] at hy hxρ2; linarith
  have hzx0 : 0 < ‖z - x‖ := by rwa [norm_sub_rev]
  have hzxρ : ‖z - x‖ < ρ := by rw [norm_sub_rev]; linarith
  have hG := log_div_le_greenFunction isBounded_ball hρ hsub hzx0 hzxρ
  have hlog : 2 * Real.pi * K < Real.log (ρ / ‖z - x‖) := by
    rw [Real.lt_log_iff_exp_lt (div_pos hρ hzx0), lt_div_iff₀ hzx0, norm_sub_rev]
    calc Real.exp (2 * Real.pi * K) * ‖x - z‖
        < Real.exp (2 * Real.pi * K) * (ρ * Real.exp (-(2 * Real.pi * K))) :=
          mul_lt_mul_of_pos_left hxe (Real.exp_pos _)
      _ = ρ := by rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hpi : 0 < (2 * Real.pi)⁻¹ := inv_pos.2 (by positivity)
  calc K = (2 * Real.pi)⁻¹ * (2 * Real.pi * K) := by field_simp
    _ ≤ (2 * Real.pi)⁻¹ * Real.log (ρ / ‖z - x‖) := mul_le_mul_of_nonneg_left hlog.le hpi.le
    _ ≤ greenFunction (ball 0 1) z x := hG

/-- A volume-growth measure has a common neighborhood of its poles on each
compact subdisc, uniformly above any fixed positive mass. -/
theorem uniform_ball_subset_cluster_of_volumeGrowth {μ : Measure ℂ} {βm βp : ℝ}
    (hμ : IsLocallyFiniteMeasure μ) (hV : VolumeGrowth μ 1 βm βp)
    {b t₀ : ℝ} (hb : b < 1) (ht₀ : 0 < t₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, ‖z‖ ≤ b → ∀ t : ℝ, t₀ ≤ t →
      ball z ε ⊆ cluster μ 1 z t := by
  obtain ⟨M, hM0, hM⟩ := exists_greenPotentialBall_le greenPotentialBallContinuousStep_holds hμ one_pos hV
  obtain ⟨ε, hε, hεb, hG⟩ := exists_uniform_le_greenFunction_near_poles hb ((M + 1) / t₀)
  refine ⟨ε, hε, ?_⟩
  intro z hz t htt x hx
  have hz1 : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (hz.trans_lt hb)
  have ht : 0 < t := ht₀.trans_le htt
  have hx1 : x ∈ ball (0 : ℂ) 1 := mem_ball_zero_of_mem_ball hx (by linarith)
  by_cases hxz : x = z
  · rw [hxz]; exact self_mem_cluster hz1
  apply mem_cluster_of_lt_mul_greenFunction obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ one_pos hV hz1 ht hM hx1
  have hnear : ‖x - z‖ < ε := by simpa only [mem_ball, dist_eq_norm] using hx
  have hbound := hG z hz x (norm_pos_iff.mpr (sub_ne_zero.mpr hxz)) hnear
  have hGpos : 0 ≤ greenFunction (ball 0 1) z x := by
    have : 0 ≤ (M + 1) / t₀ := by positivity
    exact this.trans hbound
  have hmul : M + 1 ≤ t₀ * greenFunction (ball 0 1) z x := by
    have := (div_le_iff₀ ht₀).mp hbound
    linarith
  have := mul_le_mul_of_nonneg_right htt hGpos
  linarith

/-- Almost surely, a common neighborhood works for all poles in any fixed
compact subdisc and all masses above a fixed positive lower bound. -/
theorem ae_uniform_pole_neighborhood_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b t₀ : ℝ, b < 1 → 0 < t₀ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, ‖z‖ ≤ b → ∀ t : ℝ, t₀ ≤ t →
        ball z δ ⊆ cluster (μ ω) 1 z t := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hω
  intro b t₀ hb ht₀
  exact uniform_ball_subset_cluster_of_volumeGrowth hω.1 (hω.2 1 one_pos) hb ht₀

/-- The pole crossing bound is uniform over poles in a compact subdisc and
over nearby crossing centers, for masses above a positive lower bound. -/
theorem ae_uniform_near_pole_crossings_above_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b t₀ : ℝ, b < 1 → 0 < t₀ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∀ z : ℂ, ‖z‖ ≤ b → ∀ w : ℂ, dist w z < δ →
        ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, t₀ ≤ t →
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard ≤ 1 := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_uniform_pole_neighborhood_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα
    Ω P hC hcirc μ hGFF hμ] with ω hω
  intro b t₀ hb ht₀
  obtain ⟨δ, hδ, hδsub⟩ := hω b t₀ hb ht₀
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  have hη : 0 < min (1 : ℝ) (δ / 4) := lt_min (by norm_num) (by positivity)
  filter_upwards [(eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hε hεpos
  change 0 < ε at hεpos
  have hε1 : ε < 1 := hε.trans_le (min_le_left _ _)
  have hεδ : ε < δ / 4 := hε.trans_le (min_le_right _ _)
  have hεsqrt : ε ≤ Real.sqrt ε := by
    have hs := Real.sq_sqrt hεpos.le
    have hn := Real.sqrt_nonneg ε
    nlinarith
  intro z hz w hw
  refine ⟨ε, ⟨le_rfl, hεsqrt⟩, ?_⟩
  intro t htt
  have hsub : ball w (2 * ε) ⊆ cluster (μ ω) 1 z t := by
    apply (ball_subset_ball' ?_).trans (hδsub z hz t htt)
    linarith
  rw [inter_eq_right.mpr hsub]
  exact IsPreconnected.encard_crossingComponents_le_one
    (isConnected_ball (show 0 < 2 * ε by positivity)).isPreconnected w _ _

/-- The localized exact-radius estimate needs no pole-distance condition for
poles in a fixed compact subdisc and masses above a fixed positive threshold.
The radius still carries the boundary-containment condition. -/
theorem ae_localized_crossings_above_mass_without_pole_margin
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b t₀ : ℝ, b < 1 → 0 < t₀ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε),
        ∀ z : ℂ, ‖z‖ ≤ b → ∀ t : ℝ, t₀ ≤ t → dist w 0 + 2 * ρ < 1 →
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_eventually_localized_crossings_exact_radius hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_uniform_pole_neighborhood_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα₀
      Ω P hC hcirc μ hGFF hμ] with ω hcross hpoles
  intro b t₀ hb ht₀
  obtain ⟨δ, hδ, hδsub⟩ := hpoles b t₀ hb ht₀
  have hsmall : 0 < (δ / 4) ^ 2 := sq_pos_of_pos (by positivity)
  filter_upwards [hcross, (eventually_lt_nhds hsmall).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hcross hε hεpos
  change 0 < ε at hεpos
  have hsqrt : Real.sqrt ε < δ / 4 := by
    have hs := Real.sqrt_lt_sqrt hεpos.le hε
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos (show 0 < δ / 4 by positivity)] using hs
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hcross w hw
  have hρpos : 0 < ρ := hεpos.trans_le hρ.1
  refine ⟨ρ, hρ, ?_⟩
  intro z hz t htt hboundary
  by_cases hpole : 2 * ρ < dist z w
  · exact hρbound z (mem_ball_zero_iff.mpr (hz.trans_lt hb)) t (ht₀.trans_le htt) hboundary hpole
  · have hdist : dist w z ≤ 2 * ρ := by simpa [dist_comm] using le_of_not_gt hpole
    have hsub : ball w (2 * ρ) ⊆ cluster (μ ω) 1 z t := by
      apply (ball_subset_ball' ?_).trans (hδsub z hz t htt)
      linarith [hρ.2]
    rw [inter_eq_right.mpr hsub]
    exact (IsPreconnected.encard_crossingComponents_le_one
      (isConnected_ball (show 0 < 2 * ρ by positivity)).isPreconnected w _ _).trans
      (by exact_mod_cast (Nat.ceil_pos.mpr (one_div_pos.mpr hα.1)))

end HarmonicBalls
