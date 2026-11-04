import HarmonicBalls.Proofs.Sec5.UniformLateTimeMass
import HarmonicBalls.Proofs.Sec10.ExteriorComponent

/-! # Late-time bounded holes

Compact exhaustion controls the total mass and the inradius of bounded
complementary components at late times, uniformly over compact pole sets.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- A bounded complementary component of a closed set in the closed unit
disc lies in the open unit disc. -/
theorem bounded_complement_component_subset_unit_ball
    {K U : Set ℂ} (hKclosed : IsClosed K) (hK : K ⊆ closedBall 0 1)
    (hU : U ∈ connectedComponentsIn Kᶜ) (hUb : Bornology.IsBounded U) :
    U ⊆ ball (0 : ℂ) 1 := by
  have hp2 : (2 : ℂ) ∈ (closedBall (0 : ℂ) 1)ᶜ := by
    norm_num [mem_closedBall, dist_eq_norm]
  have hne : U ≠ connectedComponentIn Kᶜ (2 : ℂ) := by
    intro heq
    exact not_isBounded_exterior_component zero_lt_one hK hp2 (heq ▸ hUb)
  have hclosed := component_compl_subset_closedBall_of_ne_exterior zero_lt_one hK hp2 hU hne
  obtain ⟨x, hx, hxeq⟩ := hU
  have hopen : IsOpen U := by
    rw [← hxeq]
    exact hKclosed.isOpen_compl.connectedComponentIn
  have h := hopen.subset_interior_iff.mpr hclosed
  rwa [interior_closedBall (0 : ℂ) one_ne_zero] at h

universe u

/-- The union of all bounded holes has arbitrarily small LQG mass at late
times, uniformly over poles in a fixed compact subset of the unit disc. -/
theorem ae_uniform_late_time_bounded_hole_mass
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 1 →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t →
        μ ω (⋃₀ {U | U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧
          Bornology.IsBounded U}) < ε := by
  filter_upwards [ae_uniform_centre_late_time_cluster_mass hI2 hγ hγ2 hα hGFF hμ]
    with ω hlate
  intro K hK hKsub ε hε
  obtain ⟨T, hT, hTmass⟩ := hlate 1 zero_lt_one K hK hKsub ε hε
  refine ⟨T, hT, ?_⟩
  intro z hz t ht
  apply (measure_mono ?_).trans_lt (hTmass z hz t ht).1
  intro x hx
  obtain ⟨U, ⟨hU, hUb⟩, hxU⟩ := mem_sUnion.mp hx
  have hcl : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  refine ⟨bounded_complement_component_subset_unit_ball isClosed_closure hcl hU hUb hxU, ?_⟩
  obtain ⟨p, hp, rfl⟩ := hU
  exact fun hxC => (connectedComponentIn_subset _ _ hxU) (subset_closure hxC)

/-- For every fixed positive radius, eventually no bounded hole contains
a ball of that radius, uniformly over any compact set of poles in the disc. -/
theorem ae_uniform_late_time_bounded_hole_inradius
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 1 →
      ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t →
        ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
          Bornology.IsBounded U → ∀ p : ℂ, ¬ ball p r ⊆ U := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_uniform_late_time_bounded_hole_mass hI2 hγ hγ2 hα hGFF hμ]
    with ω hV hlate
  have hV1 := hV.2 1 zero_lt_one
  obtain ⟨r₀, hr₀, hvol⟩ := hV1.2.2
  intro r hr K hK hKsub
  let ρ := min (r / 2) (r₀ / 2)
  have hρ : 0 < ρ := lt_min (half_pos hr) (half_pos hr₀)
  have hρr : ρ ≤ r := (min_le_left _ _).trans (half_le_self hr.le)
  have hρr₀ : ρ < r₀ := (min_le_right _ _).trans_lt (half_lt_self hr₀)
  have hε : 0 < ENNReal.ofReal (ρ ^ βm) := ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ βm)
  obtain ⟨T, hT, hsmall⟩ := hlate K hK hKsub (ENNReal.ofReal (ρ ^ βm)) hε
  refine ⟨T, hT, ?_⟩
  intro z hz t ht U hU hUb p hball
  have hpU : p ∈ U := hball (mem_ball_self hr)
  have hcl : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hp : p ∈ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure hcl hU hUb hpU
  have hsub : ball p ρ ⊆ ⋃₀ {U | U ∈
      connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ ∧ Bornology.IsBounded U} := by
    intro x hx
    exact mem_sUnion.mpr ⟨U, ⟨hU, hUb⟩, hball (ball_subset_ball hρr hx)⟩
  have hlower := (hvol ρ hρ hρr₀ p hp).1
  exact (not_lt_of_ge (hlower.trans (measure_mono hsub))) (hsmall z hz t ht)

end HarmonicBalls
