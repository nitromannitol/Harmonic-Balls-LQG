import HarmonicBalls.Proofs.Sec5.PuncturedDiscCompetitors
import HarmonicBalls.Proofs.Sec5.PuncturedDiscSmallTime

/-! # Inadmissibility at a puncture

A puncture outside the disc cluster makes the pointwise infimum fail the
continuity required of a general-domain supersolution.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- A removed point outside the disc cluster forces inadmissibility, for a
locally finite measure satisfying the disc volume growth condition. -/
theorem punctured_disc_infimum_not_admissible_of_not_mem_cluster
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 < t) (hn : a ∉ cluster μ R z t) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  have hza : z ≠ a := by simpa using hz.2
  have hG := greenFunction_ball_pos hz.1 ha hza
  have heq := odometer_eq_zero_of_notMem_cluster (le_of_lt ht) ha hn
  have hneg : leastSupersolution μ R z t a < 0 := by
    change leastSupersolution μ R z t a + t * greenFunction (ball 0 R) z a = 0 at heq
    nlinarith
  exact leastSupersolutionOn_punctured_disc_not_mem_of_negative ha hz (le_of_lt ht) hw hneg

/-- The punctured-disc cluster is contained in the disc cluster, without an
admissibility hypothesis for the punctured-domain infimum. -/
theorem clusterOn_punctured_disc_subset_cluster
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 < t) : clusterOn μ (ball (0 : ℂ) R \ {a}) z t ⊆ cluster μ R z t := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  intro x hx
  refine ⟨hx.1.1, ?_⟩
  rcases hx.2 with h | h
  · exact Or.inl h
  · by_cases hxz : x = z
    · exact Or.inl hxz
    · right
      have hle := leastSupersolutionOn_punctured_disc_le_supersolution ha hz hw hx.1 hxz
      rw [greenFunction_punctured_ball ha hz hx.1 hxz] at h
      linarith

/-- Assuming I2 and Proposition 7.1, almost surely the pointwise infimum for
the unit disc punctured at `1/2` is inadmissible throughout a positive time
interval. -/
theorem ae_small_time_punctured_disc_infimum_not_admissible
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧ ∀ t ∈ Ioc (0 : ℝ) T,
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hsmall := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ (1 / 2) (by norm_num)
  filter_upwards [hV, hsmall.ae_eventually_dyadic] with ω hV hsmall
  obtain ⟨n, hn⟩ := hsmall.exists
  refine ⟨(2 : ℝ)⁻¹ ^ n, by positivity, fun t ht => ?_⟩
  have ha : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by norm_num [mem_ball_zero_iff]
  have hz : (0 : ℂ) ∈ ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)} := by norm_num [mem_ball_zero_iff]
  have hbound := hn t ht 0 (by norm_num : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2))
  have hnot : (1 / 2 : ℂ) ∉ cluster (μ ω) 1 0 t := by
    intro ha'
    have hs := hbound (subset_closure ha')
    norm_num [mem_ball_zero_iff] at hs
  exact punctured_disc_infimum_not_admissible_of_not_mem_cluster hV.1 zero_lt_one
    (hV.2 1 zero_lt_one) ha hz ht.1 hnot

#print axioms punctured_disc_infimum_not_admissible_of_not_mem_cluster
#print axioms clusterOn_punctured_disc_subset_cluster
#print axioms ae_small_time_punctured_disc_infimum_not_admissible

end HarmonicBalls
