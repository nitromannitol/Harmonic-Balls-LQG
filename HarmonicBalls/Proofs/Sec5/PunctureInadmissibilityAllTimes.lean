import HarmonicBalls.Proofs.Sec5.UniformPunctureInadmissibility
import HarmonicBalls.Proofs.Sec5.LocallyFinitePunctureAdmissibility

/-! # Persistence of puncture inadmissibility

The disc least supersolution decreases as the mass parameter increases.
Therefore a negative value at a deleted point persists at all later times.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- At points away from the pole, the least supersolution decreases with time. -/
theorem leastSupersolution_antitone_time
    {μ : Measure ℂ} {R s t : ℝ} {z x : ℂ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    leastSupersolution μ R z t x ≤ leastSupersolution μ R z s x := by
  have hsubset : supersolutions μ R z s ⊆ supersolutions μ R z t := by
    intro w hw
    refine ⟨hw.1, hw.2.1, ?_⟩
    intro y hy hyz
    have hg := greenFunction_nonneg (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) R)) z y
    have hw' := hw.2.2 y hy hyz
    nlinarith
  apply le_csInf ((supersolutions_nonempty μ R z hs).image _)
  rintro _ ⟨w, hw, rfl⟩
  exact leastSupersolution_le (hsubset hw) hx hxz

/-- Inadmissibility after locally finite deletion persists at later positive times. -/
theorem locally_finite_puncture_inadmissible_mono_time
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp s t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    (hKR : K ⊆ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ K)
    (hs : 0 < s) (hst : s ≤ t)
    (hn : leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z s ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z s) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t := by
  intro hadm
  have ht : 0 < t := hs.trans_le hst
  have hzero := (leastSupersolutionOn_locally_finite_punctured_disc_mem_iff
    hμ hR hV K hK hKR hz ht).mp hadm
  apply hn
  apply (leastSupersolutionOn_locally_finite_punctured_disc_mem_iff
    hμ hR hV K hK hKR hz hs).mpr
  intro a ha
  have haz : a ≠ z := fun h => hz.2 (h ▸ ha)
  have haR := ball_subset_closedBall (hKR ha)
  have hle := leastSupersolution_antitone_time (μ := μ) hs.le hst haR haz
  have hnonpos := leastSupersolution_nonpos (μ := μ) hs.le haR haz
  rw [hzero a ha] at hle
  exact le_antisymm hnonpos hle

/-- Assuming I2 and Proposition 7.1, for every centre in the half disc, every
nonempty locally finite deletion excluding the centre has an inadmissible
pointwise infimum at every positive time, almost surely. -/
theorem ae_locally_finite_puncture_inadmissible_all_times
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ K : Set ℂ,
      K ⊆ ball (0 : ℂ) 1 → K.Nonempty →
      (∀ ρ : ℝ, ρ < 1 → (K ∩ closedBall (0 : ℂ) ρ).Finite) → z ∉ K →
      ∀ t : ℝ, 0 < t →
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ K) z t := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_uniform_punctured_disc_infimum_not_admissible
    hI2 h71 hγ hγ2 hα hGFF hμ] with ω hvol hsmall
  intro z hz K hKR hKne hKloc hzK t ht hadm
  obtain ⟨a, ha⟩ := hKne
  have haz : a ≠ z := fun h => hzK (h ▸ ha)
  have hdist : 0 < dist a z := dist_pos.mpr haz
  obtain ⟨T, hT, hbound⟩ := hsmall (dist a z) hdist
  let s : ℝ := min T t / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hsT : s ≤ T := by dsimp [s]; have := min_le_left T t; linarith
  have hst : s ≤ t := by dsimp [s]; have := min_le_right T t; linarith
  have hsnot := hbound s ⟨hs, hsT⟩ z hz a (hKR ha) le_rfl
  have hzsingle : z ∈ ball (0 : ℂ) 1 \ {a} :=
    ⟨ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz, by simpa using haz.symm⟩
  have hzero := (leastSupersolutionOn_locally_finite_punctured_disc_mem_iff
    hvol.1 zero_lt_one (hvol.2 1 zero_lt_one) K hKloc hKR ⟨hzsingle.1, hzK⟩ ht).mp hadm a ha
  have hle := leastSupersolution_antitone_time (μ := μ ω) hs.le hst (ball_subset_closedBall (hKR ha)) haz
  have hnpos := leastSupersolution_nonpos (μ := μ ω) hs.le (ball_subset_closedBall (hKR ha)) haz
  have hsEq : leastSupersolution (μ ω) 1 z s a = 0 := by linarith
  apply hsnot
  have hfin := (leastSupersolutionOn_finset_punctured_disc_mem_iff hvol.1 zero_lt_one
    (hvol.2 1 zero_lt_one) {a} (by simpa using hKR ha) (by simpa using hzsingle) hs).mpr
      (by simpa using hsEq)
  simpa using hfin

/-- The full-disc least supersolution is strictly negative at every point
other than the pole, simultaneously for all positive times and half-disc centres. -/
theorem ae_leastSupersolution_lt_zero_all_times
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ a ∈ ball (0 : ℂ) 1,
      a ≠ z → ∀ t : ℝ, 0 < t → leastSupersolution (μ ω) 1 z t a < 0 := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_locally_finite_puncture_inadmissible_all_times
    hI2 h71 hγ hγ2 hα hGFF hμ] with ω hvol hall
  intro z hz a ha haz t ht
  have hzU : z ∈ ball (0 : ℂ) 1 \ ({a} : Set ℂ) :=
    ⟨ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz, by simpa using haz.symm⟩
  have hnot := hall z hz {a} (by simpa using ha) (by simp)
    (fun ρ hρ => (Set.finite_singleton a).inter_of_left _) (by simpa using haz.symm) t ht
  have hnonpos := leastSupersolution_nonpos (μ := μ ω) ht.le (ball_subset_closedBall ha) haz
  apply lt_of_le_of_ne hnonpos
  intro heq
  apply hnot
  apply (leastSupersolutionOn_locally_finite_punctured_disc_mem_iff hvol.1 zero_lt_one
    (hvol.2 1 zero_lt_one) {a} (fun ρ hρ => (Set.finite_singleton a).inter_of_left _)
    (by simpa using ha) hzU ht).mpr
  simpa using heq

/-- At every deleted point, the locally finitely punctured-disc infimum is
strictly discontinuous along the punctured disc at every positive time. -/
theorem ae_locally_finite_puncture_discontinuous_all_times
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ K : Set ℂ,
      K ⊆ ball (0 : ℂ) 1 →
      (∀ ρ : ℝ, ρ < 1 → (K ∩ closedBall (0 : ℂ) ρ).Finite) → z ∉ K →
      ∀ a ∈ K, ∀ t : ℝ, 0 < t →
        ¬ ContinuousWithinAt (leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t)
          (ball (0 : ℂ) 1 \ K) a := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_leastSupersolution_lt_zero_all_times
    hI2 h71 hγ hγ2 hα hGFF hμ] with ω hvol hneg
  intro z hz K hKR hKloc hzK a ha t ht hc
  have haz : a ≠ z := fun h => hzK (h ▸ ha)
  have hzU : z ∈ ball (0 : ℂ) 1 \ K :=
    ⟨ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz, hzK⟩
  have heq := (continuousWithinAt_locally_finite_punctured_infimum_iff hvol.1 zero_lt_one
    (hvol.2 1 zero_lt_one) K hKloc hKR ha hzU ht).mp hc
  exact (ne_of_lt (hneg z hz a (hKR ha) haz t ht)) heq

end HarmonicBalls
