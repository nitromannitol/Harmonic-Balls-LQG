import HarmonicBalls.Proofs.Sec5.FinitePunctureAdmissibility
import HarmonicBalls.Proofs.Sec5.UniformPunctureInadmissibility

/-! # Uniform inadmissibility after finite point removal -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Admissibility after deleting a finite set implies admissibility after
deleting any subset of it. -/
theorem finite_puncture_admissible_of_subset
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K L : Finset ℂ)
    (hKL : K ⊆ L) (hL : (L : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (L : Set ℂ)) (ht : 0 < t)
    (hadm : leastSupersolutionOn μ (ball (0 : ℂ) R \ (L : Set ℂ)) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ (L : Set ℂ)) z t) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t := by
  have hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R := fun _ ha => hL (hKL ha)
  have hzK : z ∈ ball (0 : ℂ) R \ (K : Set ℂ) := ⟨hz.1, fun ha => hz.2 (hKL ha)⟩
  apply (leastSupersolutionOn_finset_punctured_disc_mem_iff hμ hR hV K hK hzK ht).mpr
  have hzero := (leastSupersolutionOn_finset_punctured_disc_mem_iff
    hμ hR hV L hL hz ht).mp hadm
  exact fun a ha => hzero a (hKL ha)

/-- Inadmissibility for one puncture persists after deleting any finite set
containing it, provided the pole is retained. -/
theorem finite_puncture_inadmissible_of_singleton
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z a : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R) (ha : a ∈ K)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    (hn : leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t := by
  intro hadm
  apply hn
  have h := finite_puncture_admissible_of_subset hμ hR hV {a} K
    (by simpa using ha) hK hz ht hadm
  simpa using h

/-- With polynomially high probability, every finite deletion containing a
puncture at a fixed separation has an inadmissible infimum at small times. -/
theorem polyHighProb_uniform_finset_punctured_disc_infimum_not_admissible
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    PolyHighProb P (fun T => {ω | ∀ t ∈ Ioc (0 : ℝ) T,
      ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ K : Finset ℂ,
      (K : Set ℂ) ⊆ ball (0 : ℂ) 1 → z ∉ K →
      (∃ a ∈ K, r / 2 ≤ dist a z) →
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ (K : Set ℂ)) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ (K : Set ℂ)) z t}) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hsmall := polyHighProb_uniform_punctured_disc_infimum_not_admissible
    hI2 h71 hγ hγ2 hα hGFF hμ hr
  apply (hsmall.inter_ae hV).mono
  intro T ω hω t ht z hz K hK hzn ⟨a, ha, hdist⟩
  have hzK : z ∈ ball (0 : ℂ) 1 \ (K : Set ℂ) :=
    ⟨ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz, hzn⟩
  exact finite_puncture_inadmissible_of_singleton hω.2.1 zero_lt_one
    (hω.2.2 1 zero_lt_one) K hK ha hzK ht.1 (hω.1 t ht z hz a (hK ha) hdist)

/-- Almost surely the small-time horizon is uniform over all finite deletions
containing a puncture at the specified positive separation. -/
theorem ae_uniform_finset_punctured_disc_infimum_not_admissible
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ K : Finset ℂ,
      (K : Set ℂ) ⊆ ball (0 : ℂ) 1 → z ∉ K →
      (∃ a ∈ K, ε ≤ dist a z) →
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ (K : Set ℂ)) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ (K : Set ℂ)) z t := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_uniform_punctured_disc_infimum_not_admissible
    hI2 h71 hγ hγ2 hα hGFF hμ] with ω hV hsmall
  intro ε hε
  obtain ⟨T, hT, hsmall⟩ := hsmall ε hε
  refine ⟨T, hT, ?_⟩
  intro t ht z hz K hK hzn ⟨a, ha, hdist⟩
  have hzK : z ∈ ball (0 : ℂ) 1 \ (K : Set ℂ) :=
    ⟨ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz, hzn⟩
  exact finite_puncture_inadmissible_of_singleton hV.1 zero_lt_one
    (hV.2 1 zero_lt_one) K hK ha hzK ht.1 (hsmall t ht z hz a (hK ha) hdist)


end HarmonicBalls
