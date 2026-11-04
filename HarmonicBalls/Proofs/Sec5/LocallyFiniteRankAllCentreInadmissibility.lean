import HarmonicBalls.Proofs.Sec5.LocallyFiniteRankInteriorAdmissibility
import HarmonicBalls.Proofs.Sec5.AllCentrePunctureInadmissibility

/-! # Accumulating deletions at all centres

The field invariance and coordinate-change inputs are staged and explicit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Almost surely, each deleted point is a discontinuity of the infimum,
for every centre and positive time, including locally finite accumulation rank. -/
theorem ae_locallyFiniteRankOn_puncture_discontinuous_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ K : Set ℂ,
      IsClosed K →
      LocallyFiniteRankOn (ball (0 : ℂ) 1) K →
      z ∉ K → ∀ a ∈ K, a ∈ ball (0 : ℂ) 1 → ∀ t : ℝ, 0 < t →
        ¬ ContinuousWithinAt (leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t)
          (ball (0 : ℂ) 1 \ K) a := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_leastSupersolution_lt_zero_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ] with ω hvol hneg
  intro z hz K hKclosed hK hzK a ha haR t ht hc
  have haz : a ≠ z := fun h => hzK (h ▸ ha)
  have heq := (continuousWithinAt_locallyFiniteRankOn_punctured_infimum_at_interior_iff hvol.1 zero_lt_one
    (hvol.2 1 zero_lt_one) K hKclosed hK haR ha ⟨hz, hzK⟩ ht).mp hc
  exact (ne_of_lt (hneg z hz a haR haz t ht)) heq

/-- Almost surely every deletion with locally finite accumulation rank and an interior point
has an inadmissible infimum, at every centre and positive time. -/
theorem ae_locallyFiniteRankOn_puncture_inadmissible_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ K : Set ℂ,
      (K ∩ ball (0 : ℂ) 1).Nonempty → IsClosed K →
      LocallyFiniteRankOn (ball (0 : ℂ) 1) K →
      z ∉ K → ∀ t : ℝ, 0 < t →
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ K) z t := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_leastSupersolution_lt_zero_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ] with ω hvol hneg
  intro z hz K hne hKclosed hK hzK t ht hadm
  obtain ⟨a, ha, haR⟩ := hne
  have haz : a ≠ z := fun h => hzK (h ▸ ha)
  exact (not_mem_supersolutionsOn_of_locallyFiniteRankOn_interior_puncture hvol.1 zero_lt_one
    (hvol.2 1 zero_lt_one) K hKclosed hK haR ha ⟨hz, hzK⟩ ht
    (ne_of_lt (hneg z hz a haR haz t ht))) hadm

#print axioms ae_locallyFiniteRankOn_puncture_discontinuous_all_centres
#print axioms ae_locallyFiniteRankOn_puncture_inadmissible_all_centres

end HarmonicBalls
