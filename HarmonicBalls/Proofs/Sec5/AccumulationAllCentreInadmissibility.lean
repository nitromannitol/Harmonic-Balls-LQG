import HarmonicBalls.Proofs.Sec5.AccumulationPunctureAdmissibility
import HarmonicBalls.Proofs.Sec5.AllCentrePunctureInadmissibility

/-! # Accumulating deletions at all centres

The field invariance and coordinate-change inputs are staged and explicit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Almost surely, each deleted point is a discontinuity of the infimum,
for every centre and positive time, including locally finite accumulation. -/
theorem ae_accumulating_puncture_discontinuous_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ K L : Set ℂ,
      K ⊆ ball (0 : ℂ) 1 → IsClosed K → IsClosed L →
      (∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) 1 → (L ∩ C).Finite) →
      (∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) 1 \ L → (K ∩ C).Finite) →
      z ∉ K → ∀ a ∈ K, ∀ t : ℝ, 0 < t →
        ¬ ContinuousWithinAt (leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t)
          (ball (0 : ℂ) 1 \ K) a := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_leastSupersolution_lt_zero_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ] with ω hvol hneg
  intro z hz K L hKR hKclosed hLclosed hL hK hzK a ha t ht hc
  have haz : a ≠ z := fun h => hzK (h ▸ ha)
  have heq := (continuousWithinAt_accumulating_punctured_infimum_iff hvol.1 zero_lt_one
    (hvol.2 1 zero_lt_one) K hKclosed hLclosed hL hK hKR ha ⟨hz, hzK⟩ ht).mp hc
  exact (ne_of_lt (hneg z hz a (hKR ha) haz t ht)) heq

/-- Almost surely every nonempty deletion with locally finite accumulation
has an inadmissible infimum, at every centre and positive time. -/
theorem ae_accumulating_puncture_inadmissible_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ K L : Set ℂ,
      K ⊆ ball (0 : ℂ) 1 → K.Nonempty → IsClosed K → IsClosed L →
      (∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) 1 → (L ∩ C).Finite) →
      (∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) 1 \ L → (K ∩ C).Finite) →
      z ∉ K → ∀ t : ℝ, 0 < t →
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ K) z t := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_leastSupersolution_lt_zero_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ] with ω hvol hneg
  intro z hz K L hKR hne hKclosed hLclosed hL hK hzK t ht hadm
  obtain ⟨a, ha⟩ := hne
  have haz : a ≠ z := fun h => hzK (h ▸ ha)
  have heq := (leastSupersolutionOn_accumulating_punctured_disc_mem_iff hvol.1 zero_lt_one
    (hvol.2 1 zero_lt_one) K hKclosed hLclosed hL hK hKR ⟨hz, hzK⟩ ht).mp hadm a ha
  exact (ne_of_lt (hneg z hz a (hKR ha) haz t ht)) heq


end HarmonicBalls
