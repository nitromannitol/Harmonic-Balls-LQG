import HarmonicBalls.Proofs.Sec5.RegularizedMeasure
import HarmonicBalls.Draft.Section4

/-! # Subharmonic balls and regularization -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Enlarging the domain reduces the class of subharmonic test functions. -/
theorem subharmonicBallTestClass_antitone {A B : Set ℂ} {z : ℂ} (hAB : A ⊆ B) :
    subharmonicBallTestClass B z ⊆ subharmonicBallTestClass A z := by
  intro f hf
  obtain ⟨O, K, ν₁, ν₂, q, hO, hBO, hK, hKO, hf₁, hf₂, hK₁, hK₂, hν, hq, hz, hint, rfl⟩ := hf
  exact ⟨O, K, ν₁, ν₂, q, hO, (closure_mono hAB).trans hBO, hK, hKO, hf₁, hf₂, hK₁, hK₂,
    measure_mono_null hAB hν, hq, hz, hint, rfl⟩

/-- A subharmonic ball remains one after enlargement by a null set, provided
the enlarged set is open. -/
theorem IsSubharmonicBall.of_ae_eq_superset {μ : Measure ℂ} {A B : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) (hB : IsOpen B) (hAB : A ⊆ B) (hAE : A =ᵐ[μ] B) :
    IsSubharmonicBall μ B z := by
  have hmeasure : μ A = μ B := measure_congr hAE
  have hrestrict : μ.restrict A = μ.restrict B := Measure.restrict_congr_set hAE
  refine ⟨hB, hAB hA.2.1, ?_, ?_, ?_⟩
  · rw [← hmeasure]; exact hA.2.2.1
  · rw [← hmeasure]; exact hA.2.2.2.1
  · intro f hf
    have hsub := hA.2.2.2.2 f (subharmonicBallTestClass_antitone hAB hf)
    unfold HasSubMeanValueProperty at hsub ⊢
    constructor
    · simpa only [IntegrableOn, ← hrestrict] using hsub.1
    · simpa only [Measure.real, ← hmeasure, ← hrestrict] using hsub.2

/-- Regularization preserves the subharmonic-ball property when the cluster
boundary has zero measure. -/
theorem isSubharmonicBall_regularizedCluster {μ : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hA : IsSubharmonicBall μ (cluster μ r z t) z)
    (hnull : μ (frontier (cluster μ r z t)) = 0) :
    IsSubharmonicBall μ (regularizedCluster μ r z t) z := by
  have hsub := cluster_subset_regularizedCluster hA.1
  have hmeasure := measure_regularizedCluster_eq hA.1 hnull
  have hAE : cluster μ r z t =ᵐ[μ] regularizedCluster μ r z t :=
    ae_eq_of_subset_of_measure_ge hsub (by rw [hmeasure]) hA.1.measurableSet.nullMeasurableSet
      (by rw [hmeasure]; exact hA.2.2.2.1.ne)
  exact hA.of_ae_eq_superset (isOpen_regularizedCluster μ r z t) hsub hAE

end HarmonicBalls
