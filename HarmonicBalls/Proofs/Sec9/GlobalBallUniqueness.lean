import HarmonicBalls.Proofs.Sec9.AlmostEverywhereBallUniqueness
import HarmonicBalls.Proofs.Sec9.ScalingAssembly

/-! # Global almost-everywhere uniqueness of subharmonic balls

All-radius boundary nullity extends the local comparison to bounded
subharmonic balls in the whole plane. The scaling inputs used below are
staged and remain pending source review.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- All-radius cluster boundary nullity yields almost-everywhere uniqueness
and null frontiers for bounded equal-mass subharmonic balls. -/
theorem ae_bounded_subharmonicBall_restrict_eq_of_boundaryNull
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hboundary : ClusterBoundaryNullAllRadii.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ), Bornology.IsBounded A → Bornology.IsBounded B →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      μ ω A = μ ω B →
      μ ω (frontier A) = 0 ∧ μ ω (frontier B) = 0 ∧
        μ ω (A \ B) = 0 ∧ μ ω (B \ A) = 0 ∧
        (μ ω).restrict A = (μ ω).restrict B := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_sandwich_of_weak_uniqueness hI2
      (subharmonicBallUniquenessWeak_of_boundaryNull hI2 hboundary)
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hboundary γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
      with ω hcompare hnull hopen
  intro A B z hAb hBb hA hB hmass
  obtain ⟨r, hr⟩ := hAb.closure.subset_ball (0 : ℂ)
  obtain ⟨s, hs⟩ := hBb.closure.subset_ball (0 : ℂ)
  let R := max r s + 1
  have hrR : r ≤ R := by dsimp [R]; linarith [le_max_left r s]
  have hsR : s ≤ R := by dsimp [R]; linarith [le_max_right r s]
  have hAcl : closure A ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball hrR)
  have hBcl : closure B ⊆ ball (0 : ℂ) R := hs.trans (ball_subset_ball hsR)
  have hz : z ∈ ball (0 : ℂ) R := hAcl (subset_closure hA.2.1)
  have hR : 0 < R := pos_of_mem_ball hz
  let t : ℝ := (μ ω A).toReal
  have hfinite : μ ω A ≠ ⊤ := ne_of_lt hA.2.2.2.1
  have ht : 0 < t := ENNReal.toReal_pos hA.2.2.1.ne' hfinite
  have hmassA : μ ω A = ENNReal.ofReal t := (ENNReal.ofReal_toReal hfinite).symm
  have hmassB : μ ω B = ENNReal.ofReal t := hmass.symm.trans hmassA
  obtain ⟨hCA, hAC, _⟩ := hcompare A z t R ht hR hz hAcl hA hmassA
  obtain ⟨hCB, hBC, _⟩ := hcompare B z t R ht hR hz hBcl hB hmassB
  have hCcl : closure (cluster (μ ω) R z t) ⊆ ball 0 R := (closure_mono hCA).trans hAcl
  have hzC := hnull R t hR ht z hz hCcl
  have hsets := frontier_and_sdiff_subset_of_common_closure (hopen t R ht hR z hz).1
    hA.1 hB.1 hCA (hAC.trans interior_subset) hCB (hBC.trans interior_subset)
  have hAB := measure_mono_null hsets.2.2.1 hzC
  have hBA := measure_mono_null hsets.2.2.2 hzC
  exact ⟨measure_mono_null hsets.1 hzC, measure_mono_null hsets.2.1 hzC, hAB, hBA,
    Measure.restrict_congr_set (ae_eq_set.mpr ⟨hAB, hBA⟩)⟩

/-- The global comparison from I2, the typical-scale estimate, and the staged
affine-invariance and coordinate-change inputs. -/
theorem ae_bounded_subharmonicBall_restrict_eq_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ), Bornology.IsBounded A → Bornology.IsBounded B →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      μ ω A = μ ω B →
      μ ω (frontier A) = 0 ∧ μ ω (frontier B) = 0 ∧
        μ ω (A \ B) = 0 ∧ μ ω (B \ A) = 0 ∧
        (μ ω).restrict A = (μ ω).restrict B := by
  let h8 := boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2)
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure hI2
      (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2)) h82
  exact ae_bounded_subharmonicBall_restrict_eq_of_boundaryNull hI2
    (clusterBoundaryNullAllRadii_of_integerRadii hI2
      (clusterBoundaryNullIntegerRadii_of_scaledField h8 clusterPathwiseScaleStep_proved hAff hCC))

end HarmonicBalls
