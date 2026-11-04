import HarmonicBalls.Proofs.Sec9.LQGSpatialDilation
import HarmonicBalls.Proofs.Sec9.GlobalBallUniqueness
import HarmonicBalls.Proofs.Sec9.MassSymmetricDifference

/-!
# Global subharmonic-ball comparison using dyadic scaling

The dyadic coordinate change follows from the approximation definition, so
only whole-plane GFF affine invariance remains as a staged scaling input.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped symmDiff

universe u

/-- Weak Proposition 9.2 from volume growth, Lemmas 6.11 and 8.2, and staged
GFF affine invariance. -/
theorem subharmonicBallUniquenessWeak_of_dyadic_typical_scales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_dyadic_affine hI2
    (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2) h611 h82)
    hAff

/-- The same conclusion with Lemma 6.11 supplied by the Section 6
volume-growth and Brownian-comparison assembly. -/
theorem subharmonicBallUniquenessWeak_of_dyadic_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_dyadic_typical_scales hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_harmonicMeasure hI2
      (Section6.odometerHarmonicMeasureBoundStmt_of_volumeGrowth hI2)) h82 hAff

/-- All-radius boundary nullity from the same inputs, with no LQG
coordinate-change hypothesis. -/
theorem clusterBoundaryNullAllRadii_of_dyadic_typical_scales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc) :
    ClusterBoundaryNullAllRadii.{u} := by
  apply clusterBoundaryNullAllRadii_of_cofinalRadii hI2 (fun n => (2 : ℝ) ^ n)
  · intro n
    exact pow_pos (by norm_num) n
  · intro R
    have ht := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_gt_atTop R
    obtain ⟨n, hn⟩ := ht.exists
    exact ⟨n, hn.le⟩
  · exact clusterBoundaryNullDyadicRadii_of_affine
      (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2) h611 h82)
      hAff

/-- Bounded equal-mass subharmonic balls at the same centre have null
frontiers and equal restricted measures, simultaneously almost surely. -/
theorem ae_bounded_subharmonicBall_restrict_eq_of_dyadic_typical_scales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ), Bornology.IsBounded A → Bornology.IsBounded B →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      μ ω A = μ ω B →
      μ ω (frontier A) = 0 ∧ μ ω (frontier B) = 0 ∧
        μ ω (A \ B) = 0 ∧ μ ω (B \ A) = 0 ∧
        (μ ω).restrict A = (μ ω).restrict B :=
  ae_bounded_subharmonicBall_restrict_eq_of_boundaryNull hI2
    (clusterBoundaryNullAllRadii_of_dyadic_typical_scales hI2 h611 h82 hAff)

/-- Mass distance between any two bounded same-centre subharmonic balls,
without an LQG coordinate-change input. -/
theorem ae_bounded_subharmonicBall_symmDiff_mass_of_dyadic_typical_scales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ), Bornology.IsBounded A → Bornology.IsBounded B →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      μ ω (A ∆ B) = (μ ω A - μ ω B) + (μ ω B - μ ω A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_order_of_weak_uniqueness hI2
      (subharmonicBallUniquenessWeak_of_dyadic_typical_scales hI2 h611 h82 hAff)
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_bounded_subharmonicBall_restrict_eq_of_dyadic_typical_scales hI2 h611 h82 hAff
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder hfront
  intro A B z hAb hBb hA hB
  have hnull : ∀ (D E : Set ℂ), Bornology.IsBounded D → Bornology.IsBounded E →
      IsSubharmonicBall (μ ω) D z → IsSubharmonicBall (μ ω) E z → μ ω D ≤ μ ω E →
      μ ω (D \ E) = 0 := by
    intro D E hDb hEb hD hE hmass
    have hDE := (horder D E z hDb hEb hD hE hmass).1
    have hzero := (hfront E E z hEb hEb hE hE rfl).1
    apply measure_mono_null _ hzero
    rw [hE.1.frontier_eq]
    intro x hx
    exact ⟨interior_subset (hDE hx.1), hx.2⟩
  rcases le_total (μ ω A) (μ ω B) with hmass | hmass
  · have hdiff := measure_symmDiff_of_ae_subset (μ ω) hA.1.measurableSet
      hB.1.measurableSet (ne_of_lt hA.2.2.2.1) (hnull A B hAb hBb hA hB hmass)
    simpa only [tsub_eq_zero_of_le hmass, zero_add] using hdiff
  · have hdiff := measure_symmDiff_of_ae_subset (μ ω) hB.1.measurableSet
      hA.1.measurableSet (ne_of_lt hB.2.2.2.1) (hnull B A hBb hAb hB hA hmass)
    rw [symmDiff_comm] at hdiff
    simpa only [tsub_eq_zero_of_le hmass, add_zero] using hdiff

end HarmonicBalls
