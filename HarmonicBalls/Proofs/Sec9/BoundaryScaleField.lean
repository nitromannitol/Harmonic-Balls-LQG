import HarmonicBalls.Proofs.Sec9.BoundaryScaling
import HarmonicBalls.Proofs.Sec5.ScalingMeasure

/-!
# Boundary nullity from the rescaled field

Proposition 8.1 applies directly to the normalized rescaled field. This avoids
requiring measurability of the event quantified over all centres and masses.
The affine invariance and coordinate change assumptions below are staged in
`HarmonicBalls.Proposed.LQG` and remain pending source review.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Boundary nullity at all positive integer radii from the unit-disc theorem,
the simultaneous pathwise scaling identity, and the staged affine invariance
and LQG coordinate-change inputs. -/
theorem clusterBoundaryNullIntegerRadii_of_scaledField
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hscale : ClusterPathwiseScaleStep.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ClusterBoundaryNullIntegerRadii.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  rw [ae_all_iff]
  intro n
  by_cases hn : 0 < n
  · have hk : 0 < (n : ℝ) := by exact_mod_cast hn
    let hC' := affinePairing hC hcirc (n : ℂ) 0
    let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
      hcirc ω ((n : ℝ) * r) ((n : ℝ) • z) - hcirc ω n 0
    have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
      have hcirc_eq : hcirc' = affineCircle hcirc (n : ℂ) 0 := by
        funext ω r z
        simp [hcirc', affineCircle, Complex.real_smul]
      rw [hcirc_eq]
      exact hAff Ω P hC hcirc hGFF (n : ℂ) (by exact_mod_cast hn.ne') 0
    have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
        (fun ω => normalizedPullbackMeasure γ α₀ n (hcirc ω) (μ ω)) := by
      exact isLQGMeasureOfField_normalizedPullback (hCC Ω P γ α₀ hC hcirc)
        hGFF hγ hγ2 hα hμ hk
    have hunit := h8 γ α₀ hγ hγ2 hα Ω P hC' hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ n (hcirc ω) (μ ω)) hGFF' hμ'
    filter_upwards [hunit, hscale γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ n hk] with ω hu hs _
    exact clusterBoundaryNull_of_normalized_scale γ α₀ n hk (hcirc ω) (μ ω) hu hs
  · exact Filter.Eventually.of_forall fun _ h => (hn h).elim

/-- Weak Proposition 9.2 from Proposition 8.1, pathwise cluster scaling,
volume growth, and two staged affine-field inputs. -/
theorem subharmonicBallUniquenessWeak_of_scaledField
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hscale : ClusterPathwiseScaleStep.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_integerRadii hI2
    (clusterBoundaryNullIntegerRadii_of_scaledField h8 hscale hAff hCC)

end HarmonicBalls
