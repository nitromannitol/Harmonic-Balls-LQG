import HarmonicBalls.Proofs.Sec10.JordanIntegerRadii
import HarmonicBalls.Proofs.Sec9.BoundaryScaleField

/-!
# Rescaling complementary Jordan boundaries

The simultaneous unit-disc event transfers to any fixed radius by the
pathwise cluster scaling identity. The field invariance and coordinate
change assumptions are staged inputs pending source review.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped Pointwise

universe u

/-- A homeomorphism transports complementary components with Jordan boundary. -/
theorem jordan_complement_components_image (e : ℂ ≃ₜ ℂ) (K : Set ℂ)
    (h : ∀ C ∈ connectedComponentsIn Kᶜ, IsSimpleLoop (frontier C)) :
    ∀ C ∈ connectedComponentsIn (e '' K)ᶜ, IsSimpleLoop (frontier C) := by
  intro C hC
  obtain ⟨x, hx, rfl⟩ := hC
  let y := e.symm x
  have hy : y ∈ Kᶜ := by
    intro hyK
    apply hx
    exact ⟨y, hyK, e.apply_symm_apply x⟩
  have heq : e '' connectedComponentIn Kᶜ y =
      connectedComponentIn (e '' K)ᶜ x := by
    rw [e.image_connectedComponentIn hy, e.image_compl]
    simp [y]
  have hj := (h (connectedComponentIn Kᶜ y) ⟨y, hy, rfl⟩).image e.continuous e.injective
  rwa [e.image_frontier, heq] at hj

/-- The unit-disc Jordan event transfers to radius `k` under simultaneous
pathwise scaling. -/
theorem clusterJordan_of_normalized_scale
    (γ α₀ k : ℝ) (hk : 0 < k) (hcirc : ℝ → ℂ → ℝ) (μ : Measure ℂ)
    (hunit : ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t) ⊆ ball 0 1 →
      ∀ C ∈ connectedComponentsIn (closure (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t))ᶜ,
        IsSimpleLoop (frontier C))
    (hscale : ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1 z t =
        k⁻¹ • cluster μ k (k • z)
          (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0)) * t)) :
    ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) k,
      closure (cluster μ k z t) ⊆ ball 0 k →
      ∀ C ∈ connectedComponentsIn (closure (cluster μ k z t))ᶜ,
        IsSimpleLoop (frontier C) := by
  intro t ht z hz hcl
  let A : ℝ := Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ hcirc k 0))
  have hA : 0 < A := Real.exp_pos _
  have hball : (k⁻¹ : ℝ) • ball (0 : ℂ) k = ball 0 1 := by
    rw [_root_.smul_ball (inv_ne_zero hk.ne')]
    simp [Real.norm_eq_abs, abs_of_pos hk, hk.ne']
  have hz' : k⁻¹ • z ∈ ball (0 : ℂ) 1 := by
    rw [← hball]
    exact smul_mem_smul_set hz
  have hzscale : k • (k⁻¹ • z) = z := by simp [hk.ne']
  have htscale : A * (t / A) = t := by field_simp
  have heq := hscale (k⁻¹ • z) hz' (t / A) (div_pos ht hA)
  rw [hzscale, htscale] at heq
  have hcl' : closure (cluster (normalizedPullbackMeasure γ α₀ k hcirc μ) 1
      (k⁻¹ • z) (t / A)) ⊆ ball 0 1 := by
    rw [heq, closure_smul₀' (inv_ne_zero hk.ne'), ← hball]
    exact smul_set_mono hcl
  have hj := hunit (t / A) (div_pos ht hA) (k⁻¹ • z) hz' hcl'
  rw [heq, closure_smul₀' (inv_ne_zero hk.ne')] at hj
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  have himage : e '' (k⁻¹ • closure (cluster μ k z t)) = closure (cluster μ k z t) := by
    change k • (k⁻¹ • closure (cluster μ k z t)) = _
    rw [smul_smul, mul_inv_cancel₀ hk.ne', one_smul]
  have h := jordan_complement_components_image e _ hj
  rwa [himage] at h

/-- Proposition 10.6 at unit radius implies the fixed-radius form, given
pathwise scaling and the staged affine invariance and coordinate change. -/
theorem clusterJordanFixedRadius_of_scaledField
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u})
    (hscale : ClusterPathwiseScaleStep.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ClusterJordanFixedRadius.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ k hk
  let hC' := affinePairing hC hcirc (k : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (k * r) (k • z) - hcirc ω k 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (k : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul, abs_of_pos hk]
    rw [hcirc_eq]
    exact hAff Ω P hC hcirc hGFF (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) := by
    exact isLQGMeasureOfField_normalizedPullback (hCC Ω P γ α₀ hC hcirc)
      hGFF hγ hγ2 hα hμ hk
  have hunit := h10 γ α₀ hγ hγ2 hα Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) hGFF' hμ'
  filter_upwards [hunit, hscale γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ k hk] with ω hu hs
  exact clusterJordan_of_normalized_scale γ α₀ k hk (hcirc ω) (μ ω) hu hs

/-- Proposition 10.7 follows from the unit-disc Jordan theorem, existence,
volume growth and the explicit scaling inputs. -/
theorem harmonicBallComplementBoundaryJordan_of_scaledField
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexists : ExistenceHarmonicBallsStmt.{u})
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u})
    (hscale : ClusterPathwiseScaleStep.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  harmonicBallComplementBoundaryJordan_of_fixedRadius hI2 hexists
    (clusterJordanFixedRadius_of_scaledField h10 hscale hAff hCC)

end HarmonicBalls
