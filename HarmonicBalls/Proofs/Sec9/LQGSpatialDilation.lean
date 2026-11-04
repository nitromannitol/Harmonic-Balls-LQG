import HarmonicBalls.Proofs.Sec9.DyadicApproximationShift
import HarmonicBalls.Proofs.Sec6.WeakerSingularityExistence
import HarmonicBalls.Proofs.Sec5.ScalingMeasure
import HarmonicBalls.Proofs.Sec5.SupersolutionScaling
import HarmonicBalls.Proofs.Sec9.CofinalBoundaryRadii
import HarmonicBalls.Proofs.Sec9.BoundaryScaleField
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Spatial dilation of LQG approximation limits

A planar dilation of the spatial argument in a circle-average family pulls
back the limiting measure and introduces the two-dimensional Jacobian.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped Topology

universe u

/-- Spatial dilation of a deterministic LQG limit. Continuity is needed only
at the dyadic approximation radii. -/
theorem IsLQGLimit.spatial_dilation {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    {μ : Measure ℂ} (hμ : IsLQGLimit γ hε μ)
    (hc : ∀ n, Continuous (hε (dyadicScale n))) {k : ℝ} (hk : 0 < k) :
    IsLQGLimit γ (fun r z => hε r (k • z))
      (ENNReal.ofReal (k⁻¹ ^ 2) • μ.map (fun z : ℂ => k⁻¹ • z)) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k⁻¹ (inv_ne_zero hk.ne')
  let : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  let : IsFiniteMeasureOnCompacts (μ.map e) := Measure.IsFiniteMeasureOnCompacts.map μ e
  let : IsFiniteMeasureOnCompacts (ENNReal.ofReal (k⁻¹ ^ 2) • μ.map e) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  refine ⟨?_, fun φ hφ hφc => ?_⟩
  · change IsLocallyFiniteMeasure (ENNReal.ofReal (k⁻¹ ^ 2) • μ.map e)
    infer_instance
  · let ψ : ℂ → ℝ := fun z => φ (k⁻¹ • z)
    have hψ : Continuous ψ := hφ.comp (continuous_const_smul _)
    have hψc : HasCompactSupport ψ := by
      exact hφc.comp_homeomorph e
    have hlim := (hμ.tendsto_integral ψ hψ hψc).const_mul (k⁻¹ ^ 2)
    have hmap : (∫ z, φ z ∂(ENNReal.ofReal (k⁻¹ ^ 2) •
        μ.map (fun z : ℂ => k⁻¹ • z))) = (k⁻¹ ^ 2) * ∫ z, ψ z ∂μ := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul,
        integral_map (by fun_prop) hφ.aestronglyMeasurable]
    rw [hmap]
    convert hlim using 1
    funext n
    let r := dyadicScale n
    let w : ℂ → ℝ := fun z => r ^ (γ ^ 2 / 2) * Real.exp (γ * hε r z)
    have hw : Continuous w := continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (hc n)))
    have hw0 : ∀ z, 0 ≤ w z := fun z => mul_nonneg
      (Real.rpow_nonneg (dyadicScale_pos n).le _) (Real.exp_nonneg _)
    change (∫ z, φ z ∂(volume.withDensity fun z => ENNReal.ofReal (w (k • z)))) =
      (k⁻¹ ^ 2) * ∫ z, ψ z ∂(volume.withDensity fun z => ENNReal.ofReal (w z))
    rw [Section6.integral_withDensity_nonnegative volume (fun z => w (k • z)) φ
      (hw.comp (continuous_const_smul k)) (fun z => hw0 (k • z)),
      Section6.integral_withDensity_nonnegative volume w ψ hw hw0]
    have hcomp : (fun x : ℂ => (ψ (k • x)) * w (k • x)) =
        (fun x => φ x * w (k • x)) := by
      funext x
      simp [ψ, hk.ne']
    have hs := Measure.integral_comp_smul volume (fun z : ℂ => ψ z * w z) k
    rw [hcomp] at hs
    rw [Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (pow_pos hk _)), ← inv_pow,
      smul_eq_mul] at hs
    exact hs

/-- Dyadic coordinate change for a deterministic LQG limit, including the
`Q log k` correction. No GFF invariance or coordinate-change input is used. -/
theorem IsLQGLimit.dyadic_coordinate_change {γ : ℝ} (hγ : γ ≠ 0)
    {hε : ℝ → ℂ → ℝ} {μ : Measure ℂ} (hμ : IsLQGLimit γ hε μ)
    (m : ℕ) (hc : ∀ n, Continuous (hε ((2 : ℝ) ^ m * dyadicScale n))) :
    IsLQGLimit γ (fun r z => hε ((2 : ℝ) ^ m * r) ((2 : ℝ) ^ m • z) +
      lqgQ γ * Real.log ((2 : ℝ) ^ m))
      (μ.map (fun z : ℂ => ((2 : ℝ) ^ m)⁻¹ • z)) := by
  let k : ℝ := (2 : ℝ) ^ m
  have hk : 0 < k := by dsimp [k]; positivity
  have hc' : ∀ n, Continuous (fun z => hε (k * dyadicScale n) z +
      γ / 2 * Real.log k) := fun n =>
    (hc n).add continuous_const
  have hs := (hμ.dyadic_radius_shift m).spatial_dilation hc' hk
  have ht := hs.add_const ((2 / γ) * Real.log k)
  have he : Real.exp (γ * ((2 / γ) * Real.log k)) = k ^ 2 := by
    have heq : γ * ((2 / γ) * Real.log k) = Real.log k + Real.log k := by
      field_simp
      ring
    rw [heq, Real.exp_add, Real.exp_log hk]
    ring
  have hscalar : ENNReal.ofReal (Real.exp (γ * ((2 / γ) * Real.log k))) •
      (ENNReal.ofReal (k⁻¹ ^ 2) • μ.map (fun z : ℂ => k⁻¹ • z)) =
      μ.map (fun z : ℂ => k⁻¹ • z) := by
    rw [smul_smul, he, ← ENNReal.ofReal_mul (sq_nonneg _)]
    have : k ^ 2 * k⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hk.ne', one_pow]
    rw [this, ENNReal.ofReal_one, one_smul]
  rw [hscalar] at ht
  convert ht using 1
  funext r z
  dsimp [lqgQ]
  ring

/-- Normalized pullbacks at dyadic radii are LQG measures of the rescaled
field. This follows from the dyadic definition and requires no coordinate-change
literature input, including in the presence of a logarithmic singularity. -/
theorem isLQGMeasureOfField_normalizedPullback_dyadic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : γ ≠ 0)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (m : ℕ) :
    IsLQGMeasureOfField P γ α₀
      (fun ω r z => hcirc ω ((2 : ℝ) ^ m * r) ((2 : ℝ) ^ m • z) -
        hcirc ω ((2 : ℝ) ^ m) 0)
      (fun ω => normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ m) (hcirc ω) (μ ω)) := by
  let k : ℝ := (2 : ℝ) ^ m
  have hk : 0 < k := by dsimp [k]; positivity
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous
      (fieldCircleAverage α₀ (hcirc ω) (k * dyadicScale n)) := by
    rw [ae_all_iff]
    intro n
    exact hGFF.ae_continuous_fieldCircleAverage α₀ (mul_pos hk (dyadicScale_pos n))
  filter_upwards [hμ, hc] with ω hω hcω
  let c := lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0
  have h := (hω.dyadic_coordinate_change hγ m hcω).add_const (-c)
  change IsLQGLimit γ (fun r z => fieldCircleAverage α₀ (hcirc ω) (k * r) (k • z) +
    lqgQ γ * Real.log k + -c)
    (ENNReal.ofReal (Real.exp (γ * -c)) • (μ ω).map (fun z : ℂ => k⁻¹ • z)) at h
  have hm : ENNReal.ofReal (Real.exp (γ * -c)) •
      (μ ω).map (fun z : ℂ => k⁻¹ • z) =
      normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω) := by
    simp only [normalizedPullbackMeasure, ← Real.exp_neg, mul_neg]
    rfl
  have hf : ∀ n, lqgApprox γ
      (fun r z => fieldCircleAverage α₀ (hcirc ω) (k * r) (k • z) +
        lqgQ γ * Real.log k + -c) (dyadicScale n) =
      lqgApprox γ (fieldCircleAverage α₀
        (fun r z => hcirc ω (k * r) (k • z) - hcirc ω k 0)) (dyadicScale n) := by
    intro n
    simp only [lqgApprox]
    congr 1
    funext z
    rw [fieldCircleAverage_affineScale α₀ (hcirc ω) hk (dyadicScale_pos n)]
    dsimp [c]
    congr 3
    ring
  rw [hm] at h
  refine ⟨h.isLocallyFiniteMeasure, fun f hf' hfc => ?_⟩
  simpa only [hf] using h.tendsto_integral f hf' hfc

/-- The unit-disc boundary theorem transfers to all dyadic radii using GFF
affine invariance, without an LQG coordinate-change input. The affine
invariance hypothesis remains staged pending source review. -/
theorem clusterBoundaryNullDyadicRadii_of_affine
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc) :
    ClusterBoundaryNullCofinalRadii.{u} (fun n => (2 : ℝ) ^ n) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  rw [ae_all_iff]
  intro n
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by dsimp [k]; positivity
  let hC' := affinePairing hC hcirc (k : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z => hcirc ω (k * r) (k • z) - hcirc ω k 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have heq : hcirc' = affineCircle hcirc (k : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul, Real.norm_eq_abs, abs_of_pos hk]
    rw [heq]
    exact hAff Ω P hC hcirc hGFF (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) :=
    isLQGMeasureOfField_normalizedPullback_dyadic hGFF hγ.ne' hμ n
  have hunit := h8 γ α₀ hγ hγ2 hα Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) hGFF' hμ'
  filter_upwards [hunit, clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ
    hGFF hμ k hk] with ω hu hs
  exact clusterBoundaryNull_of_normalized_scale γ α₀ k hk (hcirc ω) (μ ω) hu hs

/-- Weak Proposition 9.2 from volume growth, Proposition 8.1, and staged
GFF affine invariance. No LQG coordinate-change input is required. -/
theorem subharmonicBallUniquenessWeak_of_dyadic_affine
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_dyadicRadii hI2
    (clusterBoundaryNullDyadicRadii_of_affine h8 hAff)

end HarmonicBalls
