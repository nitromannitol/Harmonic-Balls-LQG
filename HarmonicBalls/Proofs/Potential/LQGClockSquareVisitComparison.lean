import HarmonicBalls.Proofs.Potential.LQGClockAnnularReturnMoment
import HarmonicBalls.Proofs.Sec8.ExitTimeScaling

/-! # One visit to a grid square, compared with the reference square

A Brownian path started in a grid square of side `r` is followed until it leaves the
concentric disc of radius `3 r / 2`. Under the affine space-time scaling that maps the
square into the reference square `[-1/8, 1/8]²`, this visit becomes a reference-square
occupation stopped at the exit from the disc of radius `3 / 8`, with a time factor
`(4 r) ^ 2`. The fixed-scale Gaussian comparison of a grid square with the reference
square holds for every bounded set of times spent in the square.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology

namespace HarmonicBalls

/-- Rescaling space by a homeomorphism and time by `c` turns the occupation before an
exit time into `c` times the occupation of the rescaled path before the rescaled exit. -/
theorem pathOccupationBefore_exitTime_rescale (e : ℂ ≃ₜ ℂ) {c : ℝ≥0} (hc : 0 < c)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (U : Set ℂ) (b : ContinuousPath ℂ) :
    pathOccupationBefore (fun w => g (e w)) (ContinuousPath.exitTime (e ⁻¹' U) b) b =
      c * pathOccupationBefore g (ContinuousPath.exitTime U (ContinuousPath.rescale e c b))
        (ContinuousPath.rescale e c b) := by
  have hτ : ContinuousPath.exitTime (e ⁻¹' U) b =
      c * ContinuousPath.exitTime U (ContinuousPath.rescale e c b) :=
    (exitTime_rescale_mul e c hc U b).symm
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  unfold pathOccupationBefore
  have hS : MeasurableSet {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t <
      (c : ℝ≥0∞) * ContinuousPath.exitTime U (ContinuousPath.rescale e c b)} :=
    (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  have hS' : MeasurableSet {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s <
      ContinuousPath.exitTime U (ContinuousPath.rescale e c b)} :=
    (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  have hf : Measurable (fun t : ℝ => g (e (b t.toNNReal))) :=
    hg.comp (e.continuous.measurable.comp (b.continuous.measurable.comp measurable_real_toNNReal))
  rw [hτ, lintegral_indicator hS, lintegral_time_dilation hcR _ hS _ hf,
    ENNReal.ofReal_coe_nnreal, lintegral_indicator hS']
  have hpre : (fun s : ℝ => (c : ℝ) * s) ⁻¹' {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t <
      (c : ℝ≥0∞) * ContinuousPath.exitTime U (ContinuousPath.rescale e c b)} =
      {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s <
        ContinuousPath.exitTime U (ContinuousPath.rescale e c b)} := by
    ext s
    simp only [mem_preimage, mem_setOf_eq]
    constructor
    · rintro ⟨h0, h1⟩
      have hs0 : 0 ≤ s := (mul_nonneg_iff_of_pos_left hcR).mp h0
      refine ⟨hs0, ?_⟩
      rw [ENNReal.ofReal_mul hcR.le, ENNReal.ofReal_coe_nnreal] at h1
      exact (ENNReal.mul_lt_mul_iff_right hc0 ENNReal.coe_ne_top).mp h1
    · rintro ⟨h0, h1⟩
      refine ⟨mul_nonneg hcR.le h0, ?_⟩
      rw [ENNReal.ofReal_mul hcR.le, ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.mul_lt_mul_iff_right hc0 ENNReal.coe_ne_top).mpr h1
  rw [hpre]
  congr 1
  apply lintegral_congr
  intro s
  rw [ContinuousPath.rescale_apply, Real.toNNReal_mul hcR.le, Real.toNNReal_coe]

/-- The affine map `w ↦ κ⁻¹ (w - z)` as a homeomorphism of the plane. -/
noncomputable def affineScaling {κ : ℝ} (hκ : 0 < κ) (z : ℂ) : ℂ ≃ₜ ℂ :=
  (Homeomorph.addRight (-z)).trans (Homeomorph.smulOfNeZero κ⁻¹ (inv_ne_zero hκ.ne'))

theorem affineScaling_apply {κ : ℝ} (hκ : 0 < κ) (z w : ℂ) :
    affineScaling hκ z w = κ⁻¹ • (w - z) := by
  simp [affineScaling, sub_eq_add_neg]

/-- Brownian motion from `y`, viewed through `w ↦ κ⁻¹ (w - z)` at time speed `κ ^ 2`, is
Brownian motion from `κ⁻¹ (y - z)`. -/
theorem planarBrownianMotion_map_rescale_affineScaling {κ : ℝ} (hκ : 0 < κ) (z y : ℂ) :
    (planarBrownianMotion y).map
      (ContinuousPath.rescale (affineScaling hκ z) (κ ^ 2).toNNReal) =
      planarBrownianMotion (κ⁻¹ • (y - z)) := by
  have hc : (κ ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.mpr (by positivity)).ne'
  rw [← Section6.planarBrownianMotion_map_add (κ⁻¹ • (y - z)),
    ← Section6.planarBrownianMotion_map_scaledCenteredPlanarPath y hc,
    Measure.map_map ((Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight _)).measurable
      (Section6.continuous_scaledCenteredPlanarPath y _).measurable]
  congr 1
  funext b
  ext t
  have hs : Real.sqrt (((κ ^ 2).toNNReal : ℝ≥0) : ℝ) = κ := by
    rw [Real.coe_toNNReal _ (sq_nonneg κ), Real.sqrt_sq hκ.le]
  show κ⁻¹ • (b ((κ ^ 2).toNNReal * t) + -z) =
    (Real.sqrt (((κ ^ 2).toNNReal : ℝ≥0) : ℝ))⁻¹ •
      (b ((κ ^ 2).toNNReal * t) - y) + κ⁻¹ • (y - z)
  rw [hs, ← smul_add, ← sub_eq_add_neg]
  congr 1
  ring

end HarmonicBalls
