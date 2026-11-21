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

/-- The fixed-scale comparison of a grid square with the reference square holds for
every bounded measurable set of times at which the path lies in the square. -/
theorem lintegral_rpow_square_gmcDensity_le_reference_of_timeSet
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ)
    (b : ContinuousPath ℂ) {I : Set ℝ} (hI : MeasurableSet I) {n : ℝ} (hIn : I ⊆ Icc 0 n)
    (hIsq : ∀ t ∈ I, b t.toNNReal ∈ LatticeProb.dyadicSquare r i) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ ω, (∫⁻ t in I, ENNReal.ofReal
      (LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω)) ^ q ∂P) ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
        ∫⁻ ω, (∫⁻ t in I, ENNReal.ofReal (Real.exp (γ * hcirc ω δ
          ((b t.toNNReal - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ)) -
            γ ^ 2 * (-Real.log δ) / 2))) ^ q ∂P := by
  haveI : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hq0 : 0 ≤ q := by linarith
  let c := LatticeProb.dyadicSquareCentre r i
  let g : ℝ → ℂ := fun t => (b t.toNNReal - c) / (4 * r : ℝ)
  have hg : Continuous g := by dsimp [g]; fun_prop
  haveI : IsFiniteMeasure (volume.restrict I) := ⟨by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact (measure_mono hIn).trans_lt measure_Icc_lt_top⟩
  let ν : Measure ℂ := Measure.map g (volume.restrict I)
  have hν : ∀ᵐ z ∂ν, z ∈ LatticeProb.LQG.lqgSquare := by
    apply (ae_map_iff hg.measurable.aemeasurable LatticeProb.LQG.measurableSet_lqgSquare).2
    filter_upwards [ae_restrict_mem hI] with t ht
    exact dyadicSquare_rescaled_mem_lqgSquare hr (hIsq t ht)
  have h := integral_rpow_annularSquare_le_of_finite_measure hh hr hr10 hδ hδ2 hi γ ν hν hq
  let F : Ω → ℝ := fun ω => ∫ z, Real.exp
    (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * z + c) -
      γ ^ 2 * (-Real.log (4 * r * δ)) / 2) ∂ν
  let G : Ω → ℝ := fun ω => ∫ z, Real.exp (γ * hcirc ω δ z - γ ^ 2 * (-Real.log δ) / 2) ∂ν
  have hFi : Integrable (fun ω => F ω ^ q) P := h.1
  have hGi : Integrable (fun ω => G ω ^ q) P := h.2.1
  have hle : (∫ ω, F ω ^ q ∂P) ≤
      Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) * ∫ ω, G ω ^ q ∂P := h.2.2
  have hε : 0 < 4 * r * δ := by positivity
  have hR : (((4 * r : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (show 4 * r ≠ 0 by positivity)
  have hFnn : ∀ ω, 0 ≤ F ω := fun ω => integral_nonneg fun _ => (Real.exp_pos _).le
  have hGnn : ∀ ω, 0 ≤ G ω := fun ω => integral_nonneg fun _ => (Real.exp_pos _).le
  have hFeq : ∀ᵐ ω ∂P, ENNReal.ofReal (F ω) = ∫⁻ t in I, ENNReal.ofReal
      (LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω) := by
    filter_upwards [hh.ae_continuous_circle_fixed hε] with ω hω
    have hcont : Continuous (fun z : ℂ => Real.exp
        (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * z + c) -
          γ ^ 2 * (-Real.log (4 * r * δ)) / 2)) := by fun_prop
    have hmap : F ω = ∫ t in I, Real.exp
        (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * g t + c) -
          γ ^ 2 * (-Real.log (4 * r * δ)) / 2) :=
      integral_map hg.measurable.aemeasurable hcont.aestronglyMeasurable
    have hpt : ∀ t, Real.exp (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * g t + c) -
        γ ^ 2 * (-Real.log (4 * r * δ)) / 2) =
        LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω := by
      intro t
      rw [gmcDensity_eq_exp_normalized hcirc hε]
      dsimp only [g]
      rw [mul_div_cancel₀ _ hR, sub_add_cancel]
    have hcont2 : Continuous (fun t : ℝ =>
        LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω) := by
      simp only [LatticeProb.Gauss.gmcDensity]
      fun_prop
    rw [hmap, integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact ofReal_integral_eq_lintegral_ofReal (hcont2.integrableOn_Icc.mono_set hIn)
      (Filter.Eventually.of_forall fun t => LatticeProb.Gauss.gmcDensity_nonneg hcirc hε γ _ _)
  have hGeq : ∀ᵐ ω ∂P, ENNReal.ofReal (G ω) = ∫⁻ t in I, ENNReal.ofReal (Real.exp
      (γ * hcirc ω δ ((b t.toNNReal - c) / (4 * r : ℝ)) - γ ^ 2 * (-Real.log δ) / 2)) := by
    filter_upwards [hh.ae_continuous_circle_fixed hδ] with ω hω
    have hcont : Continuous (fun z : ℂ => Real.exp
        (γ * hcirc ω δ z - γ ^ 2 * (-Real.log δ) / 2)) := by fun_prop
    have hmap : G ω = ∫ t in I, Real.exp (γ * hcirc ω δ (g t) - γ ^ 2 * (-Real.log δ) / 2) :=
      integral_map hg.measurable.aemeasurable hcont.aestronglyMeasurable
    rw [hmap]
    exact ofReal_integral_eq_lintegral_ofReal ((hcont.comp hg).integrableOn_Icc.mono_set hIn)
      (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
  calc (∫⁻ ω, (∫⁻ t in I, ENNReal.ofReal
        (LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω)) ^ q ∂P)
      = ∫⁻ ω, ENNReal.ofReal (F ω ^ q) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hFeq] with ω hω
        rw [← hω, ENNReal.ofReal_rpow_of_nonneg (hFnn ω) hq0]
    _ = ENNReal.ofReal (∫ ω, F ω ^ q ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hFi
          (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hFnn ω) q)).symm
    _ ≤ ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) *
          ∫ ω, G ω ^ q ∂P) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
          ENNReal.ofReal (∫ ω, G ω ^ q ∂P) := ENNReal.ofReal_mul (Real.exp_pos _).le
    _ = _ := by
        congr 1
        rw [ofReal_integral_eq_lintegral_ofReal hGi
          (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hGnn ω) q)]
        apply lintegral_congr_ae
        filter_upwards [hGeq] with ω hω
        rw [← hω, ENNReal.ofReal_rpow_of_nonneg (hGnn ω) hq0]

end HarmonicBalls
