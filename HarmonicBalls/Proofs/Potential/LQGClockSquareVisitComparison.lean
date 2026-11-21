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
    simp only [mem_preimage, mem_ofPred_eq]
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
  have : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hq0 : 0 ≤ q := by linarith
  let c := LatticeProb.dyadicSquareCentre r i
  let g : ℝ → ℂ := fun t => (b t.toNNReal - c) / (4 * r : ℝ)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have : IsFiniteMeasure (volume.restrict I) := ⟨by
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

/-- The normalized circle-average density `exp (γ H_δ(w) - γ² Var / 2)` of a field at
smoothing `δ`, with variance `-log δ`. -/
noncomputable def normalizedCircleDensity {Ω : Type*} (H : Ω → ℝ → ℂ → ℝ) (γ δ : ℝ) (ω : Ω)
    (w : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * H ω δ w - γ ^ 2 * (-Real.log δ) / 2))

theorem measurable_normalizedCircleDensity {Ω : Type*} [MeasurableSpace Ω]
    {H : Ω → ℝ → ℂ → ℝ} {ε : ℝ} (hHm : Measurable (fun p : ℂ × Ω => H p.2 ε p.1)) (γ : ℝ) :
    Measurable (Function.uncurry fun ω w => normalizedCircleDensity H γ ε ω w) := by
  have h : Measurable (fun p : Ω × ℂ => H p.1 ε p.2) := hHm.comp measurable_swap
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((h.const_mul γ).sub_const _))

theorem measurable_uncurry_indicator {α : Type*} [MeasurableSpace α] {f : α → ℂ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) {Q : Set ℂ} (hQ : MeasurableSet Q) :
    Measurable (Function.uncurry fun a w => Q.indicator (f a) w) := by
  have h := hf.indicator (measurable_snd hQ)
  convert h using 1
  funext p
  by_cases hp : p.2 ∈ Q
  · rw [show (Function.uncurry fun a w => Q.indicator (f a) w) p = Q.indicator (f p.1) p.2 from
      rfl, Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Q from hp)]
    rfl
  · rw [show (Function.uncurry fun a w => Q.indicator (f a) w) p = Q.indicator (f p.1) p.2 from
      rfl, Set.indicator_of_notMem hp,
      Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' Q from hp)]

theorem affineScaling_eq_div {κ : ℝ} (hκ : 0 < κ) (z w : ℂ) :
    affineScaling hκ z w = (w - z) / (κ : ℂ) := by
  rw [affineScaling_apply, Complex.real_smul, div_eq_inv_mul, Complex.ofReal_inv]

theorem preimage_affineScaling_ball {κ : ℝ} (hκ : 0 < κ) (z : ℂ) (ρ : ℝ) :
    affineScaling hκ z ⁻¹' ball 0 ρ = ball z (κ * ρ) := by
  ext w
  simp only [mem_preimage, mem_ball, dist_eq_norm, sub_zero, affineScaling_apply, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hκ]
  exact inv_mul_lt_iff₀ hκ

/-- **One visit to a grid square.** For a square of side `r ≤ 1/10` meeting the disc of
radius `1/2`, the field-averaged `q`-th moment of the normalized density at smoothing
`4 r δ` integrated along Brownian motion until it leaves the disc of radius `3 r / 2`
about the centre is at most the Gaussian scaling factor times `((4 r) ^ 2) ^ q` times the
reference-square moment at smoothing `δ`, stopped at the exit from the disc of radius
`3 / 8` and started at the rescaled point. -/
theorem lintegral_square_visit_rpow_le_reference
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {H : Ω → ℝ → ℂ → ℝ}
    (hHm : ∀ ε, 0 < ε → Measurable (fun p : ℂ × Ω => H p.2 ε p.1))
    (hHae : ∀ᵐ ω ∂P, ∀ ε z, H ω ε z = hcirc ω ε z)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ) {q : ℝ} (hq : 1 ≤ q) (y : ℂ) :
    (∫⁻ ω, ∫⁻ b, pathOccupationBefore ((LatticeProb.dyadicSquare r i).indicator
        (normalizedCircleDensity H γ (4 * r * δ) ω))
        (ContinuousPath.exitTime (ball (LatticeProb.dyadicSquareCentre r i) (3 * r / 2)) b) b ^ q
        ∂planarBrownianMotion y ∂P) ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
        ENNReal.ofReal ((4 * r) ^ 2) ^ q *
        ∫⁻ ω, ∫⁻ b, pathOccupationBefore (LatticeProb.LQG.lqgSquare.indicator
          (normalizedCircleDensity H γ δ ω)) (ContinuousPath.exitTime (ball 0 (3 / 8)) b) b ^ q
          ∂planarBrownianMotion ((4 * r)⁻¹ • (y - LatticeProb.dyadicSquareCentre r i)) ∂P := by
  have : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hκ : 0 < 4 * r := by positivity
  have hε : 0 < 4 * r * δ := by positivity
  set c := LatticeProb.dyadicSquareCentre r i with hcdef
  set e := affineScaling hκ c with hedef
  set C' : ℝ≥0 := ((4 * r) ^ 2).toNNReal with hC'def
  have hC'pos : 0 < C' := Real.toNNReal_pos.mpr (by positivity)
  set Cr : ℝ≥0∞ := ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2))
    with hCrdef
  have hQm : MeasurableSet (LatticeProb.dyadicSquare r i) := LatticeProb.measurableSet_dyadicSquare r i
  have hball : e ⁻¹' ball 0 (3 / 8) = ball c (3 * r / 2) := by
    rw [hedef, preimage_affineScaling_ball]
    congr 1
    ring
  have hdε := measurable_normalizedCircleDensity (hHm _ hε) γ
  have hdδ := measurable_normalizedCircleDensity (hHm _ hδ) γ
  have hZ : Measurable (fun p : Ω × ContinuousPath ℂ =>
      pathOccupationBefore ((LatticeProb.dyadicSquare r i).indicator
        (normalizedCircleDensity H γ (4 * r * δ) p.1))
        (ContinuousPath.exitTime (ball c (3 * r / 2)) p.2) p.2) :=
    measurable_pathOccupationBefore
      (fun (p : Ω × ContinuousPath ℂ) w => (LatticeProb.dyadicSquare r i).indicator
        (normalizedCircleDensity H γ (4 * r * δ) p.1) w)
      ((measurable_uncurry_indicator hdε hQm).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      _ ((ContinuousPath.measurable_exitTime _ isOpen_ball).comp measurable_snd)
      _ measurable_snd
  have hRm : Measurable (fun p : Ω × ContinuousPath ℂ =>
      pathOccupationBefore (LatticeProb.LQG.lqgSquare.indicator
        (normalizedCircleDensity H γ δ p.1))
        (ContinuousPath.exitTime (ball 0 (3 / 8)) p.2) p.2) :=
    measurable_pathOccupationBefore
      (fun (p : Ω × ContinuousPath ℂ) w => LatticeProb.LQG.lqgSquare.indicator
        (normalizedCircleDensity H γ δ p.1) w)
      ((measurable_uncurry_indicator hdδ LatticeProb.LQG.measurableSet_lqgSquare).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      _ ((ContinuousPath.measurable_exitTime _ isOpen_ball).comp measurable_snd)
      _ measurable_snd
  -- the pathwise estimate
  have hpath : ∀ b : ContinuousPath ℂ, (∫⁻ ω, pathOccupationBefore
      ((LatticeProb.dyadicSquare r i).indicator (normalizedCircleDensity H γ (4 * r * δ) ω))
      (ContinuousPath.exitTime (ball c (3 * r / 2)) b) b ^ q ∂P) ≤
      Cr * (C' : ℝ≥0∞) ^ q * ∫⁻ ω, pathOccupationBefore (LatticeProb.LQG.lqgSquare.indicator
        (normalizedCircleDensity H γ δ ω))
        (ContinuousPath.exitTime (ball 0 (3 / 8)) (ContinuousPath.rescale e C' b))
        (ContinuousPath.rescale e C' b) ^ q ∂P := by
    intro b
    let S : Set ℝ := {t : ℝ | (0 ≤ t ∧ ENNReal.ofReal t <
      ContinuousPath.exitTime (ball c (3 * r / 2)) b) ∧ b t.toNNReal ∈ LatticeProb.dyadicSquare r i}
    have hb : Measurable (fun t : ℝ => b t.toNNReal) :=
      b.continuous.measurable.comp measurable_real_toNNReal
    have hSm : MeasurableSet S :=
      ((measurableSet_le measurable_const measurable_id).inter
        (measurableSet_lt ENNReal.measurable_ofReal measurable_const)).inter (hQm.preimage hb)
    let I : ℕ → Set ℝ := fun n => S ∩ Icc 0 n
    have hIm : ∀ n, MeasurableSet (I n) := fun n => hSm.inter measurableSet_Icc
    let X : ℕ → Ω → ℝ≥0∞ := fun n ω => ∫⁻ t in I n,
      normalizedCircleDensity H γ (4 * r * δ) ω (b t.toNNReal)
    have hZS : ∀ ω, pathOccupationBefore ((LatticeProb.dyadicSquare r i).indicator
        (normalizedCircleDensity H γ (4 * r * δ) ω))
        (ContinuousPath.exitTime (ball c (3 * r / 2)) b) b =
        ∫⁻ t in S, normalizedCircleDensity H γ (4 * r * δ) ω (b t.toNNReal) := by
      intro ω
      unfold pathOccupationBefore
      rw [← lintegral_indicator hSm]
      apply lintegral_congr
      intro t
      by_cases h1 : t ∈ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t <
          ContinuousPath.exitTime (ball c (3 * r / 2)) b}
      · rw [Set.indicator_of_mem h1]
        by_cases h2 : b t.toNNReal ∈ LatticeProb.dyadicSquare r i
        · rw [Set.indicator_of_mem h2, Set.indicator_of_mem (show t ∈ S from ⟨h1, h2⟩)]
        · rw [Set.indicator_of_notMem h2,
            Set.indicator_of_notMem (show t ∉ S from fun h => h2 h.2)]
      · rw [Set.indicator_of_notMem h1,
          Set.indicator_of_notMem (show t ∉ S from fun h => h1 h.1)]
    have hXm : ∀ n, Measurable (X n) := fun n =>
      (hdε.comp (measurable_fst.prodMk (hb.comp measurable_snd))).lintegral_prod_right'
    have hXmono : ∀ ω, Monotone fun n => X n ω := fun ω n m hnm =>
      lintegral_mono_set (inter_subset_inter_right _ (Icc_subset_Icc_right (by exact_mod_cast hnm)))
    have hXlim : ∀ ω, Tendsto (fun n => X n ω) atTop
        (𝓝 (∫⁻ t in S, normalizedCircleDensity H γ (4 * r * δ) ω (b t.toNNReal))) := by
      intro ω
      have hiU : (⋃ n : ℕ, I n) = S := by
        ext t
        simp only [mem_iUnion]
        constructor
        · rintro ⟨n, hn⟩
          exact hn.1
        · intro ht
          obtain ⟨n, hn⟩ := exists_nat_ge t
          exact ⟨n, ht, ht.1.1, hn⟩
      have hmono : Monotone I := fun n m hnm =>
        inter_subset_inter_right _ (Icc_subset_Icc_right (by exact_mod_cast hnm))
      have h := tendsto_measure_iUnion_atTop (μ := volume.withDensity
        (fun t : ℝ => normalizedCircleDensity H γ (4 * r * δ) ω (b t.toNNReal))) hmono
      rw [hiU, withDensity_apply _ hSm] at h
      refine Tendsto.congr (fun n => ?_) h
      exact withDensity_apply _ (hIm n)
    have hbound : ∀ n : ℕ, (∫⁻ ω, X n ω ^ q ∂P) ≤ Cr * (C' : ℝ≥0∞) ^ q *
        ∫⁻ ω, pathOccupationBefore (LatticeProb.LQG.lqgSquare.indicator
          (normalizedCircleDensity H γ δ ω))
          (ContinuousPath.exitTime (ball 0 (3 / 8)) (ContinuousPath.rescale e C' b))
          (ContinuousPath.rescale e C' b) ^ q ∂P := by
      intro n
      have hcmp := lintegral_rpow_square_gmcDensity_le_reference_of_timeSet hh hr hr10 hδ hδ2
        hi γ b (hIm n) (n := (n : ℝ)) inter_subset_right (fun t ht => ht.1.2) hq
      have hL : (∫⁻ ω, X n ω ^ q ∂P) = ∫⁻ ω, (∫⁻ t in I n, ENNReal.ofReal
          (LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω)) ^ q ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hHae] with ω hω
        congr 1
        apply lintegral_congr
        intro t
        rw [normalizedCircleDensity, gmcDensity_eq_exp_normalized hcirc hε, hω]
      have hR : ∀ ω, (∀ ε z, H ω ε z = hcirc ω ε z) →
          (∫⁻ t in I n, ENNReal.ofReal (Real.exp (γ * hcirc ω δ
            ((b t.toNNReal - c) / (4 * r : ℝ)) - γ ^ 2 * (-Real.log δ) / 2))) ≤
          (C' : ℝ≥0∞) * pathOccupationBefore (LatticeProb.LQG.lqgSquare.indicator
            (normalizedCircleDensity H γ δ ω))
            (ContinuousPath.exitTime (ball 0 (3 / 8)) (ContinuousPath.rescale e C' b))
            (ContinuousPath.rescale e C' b) := by
        intro ω hω
        have hscale := pathOccupationBefore_exitTime_rescale e hC'pos
          (LatticeProb.LQG.lqgSquare.indicator (normalizedCircleDensity H γ δ ω))
          ((hdδ.comp measurable_prodMk_left).indicator LatticeProb.LQG.measurableSet_lqgSquare)
          (ball 0 (3 / 8)) b
        rw [← hscale, hball]
        unfold pathOccupationBefore
        rw [← lintegral_indicator (hIm n)]
        apply lintegral_mono
        intro t
        by_cases ht : t ∈ I n
        · have hmem : t ∈ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t <
              ContinuousPath.exitTime (ball c (3 * r / 2)) b} := ht.1.1
          have hsq : e (b t.toNNReal) ∈ LatticeProb.LQG.lqgSquare := by
            rw [hedef, affineScaling_eq_div]
            exact dyadicSquare_rescaled_mem_lqgSquare hr ht.1.2
          rw [Set.indicator_of_mem ht, Set.indicator_of_mem hmem]
          show _ ≤ LatticeProb.LQG.lqgSquare.indicator (normalizedCircleDensity H γ δ ω)
            (e (b t.toNNReal))
          rw [Set.indicator_of_mem hsq]
          apply le_of_eq
          rw [normalizedCircleDensity, hω, hedef, affineScaling_eq_div]
        · rw [Set.indicator_of_notMem ht]
          exact zero_le
      calc (∫⁻ ω, X n ω ^ q ∂P)
          ≤ Cr * ∫⁻ ω, (∫⁻ t in I n, ENNReal.ofReal (Real.exp (γ * hcirc ω δ
            ((b t.toNNReal - c) / (4 * r : ℝ)) - γ ^ 2 * (-Real.log δ) / 2))) ^ q ∂P := by
            rw [hL]
            exact hcmp
        _ ≤ Cr * ∫⁻ ω, ((C' : ℝ≥0∞) * pathOccupationBefore (LatticeProb.LQG.lqgSquare.indicator
            (normalizedCircleDensity H γ δ ω))
            (ContinuousPath.exitTime (ball 0 (3 / 8)) (ContinuousPath.rescale e C' b))
            (ContinuousPath.rescale e C' b)) ^ q ∂P := by
            refine mul_le_mul_right (lintegral_mono_ae ?_) Cr
            filter_upwards [hHae] with ω hω
            exact ENNReal.rpow_le_rpow (hR ω hω) hq0.le
        _ = Cr * (C' : ℝ≥0∞) ^ q * ∫⁻ ω, pathOccupationBefore (LatticeProb.LQG.lqgSquare.indicator
            (normalizedCircleDensity H γ δ ω))
            (ContinuousPath.exitTime (ball 0 (3 / 8)) (ContinuousPath.rescale e C' b))
            (ContinuousPath.rescale e C' b) ^ q ∂P := by
            simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
            rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.coe_ne_top),
              mul_assoc]
    have hlim : Tendsto (fun n => ∫⁻ ω, X n ω ^ q ∂P) atTop
        (𝓝 (∫⁻ ω, pathOccupationBefore ((LatticeProb.dyadicSquare r i).indicator
          (normalizedCircleDensity H γ (4 * r * δ) ω))
          (ContinuousPath.exitTime (ball c (3 * r / 2)) b) b ^ q ∂P)) := by
      simp_rw [hZS]
      exact lintegral_tendsto_of_tendsto_of_monotone
        (fun n => ((hXm n).pow_const q).aemeasurable)
        (Filter.Eventually.of_forall fun ω n m hnm =>
          ENNReal.rpow_le_rpow (hXmono ω hnm) hq0.le)
        (Filter.Eventually.of_forall fun ω =>
          (ENNReal.continuous_rpow_const.tendsto _).comp (hXlim ω))
    exact le_of_tendsto' hlim hbound
  -- average over the Brownian path and rescale its law
  have hG : Measurable (fun b' : ContinuousPath ℂ => ∫⁻ ω, pathOccupationBefore
      (LatticeProb.LQG.lqgSquare.indicator (normalizedCircleDensity H γ δ ω))
      (ContinuousPath.exitTime (ball 0 (3 / 8)) b') b' ^ q ∂P) :=
    (hRm.pow_const q).lintegral_prod_left'
  have hlaw := planarBrownianMotion_map_rescale_affineScaling hκ c y
  rw [lintegral_lintegral_swap (f := fun ω b => pathOccupationBefore
      ((LatticeProb.dyadicSquare r i).indicator (normalizedCircleDensity H γ (4 * r * δ) ω))
      (ContinuousPath.exitTime (ball c (3 * r / 2)) b) b ^ q) (hZ.pow_const q).aemeasurable,
    lintegral_lintegral_swap (f := fun ω b => pathOccupationBefore
      (LatticeProb.LQG.lqgSquare.indicator (normalizedCircleDensity H γ δ ω))
      (ContinuousPath.exitTime (ball 0 (3 / 8)) b) b ^ q) (hRm.pow_const q).aemeasurable, ← hlaw,
    lintegral_map hG (ContinuousPath.measurable_rescale _ _), ← lintegral_const_mul' _ _
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top))]
  exact lintegral_mono fun b => hpath b

end HarmonicBalls
