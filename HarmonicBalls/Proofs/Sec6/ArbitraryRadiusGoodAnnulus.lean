import HarmonicBalls.Proofs.Sec6.GoodAnnulusDyadicLaw
import HarmonicBalls.Proofs.Sec6.GoodAnnulusReduction
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly

/-! # Ball submean estimates at arbitrary radii

The fine-support assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric Complex
open scoped ENNReal

universe u

/-- A circular submean bound yields a ball submean bound at any positive radius. -/
theorem ball_submean_of_circle_submean_radius (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    {f : ℂ → ℝ≥0∞}
    (hf : Measurable f)
    (hcircle : ∀ r ∈ Ioo (ρ / 2 : ℝ) (ρ),
      f c ≤ ∫⁻ z, f z ∂(normalizedCircleMeasure c r)) :
    let D : ℝ≥0∞ := ENNReal.ofReal (ρ / 2) * ENNReal.ofReal (2 * Real.pi) *
      ENNReal.ofReal (ρ / 2)
    D * f c ≤ ∫⁻ z in ball c (ρ : ℝ), f z := by
  dsimp only
  let A : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi)
  have hA0 : A ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hAt : A ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv : ENNReal.ofReal ((2 * Real.pi)⁻¹) = A⁻¹ := by
    exact ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * Real.pi)
  have hθ : ∀ r ∈ Ioo (ρ / 2 : ℝ) (ρ),
      A * f c ≤ ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (circleMap c r θ) := by
    intro r hr
    have h := hcircle r hr
    rw [lintegral_normalizedCircleMeasure c r hf, hinv] at h
    have hm : A * f c ≤ A * (A⁻¹ *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (circleMap c r θ)) := by gcongr
    rw [← mul_assoc, ENNReal.mul_inv_cancel hA0 hAt, one_mul] at hm
    exact hm
  have hbound : ∀ r ∈ Ioo (ρ / 2 : ℝ) (ρ),
      ENNReal.ofReal (ρ / 2) * A * f c ≤
        ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal r * f (circleMap c r θ) := by
    intro r hr
    have hm : Measurable (fun θ : ℝ => f (circleMap c r θ)) :=
      hf.comp (continuous_circleMap c r).measurable
    rw [lintegral_const_mul _ hm]
    calc
      ENNReal.ofReal (ρ / 2) * A * f c = ENNReal.ofReal (ρ / 2) * (A * f c) := by rw [mul_assoc]
      _ ≤ ENNReal.ofReal (ρ / 2) *
          ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (circleMap c r θ) := by gcongr; exact hθ r hr
      _ ≤ ENNReal.ofReal r *
          ∫⁻ θ in Ioo (-Real.pi) Real.pi, f (circleMap c r θ) := by
        gcongr
        exact hr.1.le
  calc
    ENNReal.ofReal (ρ / 2) * ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (ρ / 2) * f c =
        ∫⁻ _ in Ioo (ρ / 2 : ℝ) (ρ), ENNReal.ofReal (ρ / 2) * A * f c := by
      rw [setLIntegral_const, Real.volume_Ioo]
      have he : (ρ : ℝ) - ρ / 2 = ρ / 2 := by ring
      rw [he]
      dsimp only [A]
      ac_rfl
    _ ≤ ∫⁻ r in Ioo (ρ / 2 : ℝ) (ρ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * f (circleMap c r θ) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hbound r hr
    _ ≤ ∫⁻ r in Ioo (0 : ℝ) (ρ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal r * f (circleMap c r θ) := by
      apply lintegral_mono_set
      intro r hr
      exact ⟨by linarith [hr.1], hr.2⟩
    _ = ∫⁻ z in ball c (ρ : ℝ), f z := (lintegral_ball_polar c _ hf).symm


/-- The half-radius disc about the middle circle is contained in the annulus. -/
theorem middleCircle_half_disc_subset_annulus {z v : ℂ} {r : ℝ}
    (hr : 0 < r) (hv : v ∈ sphere z (4 * r)) :
    ball v (r / 2) ⊆ annulus z (3 * r) (5 * r) := by
  intro x hx
  have hv' : dist v z = 4 * r := hv
  have hx' : dist x v < r / 2 := hx
  have hu := dist_triangle x v z
  have hl := dist_triangle v x z
  have hs : dist v x = dist x v := dist_comm _ _
  change x ∈ ball z (5 * r) ∧ x ∉ closedBall z (3 * r)
  simp only [mem_ball, mem_closedBall, not_le]
  constructor <;> linarith

/-- Compact avoidance satisfies a ball submean estimate at every positive radius. -/
theorem goodAnnulus_avoidance_ball_submean {z : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧
      ∀ K : Set ℂ, IsCompact K → ∀ v ∈ sphere z (4 * r),
        planarBrownianMotion v
          {path | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) path ≤
            ContinuousPath.exitTime Kᶜ path} ≤
        C * ∫⁻ x in ball v (r / 4), planarBrownianMotion x
          {path | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) path ≤
            ContinuousPath.exitTime Kᶜ path} ∂volume := by
  let D : ℝ≥0∞ := ENNReal.ofReal ((r / 4) / 2) * ENNReal.ofReal (2 * Real.pi) *
      ENNReal.ofReal ((r / 4) / 2)
  have hD0 : D ≠ 0 := by dsimp only [D]; positivity
  have hDt : D ≠ ∞ := by
    dsimp only [D]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  refine ⟨D⁻¹, ENNReal.inv_ne_zero.mpr hDt, ENNReal.inv_ne_top.mpr hD0, ?_⟩
  intro K hK v hv
  let f : ℂ → ℝ≥0∞ := fun x => planarBrownianMotion x
    {path | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) path ≤
      ContinuousPath.exitTime Kᶜ path}
  have hf : Measurable f := measurable_avoidance_probability
    (isOpen_ball.sdiff isClosed_closedBall) hK
  have hcircle : ∀ s ∈ Ioo ((r / 4) / 2) (r / 4),
      f v ≤ ∫⁻ x, f x ∂(normalizedCircleMeasure v s) := by
    intro s hs
    apply planarBrownian_avoidance_le_circle_mean (isOpen_ball.sdiff isClosed_closedBall) hK
      (by linarith [hs.1]) (show s < r / 2 by linarith [hs.2])
    exact middleCircle_half_disc_subset_annulus hr hv
  have hsub := ball_submean_of_circle_submean_radius v (show 0 < r / 4 by positivity) hf hcircle
  change D * f v ≤ ∫⁻ x in ball v (r / 4), f x at hsub
  have hmul : D⁻¹ * (D * f v) ≤ D⁻¹ * ∫⁻ x in ball v (r / 4), f x := by gcongr
  rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDt, one_mul] at hmul
  simpa [f] using hmul

/-- Each fixed annulus has an almost surely positive good-annulus threshold,
using only volume growth and whole-plane GFF affine invariance. -/
theorem ae_goodAnnulus_threshold_of_disc_dyadic
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    {z : ℂ} {r b : ℝ} (hr : 0 < r) (hb : 0 < b) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) r z a b := by
  obtain ⟨C, hC0, hCt, hsub⟩ := goodAnnulus_avoidance_ball_submean (z := z) hr
  let := h.isProbabilityMeasure
  apply ae_exists_goodAnnulus_threshold_of_ae_local_fine_support μ hr hb ?_ ?_ hC0 hCt hsub
  · filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  · exact ae_ae_lqg_fine_support_of_disc_dyadic hgrowth hγ hγ2 h hμ hAff

/-- For each positive radius, one deterministic threshold works at every
centre and for every whole-plane realization. The threshold may depend on the
radius; no LQG coordinate-change law is assumed. -/
theorem exists_universal_goodAnnulus_probability_fixed_radius
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {r b : ℝ} (hr : 0 < r) (hb : 0 < b) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ → ∀ z : ℂ,
      P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  let := h₀.isProbabilityMeasure
  have hAff₀ := wholePlaneGFFAffineInvariance_proved P₀ hC₀ hcirc₀
  have hmeas := h₀.aemeasurable_lqgMeasure hμ₀
  let ν := hmeas.mk μ₀
  have hν : Measurable ν := hmeas.measurable_mk
  have heq : μ₀ =ᵐ[P₀] ν := hmeas.ae_eq_mk
  have hae := ae_goodAnnulus_threshold_of_disc_dyadic hgrowth hγ hγ2 h₀ hμ₀ hAff₀
    (z := 0) hr hb
  have hνae : ∀ᵐ ω ∂P₀, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (ν ω) r 0 a b := by
    filter_upwards [hae, heq] with ω hω he
    simpa only [← he] using hω
  obtain ⟨a, ha, hbound⟩ := exists_goodAnnulus_threshold_of_measurable_events P₀
    (μ := ν) (fun n => (measurableSet_isGoodAnnulus_of_pos r hr 0
      ((1 / 2 : ℝ) ^ (n + 1)) b (by positivity)).preimage hν) hνae hp
  refine ⟨a, ha, ?_⟩
  intro Ω _ P hC hcirc μ h hμ z
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hm := (measurableSet_isGoodAnnulus_of_pos r hr 0 a b ha.1).compl
  have ht := (identDistrib_translateMeasure h hμ hAff z).measure_mem_eq hm
  change P {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} =
    P {ω | ¬ IsGoodAnnulus (affineMeasure γ hcirc μ 1 z ω) r 0 a b} at ht
  have ht' : {ω | ¬ IsGoodAnnulus (affineMeasure γ hcirc μ 1 z ω) r 0 a b} =
      {ω | ¬ IsGoodAnnulus (μ ω) r z a b} := by
    ext ω
    simp only [mem_ofPred_eq, isGoodAnnulus_affineMeasure_translate]
  rw [ht'] at ht
  have hd := h₀.identDistrib_lqgMeasure_across_spaces h hμ₀ hμ
  have hevent := hd.measure_mem_eq hm
  have hmod : P₀ {ω | ¬ IsGoodAnnulus (μ₀ ω) r 0 a b} =
      P₀ {ω | ¬ IsGoodAnnulus (ν ω) r 0 a b} := by
    apply measure_congr
    filter_upwards [heq] with ω hω
    simp only [hω]
  calc
    P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} =
        P {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} := ht.symm
    _ = P₀ {ω | ¬ IsGoodAnnulus (μ₀ ω) r 0 a b} := hevent.symm
    _ = P₀ {ω | ¬ IsGoodAnnulus (ν ω) r 0 a b} := hmod
    _ ≤ ENNReal.ofReal (1 - p) := hbound

/-- The failure probability is constant along every dyadic orbit of radii. -/
theorem badGoodAnnulus_probability_eq_dyadic_orbit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {r : ℝ} (hr : 0 < r) (n : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    P {ω | ¬ IsGoodAnnulus (μ ω) (r * dyadicScale n) 0 a b} =
      P {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} := by
  let s := r * dyadicScale n
  let k : ℝ := (2 : ℝ) ^ n
  have hs : 0 < s := mul_pos hr (dyadicScale_pos n)
  have hk : 0 < k := by dsimp [k]; positivity
  have hks : k * s = r := by
    have hscale : k * dyadicScale n = 1 := by
      dsimp [k]
      simpa only [zero_add, dyadicScale, pow_zero] using dyadicScale_shift n 0
    dsimp [s]
    calc
      k * (r * dyadicScale n) = r * (k * dyadicScale n) := by ring
      _ = r := by rw [hscale, mul_one]
  have hm := (measurableSet_isGoodAnnulus_of_pos s hs 0 a b ha).compl
  have hd := (identDistrib_normalizedPullback_dyadic hγ h hμ
    (wholePlaneGFFAffineInvariance_proved P hC hcirc) n).measure_mem_eq hm
  change P {ω | ¬ IsGoodAnnulus (μ ω) s 0 a b} =
    P {ω | ¬ IsGoodAnnulus (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω)) s 0 a b} at hd
  have hd' : {ω | ¬ IsGoodAnnulus (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω)) s 0 a b} =
      {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} := by
    ext ω
    simp only [mem_ofPred_eq, normalizedPullbackMeasure]
    let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp
      (γ * (lqgQ γ * Real.log k + fieldCircleAverage 0 (hcirc ω) k 0)))⁻¹
    have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
    change ¬ IsGoodAnnulus (c • (μ ω).map (fun x : ℂ => k⁻¹ • x)) s 0 a b ↔
      ¬ IsGoodAnnulus (μ ω) r 0 a b
    rw [isGoodAnnulus_smul _ _ _ _ _ hc0 hct,
      isGoodAnnulus_map_inv_smul_iff hk, smul_zero, hks]
  rw [hd'] at hd
  exact hd

/-- A threshold uniform on any prescribed dyadic orbit, at every centre and
for all whole-plane realizations, follows from volume growth alone. -/
theorem exists_universal_goodAnnulus_probability_dyadic_orbit
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {r b : ℝ} (hr : 0 < r) (hb : 0 < b) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ → ∀ (n : ℕ) (z : ℂ),
      P {ω | ¬ IsGoodAnnulus (μ ω) (r * dyadicScale n) z a b} ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨a, ha, hbound⟩ :=
    exists_universal_goodAnnulus_probability_fixed_radius hgrowth hγ hγ2 h₀ hμ₀ hr hb hp
  refine ⟨a, ha, ?_⟩
  intro Ω _ P hC hcirc μ h hμ n z
  have hs : 0 < r * dyadicScale n := mul_pos hr (dyadicScale_pos n)
  have hm := (measurableSet_isGoodAnnulus_of_pos (r * dyadicScale n) hs 0 a b ha.1).compl
  have ht := (identDistrib_translateMeasure h hμ
    (wholePlaneGFFAffineInvariance_proved P hC hcirc) z).measure_mem_eq hm
  change P {ω | ¬ IsGoodAnnulus (μ ω) (r * dyadicScale n) 0 a b} =
    P {ω | ¬ IsGoodAnnulus (affineMeasure γ hcirc μ 1 z ω) (r * dyadicScale n) 0 a b} at ht
  have ht' : {ω | ¬ IsGoodAnnulus (affineMeasure γ hcirc μ 1 z ω) (r * dyadicScale n) 0 a b} =
      {ω | ¬ IsGoodAnnulus (μ ω) (r * dyadicScale n) z a b} := by
    ext ω
    simp only [mem_ofPred_eq, isGoodAnnulus_affineMeasure_translate]
  rw [ht'] at ht
  rw [← ht, badGoodAnnulus_probability_eq_dyadic_orbit hγ h hμ hr n ha.1 b]
  exact hbound Ω P hC hcirc μ h hμ 0

/-- The same dyadic-orbit bound holds for a logarithmic singularity on annuli
separated from the origin, assuming existence of the zero-strength measure. -/
theorem exists_universal_singular_goodAnnulus_probability_dyadic_orbit
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {r b : ℝ} (hr : 0 < r) (hb : 0 < b) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc → ∀ (n : ℕ) (z : ℂ),
      (r * dyadicScale n) / 100 ≤ infDist (0 : ℂ)
        (annulus z (3 * (r * dyadicScale n)) (5 * (r * dyadicScale n))) →
      P {ω | ¬ IsGoodAnnulus (μ ω) (r * dyadicScale n) z a b} ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨a, ha, hbound⟩ := exists_universal_goodAnnulus_probability_dyadic_orbit
    hgrowth hγ hγ2 h₀ hμ₀ hr hb hp
  let t : ℝ := (1001 : ℝ) ^ |-(γ * α₀)|
  have ht : 1 ≤ t := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  refine ⟨a / t ^ 2, ⟨div_pos ha.1 (sq_pos_of_pos htpos), ?_⟩, ?_⟩
  · rw [div_lt_one (sq_pos_of_pos htpos)]
    nlinarith [ha.2]
  intro Ω _ P hC hcirc μ hgff hμ hEx n z hd
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hEx hgff hγ hγ2 hQ
  have hW := lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α₀)))).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ2 hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  exact (badGoodAnnulus_measure_le_of_singular_weight P
    (mul_pos hr (dyadicScale_pos n)) hd hweight).trans
      (hbound Ω P hC hcirc ν hgff hν n z)

end HarmonicBalls.Section6
