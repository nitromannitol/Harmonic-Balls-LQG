import HarmonicBalls.Steps.Sec11.WeylLocalCurveLength

/-! # Infinitesimal Weyl length

Local comparisons bound slopes of cumulative length along a unit-speed curve.
-/

namespace HarmonicBalls

open Set Filter
open scoped ENNReal Topology

/-- Near an interior parameter, slopes of cumulative shifted length are
bounded by nearby exponential weights. -/
theorem IsEuclideanLengthMetric.weylScaling_cumulative_slope_bounds
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    {p : ℝ → ℂ} {T t₀ : ℝ} (hp : IsLengthParametrized D p T)
    (ht₀ : t₀ ∈ Icc 0 T)
    (hE : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Icc 0 T, t ≠ t₀ → |t - t₀| < r →
      let L : ℝ → ℝ := fun s => (curveLength
        (fun u v => (weylScaling D ξ f u v).toReal) p 0 s).toReal
      Real.exp (ξ * f (p t₀) - ε) ≤ slope L t₀ t ∧
        slope L t₀ t ≤ Real.exp (ξ * f (p t₀) + ε) := by
  let E : ℂ → ℂ → ℝ := fun u v => (weylScaling D ξ f u v).toReal
  let L : ℝ → ℝ := fun s => (curveLength E p 0 s).toReal
  have hED : ∀ u v, E u v ≤ D u v := fun u v =>
    (weylScaling_negative_bump_real_bounds hD hξ f hl hu (hD.weylScaling_zero ξ) u v).2.2
  obtain ⟨r, hr, hcomp⟩ := hD.weylScaling_local_segment_comparison hξ f hf hl hu hp ht₀ hε
  refine ⟨r, hr, ?_⟩
  intro t ht hne hnear
  change Real.exp (ξ * f (p t₀) - ε) ≤ slope L t₀ t ∧
    slope L t₀ t ≤ Real.exp (ξ * f (p t₀) + ε)
  have hseg (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
      (hna : |a - t₀| < r) (hnb : |b - t₀| < r) :
      Real.exp (ξ * f (p t₀) - ε) * (b - a) ≤ L b - L a ∧
      L b - L a ≤ Real.exp (ξ * f (p t₀) + ε) * (b - a) := by
    have hc := hcomp a b ha hab hb hna hnb
    have hfin : curveLength E p a b ≠ ∞ := (lt_of_le_of_lt hc.2 ENNReal.ofReal_lt_top).ne
    have hleft := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfin).2 hc.1
    have hright := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).2 hc.2
    rw [hE.cumulative_curveLength_sub hp hED ha hab hb]
    constructor
    · simpa only [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr hab))] using hleft
    · simpa only [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr hab))] using hright
  have hzero : |t₀ - t₀| < r := by simpa using hr
  rw [slope_fun_def_field]
  change Real.exp (ξ * f (p t₀) - ε) ≤ (L t - L t₀) / (t - t₀) ∧
    (L t - L t₀) / (t - t₀) ≤ Real.exp (ξ * f (p t₀) + ε)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh := hseg t t₀ ht.1 hlt.le ht₀.2 hnear hzero
    have hneg : t - t₀ < 0 := sub_neg.mpr hlt
    constructor
    · apply (le_div_iff_of_neg hneg).2
      nlinarith [hh.1]
    · apply (div_le_iff_of_neg hneg).2
      nlinarith [hh.2]
  · have hh := hseg t₀ t ht₀.1 hgt.le ht.2 hzero hnear
    have hpos : 0 < t - t₀ := sub_pos.mpr hgt
    exact ⟨(le_div_iff₀ hpos).2 hh.1, (div_le_iff₀ hpos).2 hh.2⟩

/-- The derivative of cumulative shifted length is the Weyl weight along
the original unit-speed curve. -/
theorem IsEuclideanLengthMetric.hasDerivAt_weylScaling_curveLength
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    {p : ℝ → ℂ} {T t₀ : ℝ} (hp : IsLengthParametrized D p T)
    (ht₀ : t₀ ∈ Ioo 0 T)
    (hE : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal)) :
    HasDerivAt (fun s => (curveLength
      (fun u v => (weylScaling D ξ f u v).toReal) p 0 s).toReal)
      (Real.exp (ξ * f (p t₀))) t₀ := by
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhds]
  intro η hη
  let w := ξ * f (p t₀)
  have hcont : ContinuousAt (fun u : ℝ => Real.exp (w + u)) 0 :=
    Real.continuous_exp.continuousAt.comp (continuous_const.add continuous_id).continuousAt
  have hevent := (Metric.tendsto_nhds.mp hcont) η hη
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hevent
  let ε := δ / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hplus : |Real.exp (w + ε) - Real.exp w| < η := by
    have hsmall : dist ε (0 : ℝ) < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε]
      dsimp [ε]
      linarith
    have h := hδbound (y := ε) hsmall
    simpa [Real.dist_eq] using h
  have hminus : |Real.exp (w - ε) - Real.exp w| < η := by
    have hsmall : dist (-ε) (0 : ℝ) < δ := by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hε]
      dsimp [ε]
      linarith
    have h := hδbound (y := -ε) hsmall
    simpa [Real.dist_eq, sub_eq_add_neg] using h
  obtain ⟨r, hr, hbound⟩ := hD.weylScaling_cumulative_slope_bounds hξ f hf hl hu hp
    ⟨ht₀.1.le, ht₀.2.le⟩ hE hε
  have ht₀pos : 0 < t₀ := ht₀.1
  have ht₀T : 0 < T - t₀ := sub_pos.mpr ht₀.2
  let ρ := min r (min t₀ (T - t₀)) / 2
  have hmin : 0 < min r (min t₀ (T - t₀)) := lt_min hr (lt_min ht₀pos ht₀T)
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρr : ρ < r := by
    have h := min_le_left r (min t₀ (T - t₀))
    dsimp [ρ]
    linarith
  have hρ0 : ρ < t₀ := by
    have h := (min_le_right r (min t₀ (T - t₀))).trans (min_le_left t₀ (T - t₀))
    dsimp [ρ]
    linarith
  have hρT : ρ < T - t₀ := by
    have h := (min_le_right r (min t₀ (T - t₀))).trans (min_le_right t₀ (T - t₀))
    dsimp [ρ]
    linarith
  have hball : ∀ᶠ t in 𝓝[≠] t₀, t ∈ Metric.ball t₀ ρ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds t₀ hρ)
  filter_upwards [self_mem_nhdsWithin, hball] with t hne ht
  have hne' : t ≠ t₀ := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
  have htnear : |t - t₀| < ρ := by simpa only [Metric.mem_ball, Real.dist_eq] using ht
  have htmem : t ∈ Icc 0 T := by
    have h := abs_lt.mp htnear
    constructor <;> linarith
  have hs := hbound t htmem hne' (lt_trans htnear hρr)
  rw [Real.dist_eq, abs_lt]
  have hplus' := abs_lt.mp hplus
  have hminus' := abs_lt.mp hminus
  change -η < _ - Real.exp w ∧ _ - Real.exp w < η
  constructor <;> linarith [hs.1, hs.2, hplus'.2, hminus'.1]

/-- The real length of each shifted segment is the integral of the Weyl
weight along the original unit-speed curve. -/
theorem IsEuclideanLengthMetric.weylScaling_curveLength_toReal_eq_integral
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    {p : ℝ → ℂ} {T a b : ℝ} (hp : IsLengthParametrized D p T)
    (hE : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal))
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (curveLength (fun u v => (weylScaling D ξ f u v).toReal) p a b).toReal =
      ∫ t in a..b, Real.exp (ξ * f (p t)) := by
  let E : ℂ → ℂ → ℝ := fun u v => (weylScaling D ξ f u v).toReal
  have hED : ∀ u v, E u v ≤ D u v := fun u v =>
    (weylScaling_negative_bump_real_bounds hD hξ f hl hu (hD.weylScaling_zero ξ) u v).2.2
  have hcont : ContinuousOn (fun t => (curveLength E p 0 t).toReal) (Icc a b) :=
    (hE.cumulative_curveLength_lipschitzOn hp hED).continuousOn.mono (Icc_subset_Icc ha hb)
  have hwcont : ContinuousOn (fun t => Real.exp (ξ * f (p t))) (Icc a b) :=
    (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (hf.comp_continuousOn hp.2.1))).mono (Icc_subset_Icc ha hb)
  have hint : IntervalIntegrable (fun t => Real.exp (ξ * f (p t))) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hwcont
  have hderiv : ∀ t ∈ Ioo a b, HasDerivAt (fun s => (curveLength E p 0 s).toReal)
      (Real.exp (ξ * f (p t))) t := by
    intro t ht
    exact hD.hasDerivAt_weylScaling_curveLength hξ f hf hl hu hp
      ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩ hE
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint
  rw [hE.cumulative_curveLength_sub hp hED ha hab hb] at h
  exact h.symm

/-- The shifted length of each segment equals its Weyl cost. -/
theorem IsEuclideanLengthMetric.weylScaling_curveLength_eq_cost
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ξ c : ℝ} (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f)
    (hl : ∀ z, c ≤ f z) (hu : ∀ z, f z ≤ 0)
    {p : ℝ → ℂ} {T a b : ℝ} (hp : IsLengthParametrized D p T)
    (hE : IsEuclideanLengthMetric (fun u v => (weylScaling D ξ f u v).toReal))
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    curveLength (fun u v => (weylScaling D ξ f u v).toReal) p a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.exp (ξ * f (p t))) := by
  let E : ℂ → ℂ → ℝ := fun u v => (weylScaling D ξ f u v).toReal
  have hED : ∀ u v, E u v ≤ D u v := fun u v =>
    (weylScaling_negative_bump_real_bounds hD hξ f hl hu (hD.weylScaling_zero ξ) u v).2.2
  have hfin : curveLength E p a b ≠ ∞ :=
    (lt_of_le_of_lt (curveLength_le_of_lengthParametrized_of_le hp hED ha hab hb)
      ENNReal.ofReal_lt_top).ne
  have hwcont : ContinuousOn (fun t => Real.exp (ξ * f (p t))) (Icc a b) :=
    (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (hf.comp_continuousOn hp.2.1))).mono (Icc_subset_Icc ha hb)
  have hreal := hD.weylScaling_curveLength_toReal_eq_integral hξ f hf hl hu hp hE ha hab hb
  have hconvert := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (hwcont.integrableOn_Icc (μ := MeasureTheory.volume)) (Filter.Eventually.of_forall fun t => (Real.exp_nonneg _))
  have hinterval : (∫ t in a..b, Real.exp (ξ * f (p t))) =
      ∫ t in Icc a b, Real.exp (ξ * f (p t)) := by
    rw [intervalIntegral.integral_of_le hab,
      MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume))]
  rw [← ENNReal.ofReal_toReal hfin, hreal, hinterval, hconvert]


end HarmonicBalls
