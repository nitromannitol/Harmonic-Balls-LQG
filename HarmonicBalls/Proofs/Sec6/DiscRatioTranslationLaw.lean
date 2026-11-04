import HarmonicBalls.Proofs.Sec6.DiscRecurrenceVolumeGrowth
import HarmonicBalls.Proofs.Sec6.LQGTranslationCovariance

/-! # Translation invariance of disc potential ratios

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
Volume growth gives the continuity required to transfer the law of the
translated measure to the Green-potential ratio.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- At a fixed positive radius, disc potential ratios have the same law at
all centres under volume growth and affine field invariance. -/
theorem identDistrib_fineSupportDisc_ratio_translate_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio (ball 0 r) (sphere 0 (r / 4)) (μ ω))
      (fun ω => greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) (μ ω)) P P := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hs := hAff h 1 one_ne_zero c
  have hsμ := isLQGMeasureOfField_translate h hμ c
  obtain ⟨_, _, _, hko, _⟩ := fineSupportDisc_geometry 0 hr
  have hd := identDistrib_greenPotentialExtremaRatio
    (identDistrib_translateMeasure h hμ hAff c) isOpen_ball isBounded_ball
    (ae_continuous_lqg_discPotential_extrema_of_volumeGrowth hgrowth hγ hγ2 hQ h hμ 0 hr
      (hko.trans subset_closure))
    (ae_continuous_lqg_discPotential_extrema_of_volumeGrowth hgrowth hγ hγ2 hQ hs hsμ 0 hr
      (hko.trans subset_closure))
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [affineMeasure, div_one, greenPotentialExtremaRatio]
  rw [greenPotential_extrema_ratio_smul_measure _ _ _ _
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top]
  have ht := greenPotentialExtremaRatio_translate (O := ball (0 : ℂ) r) isOpen_ball
    (sphere 0 (r / 4)) (μ ω) c
  have hb : (fun z : ℂ => z + c) '' ball 0 r = ball c r := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
    · intro hz
      exact ⟨z - c, by simpa only [mem_ball, dist_eq_norm, sub_zero] using hz,
        sub_add_cancel z c⟩
  have hk : (fun z : ℂ => z + c) '' sphere 0 (r / 4) = sphere c (r / 4) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_sphere, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
    · intro hz
      exact ⟨z - c, by simpa only [mem_sphere, dist_eq_norm, sub_zero] using hz,
        sub_add_cancel z c⟩
  rw [hb, hk] at ht
  exact ht.symm


/-- The lower-tail probability of the disc ratio is independent of its centre. -/
theorem fineSupportDisc_ratio_lower_tail_eq_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (c d : ℂ) {r : ℝ} (hr : 0 < r) (a : ℝ) :
    P {ω | greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) (μ ω) < a} =
      P {ω | greenPotentialExtremaRatio (ball d r) (sphere d (r / 4)) (μ ω) < a} := by
  have hc := identDistrib_fineSupportDisc_ratio_translate_of_volumeGrowth
    hgrowth hγ hγ2 h hμ hAff c hr
  have hd := identDistrib_fineSupportDisc_ratio_translate_of_volumeGrowth
    hgrowth hγ hγ2 h hμ hAff d hr
  exact (hc.symm.trans hd).measure_mem_eq measurableSet_Iio

end HarmonicBalls.Section6
