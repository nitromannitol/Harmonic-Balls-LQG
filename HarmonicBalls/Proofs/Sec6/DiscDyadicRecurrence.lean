import HarmonicBalls.Proofs.Sec6.DiscRatioTranslationLaw
import HarmonicBalls.Proofs.Sec6.DyadicMeasureScalingLaw

/-! # Fine support along dyadic scales

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Disc continuity follows from
volume growth and dyadic coordinate change follows from the LQG limit.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter MarkovProcess
open scoped ENNReal Topology

universe u

/-- Disc potential ratios at radii differing by a power of two have the same
law under volume growth and affine field invariance. -/
theorem identDistrib_fineSupportDisc_ratio_dyadic
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) (m : ℕ) {r : ℝ} (hr : 0 < r) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio (ball 0 r) (sphere 0 (r / 4)) (μ ω))
      (fun ω => greenPotentialExtremaRatio (ball 0 ((2 : ℝ) ^ m * r))
        (sphere 0 (((2 : ℝ) ^ m * r) / 4)) (μ ω)) P P := by
  let k : ℝ := (2 : ℝ) ^ m
  have hk : 0 < k := by dsimp [k]; positivity
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hs := hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hsμ := isLQGMeasureOfField_normalizedPullback_dyadic h hγ.ne' hμ m
  have hsμ' : IsLQGMeasureOfField P γ 0 (affineCircle hcirc (k : ℂ) 0)
      (fun ω => normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω)) := by
    have hc : affineCircle hcirc (k : ℂ) 0 =
        (fun ω r z => hcirc ω (k * r) (k • z) - hcirc ω k 0) := by
      funext ω r z
      simp [affineCircle, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, Complex.real_smul]
    rw [hc]
    exact hsμ
  obtain ⟨_, _, _, hko, _⟩ := fineSupportDisc_geometry 0 hr
  have hd := identDistrib_greenPotentialExtremaRatio
    (identDistrib_normalizedPullback_dyadic hγ h hμ hAff m) isOpen_ball isBounded_ball
    (ae_continuous_lqg_discPotential_extrema_of_volumeGrowth hgrowth hγ hγ2 hQ h hμ 0 hr
      (hko.trans subset_closure))
    (ae_continuous_lqg_discPotential_extrema_of_volumeGrowth hgrowth hγ hγ2 hQ hs hsμ' 0 hr
      (hko.trans subset_closure))
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  have ht := greenPotentialExtremaRatio_dilation (O := ball (0 : ℂ) r)
    isOpen_ball isBounded_ball (sphere 0 (r / 4)) (μ ω) hk
  rw [Metric.smul_image_ball hk.ne', Metric.smul_image_sphere hk.ne'] at ht
  simp only [smul_zero, Real.norm_eq_abs, abs_of_pos hk, ← mul_div_assoc] at ht
  simp only [normalizedPullbackMeasure, greenPotentialExtremaRatio]
  rw [greenPotential_extrema_ratio_smul_measure _ _ _ _
    (by positivity) ENNReal.ofReal_ne_top]
  exact ht.symm


/-- Along inverse dyadic scales, disc ratios recur above a positive threshold
at almost every centre. -/
theorem ae_ae_fineSupportDisc_ratio_recurs_dyadic
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ᵐ c ∂(volume : Measure ℂ), ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (ball c (dyadicScale n))
        (sphere c (dyadicScale n / 4)) (μ ω) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  apply ae_ae_frequently_pos_of_equal_lower_tails_of_aemeasurable P volume
    (fun n p => greenPotentialExtremaRatio (ball p.2 (dyadicScale n))
      (sphere p.2 (dyadicScale n / 4)) (μ p.1))
  · intro n
    exact aemeasurable_fineSupportDisc_ratio_joint_of_volumeGrowth hgrowth hγ hγ2 h hμ
      (dyadicScale_pos n)
  · filter_upwards [] with c
    filter_upwards [ae_fineSupportDisc_ratio_pos_of_volumeGrowth hgrowth hγ hγ2 hQ h hμ] with ω hp
    exact hp c _ (dyadicScale_pos 0)
  · filter_upwards [] with c n a
    have hs : (2 : ℝ) ^ n * dyadicScale n = 1 := by
      simpa only [zero_add, dyadicScale, pow_zero] using dyadicScale_shift n 0
    have hn := (identDistrib_fineSupportDisc_ratio_dyadic hgrowth hγ hγ2 h hμ hAff n
      (dyadicScale_pos n)).symm.trans
      (identDistrib_fineSupportDisc_ratio_translate_of_volumeGrowth hgrowth hγ hγ2 h hμ
        hAff c (dyadicScale_pos n))
    rw [hs] at hn
    have h0 := identDistrib_fineSupportDisc_ratio_translate_of_volumeGrowth
      hgrowth hγ hγ2 h hμ hAff c (dyadicScale_pos 0)
    have heq := (hn.symm.trans h0).measure_mem_eq (measurableSet_Iio : MeasurableSet (Iio a))
    simpa only [dyadicScale, pow_zero, Set.preimage, Set.mem_Iio] using heq

/-- Volume growth and affine GFF invariance imply Brownian fine support at
almost every centre, using dyadic scales. -/
theorem ae_ae_lqg_fine_support_of_disc_dyadic
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → (μ ω) (ball x ε \ E) = 0 →
      ∀ᵐ path ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ path = 0 := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have ht : Tendsto dyadicScale atTop (𝓝 0) :=
    tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds
  have ha : Antitone dyadicScale := by
    intro m n hmn
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  filter_upwards [ae_ae_fineSupportDisc_ratio_recurs_dyadic hgrowth hγ hγ2 h hμ hAff,
    ae_fineSupportDisc_centre_hitting_union_of_volumeGrowth hgrowth hγ hγ2 hQ h hμ, hμ] with ω hrec hhit hμω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  filter_upwards [hrec] with x hrecx
  intro ε hε E hE hmass
  apply ae_instant_hit_of_recurrent_lower_bounds
    (measure_ball_ne_top (μ := μ ω) (x := x) (r := ε)) ht ha hrecx ?_
    (planarBrownian_compact_union_zeroOne x) hE hmass
  intro K hK hmono hfullK
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with n hn
  exact hhit x _ ε (dyadicScale_pos n) hn.le K hK hmono hfullK

end HarmonicBalls.Section6
