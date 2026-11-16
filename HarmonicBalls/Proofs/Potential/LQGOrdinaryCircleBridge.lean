import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge

/-! # Continuous circle averages of the whole-plane field

A measurable continuous version of the circle averages has the Gaussian law
and covariance of the normalized whole-plane field.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- A measurable continuous circle-average version has the normalized GFF law,
with agreement at all positive circles on one event. -/
theorem IsWholePlaneGFF.exists_measurable_gff_circle_average
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ H : ℝ → ℂ → Ω → ℝ,
      LQGDimension.IsGFFCircleAverage H P ∧
      (∀ r z, Measurable (H r z)) ∧
      ∀ᵐ ω ∂P, ∀ r, 0 < r → ∀ z, H r z ω = hcirc ω r z := by
  obtain ⟨F, hFm, _, hF⟩ := hh.exists_measurable_continuous_circle_version
  obtain ⟨K, hK, _, hKraw⟩ :=
    LQGMetric.CircleAvg.exists_isGFFCircleAverage_normalized hh.reconstructedGFF_normalized
  have hKactual : ∀ r, 0 < r → ∀ z, K r z =ᵐ[P] fun ω => hcirc ω r z := by
    intro r hr z
    filter_upwards [hKraw r hr z, hh.ae_circleAvg_reconstructedGFF hr z] with ω hk ha
    exact hk.trans ha.symm
  let H : ℝ → ℂ → Ω → ℝ := fun r z ω => circleProfile (F ω) r z
  have heq : ∀ r, 0 < r → ∀ z, H r z =ᵐ[P] K r z := by
    intro r hr z
    simpa only [H, circleProfile, dite_eq_left hr, Function.comp_def, id_eq] using
      (hF (⟨r, hr⟩, z)).trans (hKactual r hr z).symm
  refine ⟨H, ⟨hK.isProbabilityMeasure, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hK.isGaussianProcess.congr fun p => (heq p.1 p.1.2 p.2).symm
  · intro r hr z
    rw [integral_congr_ae (heq r hr z)]
    exact hK.integral_eq_zero r hr z
  · intro r hr s hs z w
    rw [LQGMetric.CircleAvg.covariance_congr_ae (heq r hr z) (heq s hs w)]
    exact hK.covariance_eq r hr s hs z w
  · intro r hr ω
    simpa only [H, circleProfile, dite_eq_left hr, Function.comp_def, id_eq] using
      (F ω).continuous.comp (continuous_const.prodMk continuous_id)
  · intro r z
    by_cases hr : 0 < r
    · simpa only [H, circleProfile, dite_eq_left hr, Function.comp_def, id_eq] using
        (ContinuousMap.measurable_eval (⟨r, hr⟩, z)).comp hFm
    · simpa only [H, circleProfile, dite_eq_right hr] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  · filter_upwards [hh.ae_circle_map_eq_raw hF] with ω hω r hr z
    simpa only [H, circleProfile, dite_eq_left hr] using hω (⟨r, hr⟩, z)

/-- Subcriticality admits two moments strictly between one and the critical moment. -/
theorem exists_lqg_moment_parameters {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ p q : ℝ, 1 < p ∧ p < q ∧ q < 4 / γ ^ 2 := by
  have hs : 0 < γ ^ 2 := sq_pos_of_pos hγ
  have hfour : γ ^ 2 < 4 := by nlinarith
  have ht : (1 : ℝ) < 4 / γ ^ 2 := by rw [lt_div_iff₀ hs]; linarith
  obtain ⟨q, hq1, hq⟩ := exists_between ht
  obtain ⟨p, hp, hpq⟩ := exists_between hq1
  exact ⟨p, q, hp, hpq, hq⟩

/-- A finite compact-center power bound transfers across agreement of positive
circle averages, including zero-radius balls. -/
theorem lqgApprox_ball_power_transfer_of_circle_eq
    {γ κ R : ℝ} {H h : ℝ → ℂ → ℝ} {C : ℝ≥0∞}
    (hC : C < ⊤)
    (heq : ∀ r, 0 < r → ∀ z, H r z = h r z)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ k : ℕ,
      lqgApprox γ H (dyadicScale k) (ball z s) ≤ C * ENNReal.ofReal (s ^ κ)) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ,
      0 ≤ s → s ≤ 1 → lqgApprox γ h (dyadicScale k) (ball z s) ≤
        ENNReal.ofReal (C₁ * s ^ κ) := by
  refine ⟨C.toReal + 1, by positivity, ?_⟩
  intro k z hz s hs hs1
  by_cases hs0 : s = 0
  · subst s
    simp
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have he : lqgApprox γ H (dyadicScale k) = lqgApprox γ h (dyadicScale k) := by
    unfold lqgApprox
    congr 1
    funext w
    rw [heq _ (dyadicScale_pos k) w]
  rw [← he]
  refine (hbound z hz s hspos hs1 k).trans ?_
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C.toReal + 1)]
  have hc : C ≤ ENNReal.ofReal (C.toReal + 1) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hC.ne]
    simp
  gcongr

end HarmonicBalls
