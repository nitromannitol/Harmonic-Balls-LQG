import HarmonicBalls.Proofs.Sec8.CircleDensityPolarIntegrability

/-! # Continuous observables of shrinking annuli

Normalized annular densities converge against continuous observables to the
corresponding circle average. The imported Section 8 argument uses Leonardo
Bonanno's LatticeProb formalization of the ergodic theorem.
-/

open MeasureTheory Set Metric Filter Real
open scoped Topology

namespace HarmonicBalls

/-- A normalized radial weight integrates a continuous function close to its
value at the limiting radius when the weight is supported nearby. -/
theorem circleDensityRadialWeight_integral_sub_le {r δ η ε : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hclose : ∀ ρ, |ρ - r| < η → |g ρ - g r| ≤ ε) :
    |(∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * g ρ) - g r| ≤ ε := by
  let W := circleDensityRadialWeight r δ hδ
  have hW : Continuous W := by
    dsimp [W, circleDensityRadialWeight]
    exact continuous_const.mul (continuous_id.mul
      ((circleRadiusBump r δ hδ).continuous.comp (continuous_id.pow 2)))
  have hi : IntegrableOn (fun ρ => W ρ * g ρ) (Ioi (0 : ℝ)) := by
    have hc : IntegrableOn (fun ρ => W ρ * g ρ) (Icc (r - η) (r + η)) :=
      (hW.mul hg).continuousOn.integrableOn_compact isCompact_Icc
    refine hc.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
    intro ρ hρ
    by_cases hw : W ρ = 0
    · simp [hw]
    · have hn := circleDensityRadialWeight_support_radius hr hδ hwidth
        (show 0 ≤ ρ from le_of_lt hρ.1) hw
      rw [abs_lt] at hn
      exact (hρ.2 ⟨by linarith [hn.1], by linarith [hn.2]⟩).elim
  have hwi : IntegrableOn W (Ioi (0 : ℝ)) := circleDensityRadialWeight_integrableOn hr.le hδ
  have hwm : (∫ ρ in Ioi (0 : ℝ), W ρ) = 1 := circleDensityRadialWeight_integral hr.le hδ
  have hl : g r - ε ≤ ∫ ρ in Ioi (0 : ℝ), W ρ * g ρ := by
    calc
      _ = ∫ ρ in Ioi (0 : ℝ), W ρ * (g r - ε) := by
        rw [integral_mul_const, hwm, one_mul]
      _ ≤ _ := by
        apply integral_mono_ae (hwi.mul_const _) hi
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro ρ hρ
        by_cases hw : W ρ = 0
        · simp [hw]
        · apply mul_le_mul_of_nonneg_left _ (circleDensityRadialWeight_nonneg r δ hr.le hδ hρ.le)
          have h := hclose ρ (circleDensityRadialWeight_support_radius hr hδ hwidth hρ.le hw)
          rw [abs_le] at h
          linarith [h.1]
  have hu : (∫ ρ in Ioi (0 : ℝ), W ρ * g ρ) ≤ g r + ε := by
    calc
      _ ≤ ∫ ρ in Ioi (0 : ℝ), W ρ * (g r + ε) := by
        apply integral_mono_ae hi (hwi.mul_const _)
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro ρ hρ
        by_cases hw : W ρ = 0
        · simp [hw]
        · apply mul_le_mul_of_nonneg_left _ (circleDensityRadialWeight_nonneg r δ hr.le hδ hρ.le)
          have h := hclose ρ (circleDensityRadialWeight_support_radius hr hδ hwidth hρ.le hw)
          rw [abs_le] at h
          linarith [h.2]
      _ = _ := by rw [integral_mul_const, hwm, one_mul]
  rw [abs_le]
  constructor <;> linarith

/-- Integration against shrinking normalized annular densities converges to
circle averaging for every continuous real-valued observable. -/
theorem circleDensity_integral_tendsto_circleAverage {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (z : ℂ) {f : ℂ → ℝ} (hf : Continuous f) :
    Tendsto (fun n => ∫ x, (∫ y, circleDensity r (circleDensityWidth r η n)
      (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
      circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x * f x)
      atTop (𝓝 (Real.circleAverage f z r)) := by
  have hg : Continuous (Real.circleAverage f z) := hf.circleAverage
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨κ, hκ, hk⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε / 2) (half_pos hε)
  have hlim : Tendsto (fun n : ℕ => η / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.1 hlim).2 κ hκ)
  refine ⟨N, fun n hn => ?_⟩
  rw [integral_normalized_circleDensity_eq_circleAverage hr.le
    (circleDensityWidth_pos hr hη n) z hf, Real.dist_eq]
  have hwidth : circleDensityWidth r η n ≤ r * (η / ((n : ℝ) + 1)) := by
    simp [circleDensityWidth, div_eq_mul_inv, mul_assoc]
  have hb := circleDensityRadialWeight_integral_sub_le hr
    (circleDensityWidth_pos hr hη n) hwidth (Real.circleAverage f z) hg
    (ε := ε / 2) (by
      intro ρ hρ
      have hd : dist ρ r < κ := by
        rw [Real.dist_eq]
        exact hρ.trans (hN n hn)
      have := hk hd
      rw [Real.dist_eq] at this
      exact this.le)
  exact hb.trans_lt (half_lt_self hε)

/-- The continuous whole-plane normalization term converges under annular
approximation. -/
theorem circleDensity_normalization_tendsto {r η : ℝ} (hr : 0 < r) (hη : 0 < η)
    (z : ℂ) :
    Tendsto (fun n => ∫ x, (∫ y, circleDensity r (circleDensityWidth r η n)
      (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
      circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x *
      wholePlaneNormalization x) atTop (𝓝 (Real.circleAverage wholePlaneNormalization z r)) :=
  circleDensity_integral_tendsto_circleAverage hr hη z continuous_wholePlaneNormalization

/-- Covariances of an annular pairing and a circle average converge to the
covariance of the two circle averages. -/
theorem circleDensity_circle_covariance_tendsto {r η s : ℝ} (hr : 0 < r)
    (hη : 0 < η) (hs : 0 < s) (z w : ℂ) :
    Tendsto (fun n => wholePlaneGFFCov
      (.pairing (fun x => (∫ y, circleDensity r (circleDensityWidth r η n)
        (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
        circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x))
      (.circle s w)) atTop (𝓝 (wholePlaneGFFCov (.circle r z) (.circle s w))) := by
  exact circleDensity_integral_tendsto_circleAverage hr hη z
    (continuous_circleAverage_wholePlaneCov hs w)

/-- A shrinking annulus integrates the logarithmic potential of a fixed circle
in the limit exactly as another circle does. -/
theorem circleDensity_circle_log_potential_tendsto {r η s : ℝ} (hr : 0 < r)
    (hη : 0 < η) (hs : 0 < s) (z w : ℂ) :
    Tendsto (fun n => ∫ x, (∫ y, circleDensity r (circleDensityWidth r η n)
      (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
      circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x *
      Real.log (max s ‖w - x‖)) atTop
      (𝓝 (Real.circleAverage (fun x => Real.log (max s ‖w - x‖)) z r)) := by
  have hc : Continuous (fun x : ℂ => Real.log (max s ‖w - x‖)) := by
    exact (continuous_const.max ((continuous_const.sub continuous_id).norm)).log
      (fun x => ne_of_gt (lt_of_lt_of_le hs (le_max_left _ _)))
  exact circleDensity_integral_tendsto_circleAverage hr hη z hc

end HarmonicBalls
