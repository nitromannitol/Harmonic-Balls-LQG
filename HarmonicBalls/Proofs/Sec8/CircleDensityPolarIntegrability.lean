import HarmonicBalls.Proofs.Sec8.CircleDensityRadial
import HarmonicBalls.Proofs.Potential.Fundamental
import HarmonicBalls.Proofs.Sec8.CircleLogPotential

/-! # Polar integrability for annular densities

The change-of-variables theorem gives the integrability needed to apply
Fubini even when an observable has a logarithmic singularity. The imported
Section 8 argument uses Leonardo Bonanno's LatticeProb formalization of the
ergodic theorem.
-/

open MeasureTheory Set Metric Filter Real
open scoped Topology

namespace HarmonicBalls

/-- An integrable function on the plane, composed with polar coordinates and
multiplied by the polar Jacobian, is integrable on the polar target. -/
theorem integrableOn_polarCoord_symm_of_integrable {f : ℂ → ℝ} (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
  have hpair : Integrable (f ∘ Complex.measurableEquivRealProd.symm) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hf
  have hj := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.symm.open_source.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn (f ∘ Complex.measurableEquivRealProd.symm)
  have hi := hj.mp hpair.integrableOn
  simp only [det_fderivPolarCoordSymm] at hi
  refine hi.congr_fun ?_ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  simp only [smul_eq_mul, Function.comp_apply,
    Complex.measurableEquivRealProd_symm_polarCoord_symm_apply,
    abs_of_pos (show 0 < p.1 from hp.1)]

/-- The radial-mixture identity remains valid for any observable integrable
against the annular density, including singular observables. -/
theorem integral_circleDensity_eq_circleAverage_of_integrable {r δ : ℝ}
    (hδ : 0 < δ) (z : ℂ) {f : ℂ → ℝ}
    (hf : Integrable (fun x => circleDensity r δ hδ z x * f x)) :
    (∫ x, circleDensity r δ hδ z x * f x) =
      2 * Real.pi * ∫ ρ in Ioi (0 : ℝ),
        ρ * circleRadiusBump r δ hδ (ρ ^ 2) * Real.circleAverage f z ρ := by
  let g : ℝ × ℝ → ℝ := fun p =>
    p.1 * circleRadiusBump r δ hδ (p.1 ^ 2) * f (circleMap z p.1 p.2)
  have hshift : Integrable (fun u : ℂ => circleDensity r δ hδ z (u + z) * f (u + z)) := by
    exact (measurePreserving_add_right volume z).integrable_comp_of_integrable hf
  have hpolar : IntegrableOn
      (fun p : ℝ × ℝ => p.1 * (circleDensity r δ hδ z
        (Complex.polarCoord.symm p + z) * f (Complex.polarCoord.symm p + z)))
      (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    integrableOn_polarCoord_symm_of_integrable hshift
  have heq : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      p.1 * (circleDensity r δ hδ z (Complex.polarCoord.symm p + z) *
        f (Complex.polarCoord.symm p + z)) = g p := by
    rintro ⟨ρ, θ⟩ ⟨hρ, hθ⟩
    change 0 < ρ at hρ
    have hcircle : Complex.polarCoord.symm (ρ, θ) + z = circleMap z ρ θ := by
      simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, add_comm]
    simp only [g, hcircle, circleDensity, circleMap_sub_center, norm_circleMap_zero,
      abs_of_pos hρ]
    ring
  have hint : IntegrableOn g (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    hpolar.congr_fun heq (measurableSet_Ioi.prod measurableSet_Ioo)
  have htrans : (∫ x, circleDensity r δ hδ z x * f x) =
      ∫ u : ℂ, circleDensity r δ hδ z (u + z) * f (u + z) := by
    simpa using (integral_sub_right_eq_self
      (fun u : ℂ => circleDensity r δ hδ z (u + z) * f (u + z)) z)
  have hpoleq : (∫ x, circleDensity r δ hδ z x * f x) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, g p := by
    rw [htrans, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    simpa only [smul_eq_mul] using heq p hp
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint
  rw [hpoleq, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  change (∫ θ in Ioo (-Real.pi) Real.pi,
    ρ * circleRadiusBump r δ hδ (ρ ^ 2) * f (circleMap z ρ θ)) = _
  rw [integral_const_mul, integral_circleMap_eq_circleAverage]
  ring

/-- The normalized version of the mixture formula under the same integrability
hypothesis. -/
theorem integral_normalized_circleDensity_eq_circleAverage_of_integrable {r δ : ℝ}
    (hδ : 0 < δ) (z : ℂ) {f : ℂ → ℝ}
    (hf : Integrable (fun x => circleDensity r δ hδ z x * f x)) :
    (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x * f x) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ *
        Real.circleAverage f z ρ := by
  have heq : (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
      circleDensity r δ hδ z x * f x) =
      (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
        ∫ x, circleDensity r δ hδ z x * f x := by
    simp_rw [mul_assoc, integral_const_mul]
  rw [heq, integral_circleDensity_eq_circleAverage_of_integrable hδ z hf,
    ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  simp only [circleDensityRadialWeight]
  ring

/-- The logarithmic kernel is integrable against a compactly supported
annular density, including when its singularity lies in the annulus. -/
theorem integrable_circleDensity_mul_log_norm_sub {r δ : ℝ} (hr : 0 ≤ r)
    (hδ : 0 < δ) (z w : ℂ) :
    Integrable (fun x => circleDensity r δ hδ z x * Real.log ‖x - w‖) := by
  have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm w
    ).integrable_smul_right_of_hasCompactSupport (circleDensity_contDiff r δ hδ z).continuous
      (circleDensity_hasCompactSupport hr hδ z)
  simpa only [smul_eq_mul, mul_comm] using h

/-- The logarithmic potential of a normalized annular density is the radial
mixture of the explicit circle potentials. -/
theorem integral_normalized_circleDensity_mul_log_norm_sub {r δ : ℝ} (hr : 0 ≤ r)
    (hδ : 0 < δ) (z w : ℂ) :
    (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x *
      Real.log ‖x - w‖) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ *
        Real.log (max ρ ‖z - w‖) := by
  rw [integral_normalized_circleDensity_eq_circleAverage_of_integrable hδ z
    (integrable_circleDensity_mul_log_norm_sub hr hδ z w)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  change circleDensityRadialWeight r δ hδ ρ *
      Real.circleAverage (fun x => Real.log ‖x - w‖) z ρ =
    circleDensityRadialWeight r δ hδ ρ * Real.log (max ρ ‖z - w‖)
  rw [circleAverage_log_norm_sub_eq_log_max (show 0 < ρ from hρ)]

/-- A narrow annular density has logarithmic potential between the potentials
of the two bounding circles, uniformly in the evaluation point. -/
theorem circleDensity_log_potential_bounds {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hηr : η < r) (hwidth : δ ≤ r * η)
    (z w : ℂ) :
    Real.log (max (r - η) ‖z - w‖) ≤
      (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x *
        Real.log ‖x - w‖) ∧
      (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x *
        Real.log ‖x - w‖) ≤ Real.log (max (r + η) ‖z - w‖) := by
  let W := circleDensityRadialWeight r δ hδ
  let L : ℝ → ℝ := fun ρ => Real.log (max ρ ‖z - w‖)
  have hW : Continuous W := by
    dsimp [W, circleDensityRadialWeight]
    exact continuous_const.mul (continuous_id.mul
      ((circleRadiusBump r δ hδ).continuous.comp (continuous_id.pow 2)))
  have hL : ContinuousOn L (Icc (r - η) (r + η)) := by
    dsimp [L]
    apply (continuous_id.max continuous_const).continuousOn.log
    intro ρ hρ
    exact ne_of_gt (lt_of_lt_of_le (by linarith) (hρ.1.trans (le_max_left _ _)))
  have hi : IntegrableOn (fun ρ => W ρ * L ρ) (Ioi (0 : ℝ)) := by
    have hc : IntegrableOn (fun ρ => W ρ * L ρ) (Icc (r - η) (r + η)) :=
      (hW.continuousOn.mul hL).integrableOn_compact isCompact_Icc
    refine hc.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
    intro ρ hρ
    by_cases hw : W ρ = 0
    · simp [hw]
    · have hnear := circleDensityRadialWeight_support_radius hr hδ hwidth
        (show 0 ≤ ρ from le_of_lt hρ.1) hw
      rw [abs_lt] at hnear
      exact (hρ.2 ⟨by linarith [hnear.1], by linarith [hnear.2]⟩).elim
  have hwi : IntegrableOn W (Ioi (0 : ℝ)) := circleDensityRadialWeight_integrableOn hr.le hδ
  have hwm : (∫ ρ in Ioi (0 : ℝ), W ρ) = 1 := circleDensityRadialWeight_integral hr.le hδ
  rw [integral_normalized_circleDensity_mul_log_norm_sub hr.le hδ z w]
  constructor
  · calc
      _ = ∫ ρ in Ioi (0 : ℝ), W ρ * Real.log (max (r - η) ‖z - w‖) := by
        rw [integral_mul_const, hwm, one_mul]
      _ ≤ ∫ ρ in Ioi (0 : ℝ), W ρ * L ρ := by
        apply integral_mono_ae (hwi.mul_const _) hi
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro ρ hρ
        by_cases hw : W ρ = 0
        · simp [hw]
        · apply mul_le_mul_of_nonneg_left _ (circleDensityRadialWeight_nonneg r δ hr.le hδ hρ.le)
          have hn := circleDensityRadialWeight_support_radius hr hδ hwidth hρ.le hw
          rw [abs_lt] at hn
          apply Real.log_le_log
          · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
          · exact max_le_max_right _ (by linarith [hn.1])
  · calc
      (∫ ρ in Ioi (0 : ℝ), W ρ * L ρ) ≤
          ∫ ρ in Ioi (0 : ℝ), W ρ * Real.log (max (r + η) ‖z - w‖) := by
        apply integral_mono_ae hi (hwi.mul_const _)
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro ρ hρ
        by_cases hw : W ρ = 0
        · simp [hw]
        · apply mul_le_mul_of_nonneg_left _ (circleDensityRadialWeight_nonneg r δ hr.le hδ hρ.le)
          have hn := circleDensityRadialWeight_support_radius hr hδ hwidth hρ.le hw
          rw [abs_lt] at hn
          apply Real.log_le_log
          · exact lt_of_lt_of_le hρ (le_max_left _ _)
          · exact max_le_max_right _ (by linarith [hn.2])
      _ = _ := by rw [integral_mul_const, hwm, one_mul]

/-- The change in a circle's logarithmic potential between two radii is
bounded by their logarithmic separation, uniformly in the other point. -/
theorem log_max_sub_log_max_le {a b d : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (max b d) - Real.log (max a d) ≤ Real.log b - Real.log a := by
  by_cases hda : d ≤ a
  · rw [max_eq_left hda, max_eq_left (hda.trans hab)]
  · have had : a ≤ d := le_of_not_ge hda
    by_cases hdb : d ≤ b
    · rw [max_eq_right had, max_eq_left hdb]
      have h := Real.log_le_log ha had
      linarith
    · have hbd : b ≤ d := le_of_not_ge hdb
      rw [max_eq_right had, max_eq_right hbd]
      have h := Real.log_le_log ha hab
      linarith

/-- The normalized annular logarithmic potential differs from the target
circle potential by at most the logarithmic separation of the bounding
circles, uniformly in the point at which it is evaluated. -/
theorem abs_circleDensity_log_potential_sub_circle_le {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hηr : η < r) (hwidth : δ ≤ r * η) (z w : ℂ) :
    |(∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x *
      Real.log ‖x - w‖) - Real.log (max r ‖z - w‖)| ≤
      Real.log (r + η) - Real.log (r - η) := by
  have hη : 0 < η := by nlinarith
  have hb := circleDensity_log_potential_bounds hr hδ hηr hwidth z w
  have hlower : Real.log (max (r - η) ‖z - w‖) ≤ Real.log (max r ‖z - w‖) := by
    apply Real.log_le_log
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · exact max_le_max_right _ (by linarith)
  have hupper : Real.log (max r ‖z - w‖) ≤ Real.log (max (r + η) ‖z - w‖) := by
    apply Real.log_le_log
    · exact lt_of_lt_of_le hr (le_max_left _ _)
    · exact max_le_max_right _ (by linarith)
  have hspan := log_max_sub_log_max_le (a := r - η) (b := r + η)
    (d := ‖z - w‖) (by linarith) (by linarith)
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

/-- Shrinking annular densities have logarithmic potentials converging
uniformly, over both the center and evaluation point, to the circle potential. -/
theorem circleDensity_log_potential_tendsto_uniformly {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ z w : ℂ,
      |(∫ x, (∫ y, circleDensity r (circleDensityWidth r η n)
          (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
          circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x *
          Real.log ‖x - w‖) - Real.log (max r ‖z - w‖)| < ε := by
  have hηlim : Tendsto (fun n : ℕ => η / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hp : Tendsto (fun n : ℕ => r + η / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).add hηlim
  have hm : Tendsto (fun n : ℕ => r - η / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).sub hηlim
  have hspan : Tendsto (fun n : ℕ => Real.log (r + η / ((n : ℝ) + 1)) -
      Real.log (r - η / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ((Real.continuousAt_log hr.ne').tendsto.comp hp).sub
      ((Real.continuousAt_log hr.ne').tendsto.comp hm)
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, η / ((n : ℝ) + 1) < r :=
    (tendsto_order.1 hηlim).2 r hr
  have herror : ∀ᶠ n : ℕ in atTop,
      Real.log (r + η / ((n : ℝ) + 1)) -
        Real.log (r - η / ((n : ℝ) + 1)) < ε := (tendsto_order.1 hspan).2 ε hε
  have hgoal : ∀ᶠ n : ℕ in atTop, ∀ z w : ℂ,
      |(∫ x, (∫ y, circleDensity r (circleDensityWidth r η n)
          (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
          circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z x *
          Real.log ‖x - w‖) - Real.log (max r ‖z - w‖)| < ε := by
    filter_upwards [hsmall, herror] with n hsmalln herrorn
    intro z w
    have hwidth : circleDensityWidth r η n ≤ r * (η / ((n : ℝ) + 1)) := by
      simp [circleDensityWidth, div_eq_mul_inv, mul_assoc]
    exact (abs_circleDensity_log_potential_sub_circle_le hr
      (circleDensityWidth_pos hr hη n) hsmalln hwidth z w).trans_lt herrorn
  exact eventually_atTop.1 hgoal

end HarmonicBalls
