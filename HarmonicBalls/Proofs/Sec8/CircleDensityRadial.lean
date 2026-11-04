import HarmonicBalls.Proofs.Sec8.CircleDensityLocal

/-! # Radial mass of annular approximations

Polar coordinates identify the radial mass of the normalized annular bumps.
The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory Set Metric Filter Real
open scoped Topology Real

namespace HarmonicBalls

/-- Integrating a radial function on the plane gives its polar radial integral. -/
theorem integral_radial (f : ℝ → ℝ) (z : ℂ) :
    (∫ x : ℂ, f ‖x - z‖) = 2 * Real.pi * ∫ ρ in Ioi (0 : ℝ), ρ * f ρ := by
  have htrans : (∫ x : ℂ, f ‖x - z‖) = ∫ x : ℂ, f ‖x‖ := by
    simpa using (integral_sub_right_eq_self (fun x : ℂ => f ‖x‖) z)
  rw [htrans, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  simp_rw [Complex.norm_polarCoord_symm, smul_eq_mul]
  calc
    _ = (∫ ρ in Ioi (0 : ℝ), ρ * f |ρ|) * ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      rw [← setIntegral_prod_mul, Measure.volume_eq_prod]
      simp
    _ = 2 * Real.pi * ∫ ρ in Ioi (0 : ℝ), ρ * f ρ := by
      have hvol : (∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℝ)) = 2 * Real.pi := by
        rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, univ_inter]
        simp [Real.pi_nonneg, ← two_mul]
      rw [hvol, mul_comm]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro ρ hρ
      simp [abs_of_pos (show 0 < ρ from hρ)]

/-- Radial mass profile associated with a normalized annular density. -/
noncomputable def circleDensityRadialWeight (r δ : ℝ) (hδ : 0 < δ) (ρ : ℝ) : ℝ :=
  2 * Real.pi * (∫ x, circleDensity r δ hδ 0 x)⁻¹ *
    (ρ * circleRadiusBump r δ hδ (ρ ^ 2))

/-- The radial mass profile has total mass one on the positive half-line. -/
theorem circleDensityRadialWeight_integral {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    (∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ) = 1 := by
  simp_rw [circleDensityRadialWeight]
  rw [integral_const_mul]
  have h : (∫ x, circleDensity r δ hδ 0 x) =
      2 * Real.pi * ∫ ρ in Ioi (0 : ℝ), ρ * circleRadiusBump r δ hδ (ρ ^ 2) := by
    simpa [circleDensity] using integral_radial (fun t => circleRadiusBump r δ hδ (t ^ 2)) 0
  have hm := ne_of_gt (circleDensity_integral_pos hr hδ 0)
  calc
    _ = (∫ x, circleDensity r δ hδ 0 x)⁻¹ *
        (2 * Real.pi * ∫ ρ in Ioi (0 : ℝ), ρ * circleRadiusBump r δ hδ (ρ ^ 2)) := by ring
    _ = 1 := by rw [← h, inv_mul_cancel₀ hm]

/-- The radial mass profile is nonnegative at positive radii. -/
theorem circleDensityRadialWeight_nonneg (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ circleDensityRadialWeight r δ hδ ρ := by
  unfold circleDensityRadialWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
    (inv_nonneg.mpr (circleDensity_integral_pos hr hδ 0).le))
    (mul_nonneg hρ (circleRadiusBump r δ hδ).nonneg)

/-- The radial weight vanishes outside the annulus of the original density. -/
theorem circleDensityRadialWeight_support_radius {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hwidth : δ ≤ r * η) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : circleDensityRadialWeight r δ hδ ρ ≠ 0) : |ρ - r| < η := by
  have hb : circleRadiusBump r δ hδ (ρ ^ 2) ≠ 0 := by
    intro hz
    apply h
    simp [circleDensityRadialWeight, hz]
  have hd : (ρ : ℂ) ∈ Function.support (circleDensity r δ hδ 0) := by
    simpa [circleDensity, abs_of_nonneg hρ] using hb
  have := circleDensity_support_radius hr hδ hwidth 0 (ρ : ℂ) hd
  simpa [abs_of_nonneg hρ] using this

/-- The radial weight is integrable on positive radii. -/
theorem circleDensityRadialWeight_integrableOn {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    IntegrableOn (circleDensityRadialWeight r δ hδ) (Ioi (0 : ℝ)) := by
  have hc : Continuous (circleDensityRadialWeight r δ hδ) := by
    unfold circleDensityRadialWeight
    exact continuous_const.mul (continuous_id.mul
      ((circleRadiusBump r δ hδ).continuous.comp (continuous_id.pow 2)))
  let M : ℝ := r + δ + 1
  have hi : IntegrableOn (circleDensityRadialWeight r δ hδ) (Icc 0 M) :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  refine hi.of_forall_sdiff_eq_zero measurableSet_Ioi ?_
  intro ρ hρ
  have hρpos : 0 < ρ := hρ.1
  have hρM : M < ρ := by
    by_contra hn
    exact hρ.2 ⟨hρpos.le, le_of_not_gt hn⟩
  by_contra hn
  have hb : circleRadiusBump r δ hδ (ρ ^ 2) ≠ 0 := by
    intro hz
    apply hn
    simp [circleDensityRadialWeight, hz]
  have hd : (ρ : ℂ) ∈ Function.support (circleDensity r δ hδ 0) := by
    simpa [circleDensity, abs_of_pos hρpos] using hb
  have hs := circleDensity_support r δ hδ 0 (ρ : ℂ) hd
  simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos] at hs
  have hs' := (abs_lt.mp hs).2
  dsimp [M] at hρM
  nlinarith [sq_nonneg δ, sq_nonneg r]

/-- Integration of a radial observable against the normalized annular density
reduces to integration against its radial mass profile. -/
theorem integral_normalized_circleDensity_radial (r δ : ℝ) (hδ : 0 < δ)
    (z : ℂ) (f : ℝ → ℝ) :
    (∫ x : ℂ, (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
      circleDensity r δ hδ z x * f ‖x - z‖) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * f ρ := by
  have h := integral_radial
    (fun ρ => (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
      circleRadiusBump r δ hδ (ρ ^ 2) * f ρ) z
  simp only [circleDensity] at h ⊢
  rw [h, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  simp only [circleDensityRadialWeight, circleDensity, sub_zero]
  ring

/-- The angular integral on the polar-coordinate interval is the circle
average multiplied by the interval length. -/
theorem integral_circleMap_eq_circleAverage (f : ℂ → ℝ) (z : ℂ) (ρ : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, f (circleMap z ρ θ)) =
      2 * Real.pi * Real.circleAverage f z ρ := by
  have h := Real.circleAverage_eq_integral_add (f := f) (c := z) (R := ρ) (-Real.pi)
  change Real.circleAverage f z ρ = (2 * Real.pi)⁻¹ •
    ∫ θ in (0 : ℝ)..2 * Real.pi, (fun t => f (circleMap z ρ t)) (θ + -Real.pi) at h
  rw [intervalIntegral.integral_comp_add_right (fun t => f (circleMap z ρ t)) (-Real.pi)] at h
  have heq : 2 * Real.pi + -Real.pi = Real.pi := by ring
  simp only [zero_add, heq, smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_nonneg]),
    integral_Ioc_eq_integral_Ioo] at h
  rw [h]
  field_simp

/-- A continuous observable integrated against an annular density is a radial
mixture of its circle averages. -/
theorem integral_circleDensity_eq_circleAverage {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (z : ℂ) {f : ℂ → ℝ} (hf : Continuous f) :
    (∫ x, circleDensity r δ hδ z x * f x) =
      2 * Real.pi * ∫ ρ in Ioi (0 : ℝ),
        ρ * circleRadiusBump r δ hδ (ρ ^ 2) * Real.circleAverage f z ρ := by
  let g : ℝ × ℝ → ℝ := fun p =>
    p.1 * circleRadiusBump r δ hδ (p.1 ^ 2) * f (circleMap z p.1 p.2)
  have hc : Continuous g := by
    dsimp only [g, circleMap]
    apply (continuous_fst.mul ((circleRadiusBump r δ hδ).continuous.comp
      (continuous_fst.pow 2))).mul
    apply hf.comp
    fun_prop
  let M : ℝ := r + δ + 1
  have hint : IntegrableOn g (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) := by
    have hi : IntegrableOn g (Icc 0 M ×ˢ Icc (-Real.pi) Real.pi) :=
      hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    refine hi.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨ρ, θ⟩ ⟨⟨hρ, hθ⟩, hn⟩
    change 0 < ρ at hρ
    have hρM : M < ρ := by
      by_contra hnot
      exact hn ⟨⟨hρ.le, le_of_not_gt hnot⟩, ⟨hθ.1.le, hθ.2.le⟩⟩
    have hb : circleRadiusBump r δ hδ (ρ ^ 2) = 0 := by
      by_contra hb
      have hd : (ρ : ℂ) ∈ Function.support (circleDensity r δ hδ 0) := by
        simpa [circleDensity, abs_of_pos hρ] using hb
      have hs := circleDensity_support r δ hδ 0 (ρ : ℂ) hd
      simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at hs
      have hs' := (abs_lt.mp hs).2
      dsimp [M] at hρM
      nlinarith [sq_nonneg δ, sq_nonneg r]
    simp [g, hb]
  have htrans : (∫ x, circleDensity r δ hδ z x * f x) =
      ∫ u : ℂ, circleDensity r δ hδ z (u + z) * f (u + z) := by
    simpa using (integral_sub_right_eq_self
      (fun u : ℂ => circleDensity r δ hδ z (u + z) * f (u + z)) z)
  have hpolar : (∫ x, circleDensity r δ hδ z x * f x) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, g p := by
    rw [htrans, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨ρ, θ⟩ ⟨hρ, hθ⟩
    change 0 < ρ at hρ
    have hcircle : (Complex.polarCoord.symm (ρ, θ) + z) = circleMap z ρ θ := by
      simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, add_comm]
    simp only [g, smul_eq_mul, hcircle, circleDensity, circleMap_sub_center,
      norm_circleMap_zero, abs_of_pos hρ]
    ring
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint
  rw [hpolar, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  change (∫ θ in Ioo (-Real.pi) Real.pi,
    ρ * circleRadiusBump r δ hδ (ρ ^ 2) * f (circleMap z ρ θ)) = _
  rw [integral_const_mul, integral_circleMap_eq_circleAverage]
  ring

/-- The normalized annular density is the mixture of circle measures with
its normalized radial mass profile. -/
theorem integral_normalized_circleDensity_eq_circleAverage {r δ : ℝ} (hr : 0 ≤ r)
    (hδ : 0 < δ) (z : ℂ) {f : ℂ → ℝ} (hf : Continuous f) :
    (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x * f x) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ *
        Real.circleAverage f z ρ := by
  have heq : (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
      circleDensity r δ hδ z x * f x) =
      (∫ y, circleDensity r δ hδ 0 y)⁻¹ *
        ∫ x, circleDensity r δ hδ z x * f x := by
    simp_rw [mul_assoc, integral_const_mul]
  rw [heq, integral_circleDensity_eq_circleAverage hr hδ z hf, ← integral_const_mul,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  simp only [circleDensityRadialWeight]
  ring

end HarmonicBalls
