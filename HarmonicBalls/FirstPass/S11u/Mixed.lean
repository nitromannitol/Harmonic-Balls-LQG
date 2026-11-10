import HarmonicBalls.FirstPass.S11u.Kernel
import HarmonicBalls.Proofs.Sec8.CircleDensityPolarIntegrability

/-!
# Mixed covariances of a unit annular density and a circle average (fp-S11u, owner n4)

For the normalized Section 8 bump `unitCircleDensity r δ z` (unit mass, supported in an annulus around `∂B_r(z)`),
the three whole-plane covariances of `hC(μ)` and `hcirc(r, z)` are expressed through the logarithmic potentials
`U x = ∫ μ(y) log|y - x| dy` and `J x = log max(r, |x - z|)` (Jensen). Their combination is bounded by the uniform
potential error `log(r + η) - log(r - η)` (Section 8, `abs_circleDensity_log_potential_sub_circle_le`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology

/-- The unit-mass annular density `μ(x) = (∫ circleDensity 0)⁻¹ circleDensity z x` around `∂B_r(z)`. -/
noncomputable def unitCircleDensity (r δ : ℝ) (hδ : 0 < δ) (z x : ℂ) : ℝ :=
  (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x

/-- The logarithmic potential `U x = ∫ μ(y) log|y - x| dy` of the unit annular density. -/
noncomputable def logPotential (r δ : ℝ) (hδ : 0 < δ) (z x : ℂ) : ℝ :=
  ∫ y, unitCircleDensity r δ hδ z y * Real.log ‖y - x‖

/-- `J x = log max(r, |x - z|)`: the logarithmic potential of the uniform measure on `∂B_r(z)`. -/
noncomputable def circlePotential (r : ℝ) (z x : ℂ) : ℝ := Real.log (max r ‖x - z‖)

theorem unitCircleDensity_nonneg {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z x : ℂ) :
    0 ≤ unitCircleDensity r δ hδ z x :=
  mul_nonneg (inv_nonneg.mpr (circleDensity_integral_pos hr hδ 0).le) (circleDensity_nonneg r δ hδ z x)

theorem integral_unitCircleDensity {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z : ℂ) :
    ∫ x, unitCircleDensity r δ hδ z x = 1 :=
  circleDensity_normalized_integral hr hδ z

theorem unitCircleDensity_continuous (r δ : ℝ) (hδ : 0 < δ) (z : ℂ) :
    Continuous (unitCircleDensity r δ hδ z) :=
  continuous_const.mul (circleDensity_contDiff r δ hδ z).continuous

theorem unitCircleDensity_hasCompactSupport {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z : ℂ) :
    HasCompactSupport (unitCircleDensity r δ hδ z) :=
  (circleDensity_hasCompactSupport hr hδ z).mul_left

theorem integrable_unitCircleDensity_mul {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z : ℂ) {g : ℂ → ℝ}
    (hg : Continuous g) : Integrable (fun x => unitCircleDensity r δ hδ z x * g x) :=
  (((unitCircleDensity_continuous r δ hδ z).mul hg)).integrable_of_hasCompactSupport
    ((unitCircleDensity_hasCompactSupport hr hδ z).mul_right)

theorem integrable_unitCircleDensity_mul_log {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z w : ℂ) :
    Integrable (fun y => unitCircleDensity r δ hδ z y * Real.log ‖y - w‖) := by
  unfold unitCircleDensity
  simpa only [mul_assoc] using (integrable_circleDensity_mul_log_norm_sub hr hδ z w).const_mul
    (∫ y, circleDensity r δ hδ 0 y)⁻¹

theorem stronglyMeasurable_logPotential {r δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    StronglyMeasurable (logPotential r δ hδ z) := by
  unfold logPotential
  refine StronglyMeasurable.integral_prod_right'
    (f := fun p : ℂ × ℂ => unitCircleDensity r δ hδ z p.2 * Real.log ‖p.2 - p.1‖) ?_
  apply Measurable.stronglyMeasurable
  exact (((unitCircleDensity_continuous r δ hδ z).measurable.comp measurable_snd)).mul
    (Real.measurable_log.comp (measurable_norm.comp (measurable_snd.sub measurable_fst)))

theorem circlePotential_continuous {r : ℝ} (hr : 0 < r) (z : ℂ) : Continuous (circlePotential r z) :=
  (continuous_const.max (continuous_norm.comp (continuous_id.sub continuous_const))).log
    (fun _ => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _)))

/-- The uniform bound on the potential error (Section 8, `abs_circleDensity_log_potential_sub_circle_le`). -/
theorem abs_logPotential_sub_circlePotential_le {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hηr : η < r)
    (hwidth : δ ≤ r * η) (z x : ℂ) :
    |logPotential r δ hδ z x - circlePotential r z x| ≤ Real.log (r + η) - Real.log (r - η) := by
  have h := abs_circleDensity_log_potential_sub_circle_le hr hδ hηr hwidth z x
  rw [norm_sub_rev z x] at h
  exact h

theorem integrable_unitCircleDensity_mul_logPotential {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hηr : η < r)
    (hwidth : δ ≤ r * η) (z : ℂ) :
    Integrable (fun x => unitCircleDensity r δ hδ z x * logPotential r δ hδ z x) := by
  set e := Real.log (r + η) - Real.log (r - η) with he
  have hg : Integrable (fun x => unitCircleDensity r δ hδ z x * (|circlePotential r z x| + e)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (unitCircleDensity_continuous r δ hδ z).mul
        ((circlePotential_continuous hr z).abs.add continuous_const)
    · exact (unitCircleDensity_hasCompactSupport hr.le hδ z).mul_right
  refine hg.mono' ?_ ?_
  · exact ((unitCircleDensity_continuous r δ hδ z).stronglyMeasurable.mul
      (stronglyMeasurable_logPotential hδ z)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun x => ?_)
    have hμ := unitCircleDensity_nonneg hr.le hδ z x
    have hU := abs_logPotential_sub_circlePotential_le hr hδ hηr hwidth z x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hμ]
    apply mul_le_mul_of_nonneg_left _ hμ
    have h1 := abs_sub_abs_le_abs_sub (logPotential r δ hδ z x) (circlePotential r z x)
    have h2 : |logPotential r δ hδ z x| ≤ |circlePotential r z x| + e := by
      have := abs_sub_abs_le_abs_sub (logPotential r δ hδ z x) (circlePotential r z x)
      linarith [abs_sub_comm (logPotential r δ hδ z x) (circlePotential r z x)]
    exact h2

theorem integrable_unitCircleDensity {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z : ℂ) :
    Integrable (unitCircleDensity r δ hδ z) :=
  (unitCircleDensity_continuous r δ hδ z).integrable_of_hasCompactSupport
    (unitCircleDensity_hasCompactSupport hr hδ z)

/-- Scaling: an integrable `μ g` makes `circleDensity z g` integrable (`μ = M⁻¹ circleDensity`). -/
theorem integrable_circleDensity_mul_of_unit {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z : ℂ) {g : ℂ → ℝ}
    (hg : Integrable (fun x => unitCircleDensity r δ hδ z x * g x)) :
    Integrable (fun x => circleDensity r δ hδ z x * g x) := by
  have hM : (∫ y, circleDensity r δ hδ 0 y) ≠ 0 := (circleDensity_integral_pos hr hδ 0).ne'
  refine (hg.const_mul (∫ y, circleDensity r δ hδ 0 y)).congr (Filter.Eventually.of_forall fun x => ?_)
  unfold unitCircleDensity
  field_simp

/-- The inner integral of the whole-plane kernel against the unit density, at a point `x`. -/
theorem integral_unitCircleDensity_mul_wholePlaneCov {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) (z x : ℂ) :
    ∫ y, unitCircleDensity r δ hδ z y * wholePlaneCov x y =
      logMaxAbs x + (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) - logPotential r δ hδ z x := by
  have hae : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ x := by
    rw [ae_iff]
    simp
  have hcongr : (fun y => unitCircleDensity r δ hδ z y * wholePlaneCov x y) =ᵐ[volume]
      (fun y => logMaxAbs x * unitCircleDensity r δ hδ z y +
        unitCircleDensity r δ hδ z y * logMaxAbs y - unitCircleDensity r δ hδ z y * Real.log ‖y - x‖) := by
    filter_upwards [hae] with y hy
    rw [wholePlaneCov_eq_of_ne hy.symm, norm_sub_rev]
    ring
  have I1 : Integrable (fun y => logMaxAbs x * unitCircleDensity r δ hδ z y) :=
    (integrable_unitCircleDensity hr hδ z).const_mul _
  have I2 : Integrable (fun y => unitCircleDensity r δ hδ z y * logMaxAbs y) :=
    integrable_unitCircleDensity_mul hr hδ z logMaxAbs_continuous
  have I3 : Integrable (fun y => unitCircleDensity r δ hδ z y * Real.log ‖y - x‖) :=
    integrable_unitCircleDensity_mul_log hr hδ z x
  have I12 : Integrable (fun y => logMaxAbs x * unitCircleDensity r δ hδ z y + unitCircleDensity r δ hδ z y * logMaxAbs y) := I1.add I2
  rw [integral_congr_ae hcongr, integral_sub I12 I3, integral_add I1 I2,
    integral_const_mul, integral_unitCircleDensity hr hδ z, logPotential]
  ring

/-- `Kpp = ∫ μ(x) ∫ μ(y) K(x,y) dy dx = 2 ∫ μ a - ∫ μ U`. -/
theorem integral_unitCircleDensity_mul_inner {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hηr : η < r)
    (hwidth : δ ≤ r * η) (z : ℂ) :
    ∫ x, unitCircleDensity r δ hδ z x * ∫ y, unitCircleDensity r δ hδ z y * wholePlaneCov x y =
      2 * (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) -
        ∫ x, unitCircleDensity r δ hδ z x * logPotential r δ hδ z x := by
  simp only [integral_unitCircleDensity_mul_wholePlaneCov (r := r) (δ := δ) hr.le hδ z]
  have hA : Integrable (fun x => unitCircleDensity r δ hδ z x * logMaxAbs x) :=
    integrable_unitCircleDensity_mul hr.le hδ z logMaxAbs_continuous
  have hC : Integrable (fun x => (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) *
      unitCircleDensity r δ hδ z x) :=
    (integrable_unitCircleDensity hr.le hδ z).const_mul _
  have hsum : Integrable (fun x => unitCircleDensity r δ hδ z x * logMaxAbs x +
      (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) * unitCircleDensity r δ hδ z x) := hA.add hC
  have hI : Integrable (fun x => unitCircleDensity r δ hδ z x * logPotential r δ hδ z x) :=
    integrable_unitCircleDensity_mul_logPotential hr hδ hηr hwidth z
  have hpt : ∀ x, unitCircleDensity r δ hδ z x * (logMaxAbs x +
      (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) - logPotential r δ hδ z x) =
      (unitCircleDensity r δ hδ z x * logMaxAbs x +
        (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) * unitCircleDensity r δ hδ z x) -
        unitCircleDensity r δ hδ z x * logPotential r δ hδ z x := fun x => by ring
  simp only [hpt]
  rw [integral_sub hsum hI, integral_add hA hC, integral_const_mul,
    integral_unitCircleDensity hr.le hδ z]
  ring

/-- `Kpc = ∫ μ(x) circleAverage_y K(x,y) dx = ∫ μ a + A - ∫ μ J`, with `A = circleAverage a`. -/
theorem integral_unitCircleDensity_mul_circleAverage {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ) :
    ∫ x, unitCircleDensity r δ hδ z x * Real.circleAverage (fun y => wholePlaneCov x y) z r =
      (∫ y, unitCircleDensity r δ hδ z y * logMaxAbs y) + Real.circleAverage logMaxAbs z r -
        ∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x := by
  simp only [circleAverage_wholePlaneCov hr]
  have hA : Integrable (fun x => unitCircleDensity r δ hδ z x * logMaxAbs x) :=
    integrable_unitCircleDensity_mul hr.le hδ z logMaxAbs_continuous
  have hC : Integrable (fun x => (Real.circleAverage logMaxAbs z r) *
      unitCircleDensity r δ hδ z x) :=
    (integrable_unitCircleDensity hr.le hδ z).const_mul _
  have hsum : Integrable (fun x => unitCircleDensity r δ hδ z x * logMaxAbs x +
      (Real.circleAverage logMaxAbs z r) * unitCircleDensity r δ hδ z x) := hA.add hC
  have hJ : Integrable (fun x => unitCircleDensity r δ hδ z x * circlePotential r z x) :=
    integrable_unitCircleDensity_mul hr.le hδ z (circlePotential_continuous hr z)
  have hpt : ∀ x, unitCircleDensity r δ hδ z x * (logMaxAbs x + Real.circleAverage logMaxAbs z r -
      Real.log (max r ‖x - z‖)) = (unitCircleDensity r δ hδ z x * logMaxAbs x +
        (Real.circleAverage logMaxAbs z r) * unitCircleDensity r δ hδ z x) -
        unitCircleDensity r δ hδ z x * circlePotential r z x := fun x => by
    unfold circlePotential
    ring
  simp only [hpt]
  rw [integral_sub hsum hJ, integral_add hA hC, integral_const_mul,
    integral_unitCircleDensity hr.le hδ z]
  ring

/-- `Kzz = circleAverage_x circleAverage_y K(x,y) = 2 A - log r`. -/
theorem circleAverage_circleAverage_wholePlaneCov {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r) z r =
      2 * Real.circleAverage logMaxAbs z r - Real.log r := by
  have hfun : (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r) =
      (fun x => logMaxAbs x + Real.circleAverage logMaxAbs z r - circlePotential r z x) := by
    funext x
    rw [circleAverage_wholePlaneCov hr]
    rfl
  rw [hfun]
  have h1 : CircleIntegrable logMaxAbs z r :=
    ContinuousOn.circleIntegrable' logMaxAbs_continuous.continuousOn
  have h2 : CircleIntegrable (circlePotential r z) z r :=
    ContinuousOn.circleIntegrable' (circlePotential_continuous hr z).continuousOn
  have h3 : CircleIntegrable (logMaxAbs + fun _ => Real.circleAverage logMaxAbs z r) z r :=
    h1.add (circleIntegrable_const _ _ _)
  rw [show (fun x => logMaxAbs x + Real.circleAverage logMaxAbs z r - circlePotential r z x) =
      (logMaxAbs + fun _ => Real.circleAverage logMaxAbs z r) - circlePotential r z from rfl,
    Real.circleAverage_sub h3 h2, Real.circleAverage_add h1 (circleIntegrable_const _ _ _),
    Real.circleAverage_const]
  have hJ : Real.circleAverage (circlePotential r z) z r = Real.log r := by
    apply Real.circleAverage_const_on_circle
    intro x hx
    rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos hr] at hx
    unfold circlePotential
    rw [hx, max_self]
  rw [hJ]
  ring

/-- `|∫ μ (J - U)| ≤ e`: the uniform potential error integrated against the unit mass. -/
theorem abs_integral_unitCircleDensity_sub_potential_le {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hηr : η < r) (hwidth : δ ≤ r * η) (z : ℂ) :
    |(∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) -
        ∫ x, unitCircleDensity r δ hδ z x * logPotential r δ hδ z x| ≤
      Real.log (r + η) - Real.log (r - η) := by
  rw [← integral_sub (integrable_unitCircleDensity_mul hr.le hδ z (circlePotential_continuous hr z))
    (integrable_unitCircleDensity_mul_logPotential hr hδ hηr hwidth z)]
  have hpt : ∀ x, ‖unitCircleDensity r δ hδ z x * circlePotential r z x -
      unitCircleDensity r δ hδ z x * logPotential r δ hδ z x‖ ≤
      (Real.log (r + η) - Real.log (r - η)) * unitCircleDensity r δ hδ z x := by
    intro x
    have hμ := unitCircleDensity_nonneg hr.le hδ z x
    have hU := abs_logPotential_sub_circlePotential_le hr hδ hηr hwidth z x
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg hμ, abs_sub_comm]
    have := mul_le_mul_of_nonneg_left hU hμ
    linarith [mul_comm (unitCircleDensity r δ hδ z x) (Real.log (r + η) - Real.log (r - η))]
  have hint := norm_integral_le_of_norm_le
    ((integrable_unitCircleDensity hr.le hδ z).const_mul (Real.log (r + η) - Real.log (r - η)))
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_unitCircleDensity hr.le hδ z, mul_one] at hint
  simpa [Real.norm_eq_abs] using hint

/-- The circle average of `J = log max(r, |· - z|)` over `∂B_ρ(z)` is `log max(r, ρ)`. -/
theorem circleAverage_circlePotential_eq {r : ℝ} (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage (circlePotential r z) z ρ = Real.log (max r ρ) := by
  apply Real.circleAverage_const_on_circle
  intro x hx
  rw [Metric.mem_sphere, dist_eq_norm, abs_of_pos hρ] at hx
  unfold circlePotential
  rw [hx]

/-- `|∫ μ J - log r| ≤ e`: the polar identity for the radial weight and its support in `|ρ - r| < η`. -/
theorem abs_integral_unitCircleDensity_mul_circlePotential_sub_log_le {r δ η : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hηr : η < r) (hwidth : δ ≤ r * η) (z : ℂ) :
    |(∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) - Real.log r| ≤
      Real.log (r + η) - Real.log (r - η) := by
  have hf : Integrable (fun x => circleDensity r δ hδ z x * circlePotential r z x) :=
    integrable_circleDensity_mul_of_unit hr.le hδ z
      (integrable_unitCircleDensity_mul hr.le hδ z (circlePotential_continuous hr z))
  have hpolar : (∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * Real.circleAverage (circlePotential r z) z ρ :=
    integral_normalized_circleDensity_eq_circleAverage_of_integrable hδ z hf
  have hpolar' : (∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) =
      ∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * Real.log (max r ρ) := by
    rw [hpolar]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
    rw [circleAverage_circlePotential_eq z hρ]
  have hW := circleDensityRadialWeight_integrableOn hr.le hδ
  have hcont : Continuous (fun ρ : ℝ => Real.log (max r ρ) - Real.log r) :=
    ((continuous_const.max continuous_id).log (fun ρ => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _)))).sub
      continuous_const
  have hpt : ∀ ρ : ℝ, 0 < ρ → ‖circleDensityRadialWeight r δ hδ ρ *
      (Real.log (max r ρ) - Real.log r)‖ ≤
      (Real.log (r + η) - Real.log (r - η)) * circleDensityRadialWeight r δ hδ ρ := by
    intro ρ hρ
    have hw0 := circleDensityRadialWeight_nonneg r δ hr.le hδ hρ.le
    by_cases hw : circleDensityRadialWeight r δ hδ ρ = 0
    · simp [hw]
    · have hsup := circleDensityRadialWeight_support_radius hr hδ hwidth hρ.le hw
      obtain ⟨hs1, hs2⟩ := abs_lt.mp hsup
      have hc1 : Real.log r ≤ Real.log (max r ρ) := Real.log_le_log hr (le_max_left _ _)
      have hc2 : Real.log (max r ρ) ≤ Real.log (r + η) :=
        Real.log_le_log (lt_of_lt_of_le hr (le_max_left _ _))
          (max_le (by linarith) (by linarith))
      have hc3 : Real.log (r - η) ≤ Real.log r := Real.log_le_log (by linarith) (by linarith)
      have hbd : |Real.log (max r ρ) - Real.log r| ≤ Real.log (r + η) - Real.log (r - η) := by
        rw [abs_le]
        constructor <;> linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
      have := mul_le_mul_of_nonneg_left hbd hw0
      linarith [mul_comm (circleDensityRadialWeight r δ hδ ρ) (Real.log (r + η) - Real.log (r - η))]
  have hI1 : IntegrableOn (fun ρ => circleDensityRadialWeight r δ hδ ρ *
      (Real.log (max r ρ) - Real.log r)) (Ioi 0) := by
    refine Integrable.mono' (hW.const_mul (Real.log (r + η) - Real.log (r - η))) ?_ ?_
    · exact (hW.aestronglyMeasurable.mul hcont.aestronglyMeasurable)
    · exact (ae_restrict_mem measurableSet_Ioi).mono fun ρ hρ => hpt ρ hρ
  have hI2 : IntegrableOn (fun ρ => Real.log r * circleDensityRadialWeight r δ hδ ρ) (Ioi 0) :=
    hW.const_mul _
  have hsplit : (∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * Real.log (max r ρ)) =
      (∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ *
        (Real.log (max r ρ) - Real.log r)) + Real.log r := by
    have h1 : (∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ * Real.log (max r ρ)) =
        ∫ ρ in Ioi (0 : ℝ), (circleDensityRadialWeight r δ hδ ρ *
          (Real.log (max r ρ) - Real.log r) + Real.log r * circleDensityRadialWeight r δ hδ ρ) :=
      setIntegral_congr_fun measurableSet_Ioi (fun ρ _ => by ring)
    rw [h1, integral_add hI1 hI2, integral_const_mul, circleDensityRadialWeight_integral hr.le hδ,
      mul_one]
  have hfin : |∫ ρ in Ioi (0 : ℝ), circleDensityRadialWeight r δ hδ ρ *
      (Real.log (max r ρ) - Real.log r)| ≤ Real.log (r + η) - Real.log (r - η) := by
    have hint := norm_integral_le_of_norm_le (hW.const_mul (Real.log (r + η) - Real.log (r - η)))
      ((ae_restrict_mem measurableSet_Ioi).mono fun ρ hρ => hpt ρ hρ)
    rw [integral_const_mul, circleDensityRadialWeight_integral hr.le hδ, mul_one] at hint
    simpa [Real.norm_eq_abs] using hint
  rw [hpolar', hsplit, add_sub_cancel_right]
  exact hfin

/-- The whole-plane covariance combination `Kpp + Kzz - 2 Kpc` of a unit annular density, bounded by the
uniform potential error. This is the variance of `hC μ - hcirc(r, z)` (see `variance_unitCircleDensity`). -/
theorem abs_unitCircleDensity_covariance_combination {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hηr : η < r) (hwidth : δ ≤ r * η) (z : ℂ) :
    |(∫ x, unitCircleDensity r δ hδ z x * ∫ y, unitCircleDensity r δ hδ z y * wholePlaneCov x y) +
        Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r) z r -
      2 * ∫ x, unitCircleDensity r δ hδ z x * Real.circleAverage (fun y => wholePlaneCov x y) z r| ≤
      2 * (Real.log (r + η) - Real.log (r - η)) := by
  rw [integral_unitCircleDensity_mul_inner hr hδ hηr hwidth z,
    integral_unitCircleDensity_mul_circleAverage hr hδ z,
    circleAverage_circleAverage_wholePlaneCov hr z]
  have key : ∀ a b u j L : ℝ, (2 * a - u) + (2 * b - L) - 2 * (a + b - j) = (j - u) + (j - L) :=
    fun a b u j L => by ring
  rw [key]
  have h2 := abs_integral_unitCircleDensity_sub_potential_le hr hδ hηr hwidth z
  have h3 := abs_integral_unitCircleDensity_mul_circlePotential_sub_log_le hr hδ hηr hwidth z
  have h4 := abs_add_le ((∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) -
      ∫ x, unitCircleDensity r δ hδ z x * logPotential r δ hδ z x)
    ((∫ x, unitCircleDensity r δ hδ z x * circlePotential r z x) - Real.log r)
  linarith

end HarmonicBalls
