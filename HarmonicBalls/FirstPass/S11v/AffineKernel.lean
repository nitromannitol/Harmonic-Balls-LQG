import HarmonicBalls.FirstPass.S11v.AffineCore
import HarmonicBalls.FirstPass.S11i.DilationMixing
import HarmonicBalls.FirstPass.S11u.Kernel
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity

/-!
# Kernel identities for the affine pull-back of the whole-plane covariance

For `F z = a z + b` with `a ≠ 0`, `s = |a|`, let `A = avg_{∂B(0,1)} L∘F` and `M(x) = L(F x) - L(x) + A - log s`,
`M0 = 2A - log s`, where `L = logMaxAbs = log max(|·|,1)` (`HarmonicBalls.logMaxAbs`, S11u/Kernel.lean).
These give the exact pointwise identity off the diagonal (`wholePlaneCov_affine`)
  `K(F x, F y) = K(x, y) + M x + M y - M0`  (`K = wholePlaneCov`),
the unit-circle identities `avg_{∂B(0,1)} K(x, ·) = 0` and `avg_{∂B(0,1)} M = M0`, and the continuity of the
smeared potentials `x ↦ q.smear (K x ·)` of admissible observables `q`.
Reference: Armstrong–Kuusi–Mourrat-style log-potential calculus.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology

/-- The unit-circle average of `L ∘ F`, `A = avg_{∂B(0,1)} log max(|a v + b|, 1)`. -/
noncomputable def affA (a b : ℂ) : ℝ :=
  Real.circleAverage (fun v => logMaxAbs (a * v + b)) 0 1

/-- The pointwise pull-back of the log-potential, `M(x) = L(F x) - L(x) + A - log |a|`. -/
noncomputable def affM (a b : ℂ) (x : ℂ) : ℝ :=
  logMaxAbs (a * x + b) - logMaxAbs x + affA a b - Real.log ‖a‖

/-- The constant `M0 = 2A - log |a|`. -/
noncomputable def affM0 (a b : ℂ) : ℝ :=
  2 * affA a b - Real.log ‖a‖

/-- **Pointwise affine identity** of the whole-plane kernel off the diagonal:
`K(F x, F y) = K(x, y) + M x + M y - M0`. -/
theorem wholePlaneCov_affine {a : ℂ} (ha : a ≠ 0) (b : ℂ) {x y : ℂ} (hxy : x ≠ y) :
    wholePlaneCov (a * x + b) (a * y + b) =
      wholePlaneCov x y + affM a b x + affM a b y - affM0 a b := by
  have hs : 0 < ‖a‖ := norm_pos_iff.2 ha
  have ht : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hd : ‖a * x + b - (a * y + b)‖ = ‖a‖ * ‖x - y‖ := by
    rw [show a * x + b - (a * y + b) = a * (x - y) by ring, norm_mul]
  have hL : ∀ z : ℂ, 0 < max ‖z‖ 1 := fun z => lt_of_lt_of_le one_pos (le_max_right _ _)
  unfold wholePlaneCov affM affM0 logMaxAbs
  rw [hd, Real.log_div (mul_pos (hL _) (hL _)).ne' (mul_pos hs ht).ne',
    Real.log_mul (hL _).ne' (hL _).ne', Real.log_mul hs.ne' ht.ne',
    Real.log_div (mul_pos (hL _) (hL _)).ne' ht.ne', Real.log_mul (hL _).ne' (hL _).ne']
  ring

/-- The unit-circle average of `L` vanishes. -/
theorem circleAverage_logMaxAbs_unit : Real.circleAverage logMaxAbs 0 1 = 0 := by
  have h : Real.circleAverage logMaxAbs 0 1 = Real.circleAverage (fun _ => (0 : ℝ)) 0 1 := by
    refine Real.circleAverage_congr_sphere (fun y hy => ?_)
    have hy1 : ‖y‖ = 1 := by simpa using hy
    simp [logMaxAbs, hy1]
  rw [h, Real.circleAverage_const]

/-- The unit-circle average of the kernel vanishes at every point: `avg_{∂B(0,1)} K(x, ·) = 0`. -/
theorem circleAverage_wholePlaneCov_unit (x : ℂ) :
    Real.circleAverage (fun y => wholePlaneCov x y) 0 1 = 0 := by
  rw [circleAverage_wholePlaneCov one_pos, circleAverage_logMaxAbs_unit]
  simp only [logMaxAbs, sub_zero, add_zero, max_comm 1 ‖x‖, sub_self]

/-- The unit-circle average of `M` is `M0`: `avg_{∂B(0,1)} M = M0`. -/
theorem circleAverage_affM_unit (a b : ℂ) : Real.circleAverage (affM a b) 0 1 = affM0 a b := by
  have hc1 : CircleIntegrable (fun y => logMaxAbs (a * y + b)) 0 1 :=
    ContinuousOn.circleIntegrable' (logMaxAbs_continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).continuousOn
  have hc2 : CircleIntegrable (fun y => logMaxAbs y) 0 1 :=
    ContinuousOn.circleIntegrable' logMaxAbs_continuous.continuousOn
  have hc3 : CircleIntegrable (fun _ : ℂ => affA a b - Real.log ‖a‖) 0 1 :=
    circleIntegrable_const _ _ _
  have hfun : affM a b = fun y => (logMaxAbs (a * y + b) - logMaxAbs y) + (affA a b - Real.log ‖a‖) :=
    funext fun y => by unfold affM; ring
  have hc12 : CircleIntegrable (fun y => logMaxAbs (a * y + b) - logMaxAbs y) 0 1 := hc1.sub hc2
  rw [hfun, Real.circleAverage_fun_add hc12 hc3, Real.circleAverage_fun_sub hc1 hc2,
    Real.circleAverage_const, circleAverage_logMaxAbs_unit]
  unfold affM0
  have : Real.circleAverage (fun y => logMaxAbs (a * y + b)) 0 1 = affA a b := rfl
  rw [this]
  ring

/-- Continuity of the pairing potential `x ↦ ∫ ψ(y) K(x, y) dy` for a test function `ψ`. -/
theorem continuous_potential_pairing {ψ : ℂ → ℝ} (hψ : IsTestFunction univ ψ) :
    Continuous (fun x => (GFFObservable.pairing ψ).smear (fun y => wholePlaneCov x y)) :=
  continuous_wholePlaneCov_potential_general hψ.1.continuous hψ.2.1

/-- Continuity of the circle potential `x ↦ avg_{∂B(z, r)} K(x, ·)` for `r > 0`. -/
theorem continuous_potential_circle {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Continuous (fun x => (GFFObservable.circle r z).smear (fun y => wholePlaneCov x y)) := by
  have h : (fun x => (GFFObservable.circle r z).smear (fun y => wholePlaneCov x y)) =
      fun x => logMaxAbs x + Real.circleAverage logMaxAbs z r - Real.log (max r ‖x - z‖) :=
    funext fun x => circleAverage_wholePlaneCov hr
  rw [h]
  have hmax : ∀ x : ℂ, max r ‖x - z‖ ≠ 0 := fun x => (lt_of_lt_of_le hr (le_max_left _ _)).ne'
  exact (logMaxAbs_continuous.add continuous_const).sub
    (Continuous.log (by fun_prop) hmax)

/-- Continuity of the smeared potential of every admissible observable. -/
theorem continuous_potential {q : GFFObservable} (hq : q.IsAdmissible) :
    Continuous (fun x => q.smear (fun y => wholePlaneCov x y)) := by
  cases q with
  | pairing ψ => exact continuous_potential_pairing hq
  | circle r z => exact continuous_potential_circle hq z

/-- `M` is continuous. -/
theorem continuous_affM (a b : ℂ) : Continuous (affM a b) := by
  unfold affM
  exact ((logMaxAbs_continuous.comp (by fun_prop)).sub logMaxAbs_continuous).add continuous_const |>.sub
    continuous_const

/-- Circle case of the affine potential identity: the circle average over `∂B(z, r)` of `K(F x, F ·)`. -/
theorem circleAverage_potential_affine {a : ℂ} (ha : a ≠ 0) (b x z : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (fun y => wholePlaneCov (a * x + b) (a * y + b)) z r =
      Real.circleAverage (fun y => wholePlaneCov x y) z r + affM a b x +
        Real.circleAverage (affM a b) z r - affM0 a b := by
  have hcongr : (fun y => wholePlaneCov (a * x + b) (a * y + b)) =ᶠ[codiscreteWithin (sphere z |r|)]
      (fun y => (logMaxAbs x + logMaxAbs y - Real.log ‖x - y‖) + affM a b x + affM a b y - affM0 a b) := by
    refine Filter.eventually_of_mem (compl_singleton_mem_codiscreteWithin x) ?_
    intro y hy
    have hxy : x ≠ y := fun h => hy (Set.mem_singleton_iff.2 h.symm)
    show wholePlaneCov (a * x + b) (a * y + b) = _
    rw [wholePlaneCov_affine ha b hxy, wholePlaneCov_eq_of_ne hxy]
  rw [Real.circleAverage_congr_codiscreteWithin hcongr hr.ne']
  have i1 : CircleIntegrable (fun y => logMaxAbs y) z r :=
    ContinuousOn.circleIntegrable' logMaxAbs_continuous.continuousOn
  have i2 : CircleIntegrable (fun y => Real.log ‖x - y‖) z r := by
    have := circleIntegrable_log_norm_sub_const (c := z) (a := x) r
    simpa only [norm_sub_rev] using this
  have hlog : Real.circleAverage (fun y => Real.log ‖x - y‖) z r = Real.log (max r ‖x - z‖) := by
    rw [show (fun y => Real.log ‖x - y‖) = fun y => Real.log ‖y - x‖ from funext fun y => by rw [norm_sub_rev],
      circleAverage_log_norm_sub_eq z x hr, norm_sub_rev z x]
  have iM : CircleIntegrable (affM a b) z r := (continuous_affM a b).continuousOn.circleIntegrable'
  have hfun : (fun y => (logMaxAbs x + logMaxAbs y - Real.log ‖x - y‖) + affM a b x + affM a b y - affM0 a b) =
      fun y => ((logMaxAbs x + affM a b x - affM0 a b) + logMaxAbs y + affM a b y) - Real.log ‖x - y‖ :=
    funext fun y => by ring
  have hc0 : CircleIntegrable (fun _ : ℂ => logMaxAbs x + affM a b x - affM0 a b) z r :=
    circleIntegrable_const _ _ _
  have hs1 : CircleIntegrable (fun y => (logMaxAbs x + affM a b x - affM0 a b) + logMaxAbs y) z r :=
    hc0.fun_add i1
  have hs2 : CircleIntegrable (fun y => ((logMaxAbs x + affM a b x - affM0 a b) + logMaxAbs y) + affM a b y)
      z r := hs1.fun_add iM
  rw [hfun, Real.circleAverage_fun_sub hs2 i2, Real.circleAverage_fun_add hs1 iM,
    Real.circleAverage_fun_add hc0 i1, Real.circleAverage_const, hlog, circleAverage_wholePlaneCov hr]
  unfold affM0
  ring

/-- A test function times a continuous function is integrable. -/
theorem integrable_test_mul_continuous {ψ : ℂ → ℝ} (hψ : IsTestFunction univ ψ) {g : ℂ → ℝ}
    (hg : Continuous g) : Integrable (fun y => ψ y * g y) :=
  (hψ.1.continuous.mul hg).integrable_of_hasCompactSupport hψ.2.1.mul_right

/-- Pairing case of the affine potential identity:
`∫ ψ(y) K(F x, F y) dy = ∫ ψ(y) K(x, y) dy + (∫ ψ) M x + ∫ ψ M - (∫ ψ) M0`. -/
theorem integral_potential_affine_pairing {a : ℂ} (ha : a ≠ 0) (b x : ℂ) {ψ : ℂ → ℝ}
    (hψ : IsTestFunction univ ψ) :
    ∫ y, ψ y * wholePlaneCov (a * x + b) (a * y + b) =
      (∫ y, ψ y * wholePlaneCov x y) + (∫ y, ψ y) * affM a b x + (∫ y, ψ y * affM a b y) -
        (∫ y, ψ y) * affM0 a b := by
  obtain ⟨R, hR⟩ := hψ.2.1.isCompact.isBounded.subset_closedBall 0
  have hψi : Integrable ψ := integrable_of_isTestFunction hψ
  have hMi : Integrable (fun y => ψ y * affM a b y) := integrable_test_mul_continuous hψ (continuous_affM a b)
  have hLi : Integrable (fun y => ψ y * logMaxAbs y) :=
    integrable_test_mul_continuous hψ logMaxAbs_continuous
  have hlog : Integrable (fun y => ψ y * Real.log ‖x - y‖) := by
    have h := integrable_mul_log_norm_sub hψ (R := R) (fun z hz => by
      have := hR (subset_tsupport ψ hz)
      simpa using this) x
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [norm_sub_rev]
  have hKi : Integrable (fun y => ψ y * wholePlaneCov x y) := by
    have h := ((hψi.mul_const (logMaxAbs x)).add hLi).sub hlog
    refine h.congr ?_
    filter_upwards [Measure.ae_ne volume x] with y hy
    rw [wholePlaneCov_eq_of_ne hy.symm]
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hae : (fun y => ψ y * wholePlaneCov (a * x + b) (a * y + b)) =ᵐ[volume]
      (fun y => ψ y * wholePlaneCov x y + ψ y * affM a b x + ψ y * affM a b y - ψ y * affM0 a b) := by
    filter_upwards [Measure.ae_ne volume x] with y hy
    rw [wholePlaneCov_affine ha b hy.symm]
    ring
  have I1 : Integrable (fun y => ψ y * wholePlaneCov x y + ψ y * affM a b x) :=
    hKi.add (hψi.mul_const _)
  have I2 : Integrable (fun y => ψ y * wholePlaneCov x y + ψ y * affM a b x + ψ y * affM a b y) :=
    I1.add hMi
  have I3 : Integrable (fun y => ψ y * affM0 a b) := hψi.mul_const _
  rw [integral_congr_ae hae, integral_sub I2 I3, integral_add I1 hMi, integral_add hKi (hψi.mul_const _)]
  simp only [integral_mul_const]

end HarmonicBalls
