import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Proposed.DuplantierMillerSheffield
import HarmonicBalls.Proofs.Sec8.CircleLogPotential
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteAKernel

/-! # Route (A), Palm identity: the covariance shift of a marked circle observable

For the whole-plane GFF `(P, hC, hcirc)` and a circle `∂B(z, ε)` in the closed unit disk, the covariance of the pairing
`hC · φ` with the circle average `hcirc · ε z` is, by Sec8 `circleAverage_wholePlaneCov_eq`,
`∫ φ(x) (log max(|x|,1) - log max(ε, |z - x|)) dx`. The DMS shift `dmsShift γ z` (the marked shift `k_z`) has pairing `∫ dmsShift γ z · φ`. Their difference is
`γ ∫ φ(x) (log|x - z| - log max(ε, |x - z|)) dx`, which vanishes off `B_ε(z)` and is bounded by
`|γ| ‖φ‖∞ ∫_{B_ε} |log(|v|/ε)| dv`, hence by `|γ| C 2π ε²`, uniformly in `z`. (the absolute error is
bounded by `γ ‖φ_j‖∞ ∫_{|v|<ε} log(ε/|v|) d²v`; we use the cruder constant `2π` for the integral.)
-/

noncomputable section

open MeasureTheory Set Metric

namespace HarmonicBalls

/-- The circle average of the normalization `log max(|·|, 1)` vanishes on a circle in the closed unit disk. -/
theorem circleAverage_wholePlaneNormalization_eq_zero {z : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hdisk : ∀ y ∈ Metric.sphere z ε, ‖y‖ ≤ 1) :
    Real.circleAverage wholePlaneNormalization z ε = 0 := by
  have hEq : Set.EqOn wholePlaneNormalization (fun _ => (0 : ℝ)) (Metric.sphere z |ε|) := by
    intro y hy
    rw [abs_of_pos hε] at hy
    simp [wholePlaneNormalization, max_eq_right (hdisk y hy)]
  rw [Real.circleAverage_congr_sphere hEq, Real.circleAverage_const]

/-- The radial integral `∫_{B_ε} |log(|v|/ε)| dv ≤ 2π ε²` (polar coordinates: `integral_fun_norm_addHaar`). -/
theorem integral_abs_log_div_ball_le {ε : ℝ} (hε : 0 < ε) :
    ∫ v in ball (0 : ℂ) ε, |Real.log (‖v‖ / ε)| ∂(volume : Measure ℂ) ≤ 2 * Real.pi * ε ^ 2 := by
  set F : ℝ → ℝ := (Iio ε).indicator (fun y => |Real.log (y / ε)|) with hF
  have hFnn : ∀ y : ℝ, 0 ≤ F y := fun y => by
    rw [hF]
    exact indicator_nonneg (fun _ _ => abs_nonneg _) y
  have h1 : ∫ v in ball (0 : ℂ) ε, |Real.log (‖v‖ / ε)| ∂(volume : Measure ℂ)
      = ∫ v, F ‖v‖ ∂(volume : Measure ℂ) := by
    rw [← integral_indicator measurableSet_ball]
    congr 1
    funext v
    by_cases hv : v ∈ ball (0 : ℂ) ε
    · have hv' : ‖v‖ ∈ Iio ε := mem_ball_zero_iff.1 hv
      rw [indicator_of_mem hv, hF, indicator_of_mem hv']
    · have hv' : ‖v‖ ∉ Iio ε := fun h => hv (mem_ball_zero_iff.2 h)
      rw [indicator_of_notMem hv, hF, indicator_of_notMem hv']
  rw [h1, integral_fun_norm_addHaar volume F]
  have hdim : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have hvol : (volume : Measure ℂ).real (ball (0 : ℂ) 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  rw [hdim, hvol]
  have hpt : ∀ y ∈ Ioi (0 : ℝ), y ^ (2 - 1) • F y ≤ (Ioo (0 : ℝ) ε).indicator (fun _ : ℝ => ε) y := by
    intro y hy
    have hy' : (0 : ℝ) < y := hy
    rw [show (2 - 1 : ℕ) = 1 from rfl]
    by_cases hyε : y < ε
    · have hFy : F y = |Real.log (y / ε)| := by
        rw [hF, indicator_of_mem (show y ∈ Iio ε from hyε)]
      rw [hFy, indicator_of_mem (show y ∈ Ioo (0 : ℝ) ε from ⟨hy', hyε⟩)]
      have hle : Real.log (y / ε) ≤ 0 :=
        Real.log_nonpos (div_nonneg hy'.le hε.le) ((div_le_one hε).2 hyε.le)
      rw [abs_of_nonpos hle, smul_eq_mul, pow_one]
      have hlog : -Real.log (y / ε) = Real.log (ε / y) := by
        rw [← Real.log_inv, inv_div]
      rw [hlog]
      show y * Real.log (ε / y) ≤ ε
      have h2 : Real.log (ε / y) ≤ ε / y - 1 := Real.log_le_sub_one_of_pos (div_pos hε hy')
      have h3 := mul_le_mul_of_nonneg_left h2 hy'.le
      rw [mul_sub, mul_one] at h3
      have h5 : y * (ε / y) = ε := by field_simp
      linarith
    · have hFy : F y = 0 := by
        rw [hF, indicator_of_notMem (show y ∉ Iio ε from hyε)]
      rw [hFy, smul_zero]
      exact indicator_nonneg (fun _ _ => hε.le) y
  have hint_ind : Integrable ((Ioo (0 : ℝ) ε).indicator (fun _ : ℝ => ε))
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))) := by
    have hs : (volume : Measure ℝ) (Ioo (0 : ℝ) ε) ≠ ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    have hI : Integrable ((Ioo (0 : ℝ) ε).indicator (fun _ : ℝ => ε)) (volume : Measure ℝ) :=
      (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const hs)
    exact hI.restrict
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • F y ≤ ε ^ 2 := by
    have hnn : ∀ᵐ y ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))), (0 : ℝ) ≤ y ^ (2 - 1) • F y := by
      refine (ae_restrict_mem measurableSet_Ioi).mono fun y hy => ?_
      rw [smul_eq_mul]
      exact mul_nonneg (pow_nonneg (le_of_lt hy) _) (hFnn y)
    have hle : ∀ᵐ y ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
        y ^ (2 - 1) • F y ≤ (Ioo (0 : ℝ) ε).indicator (fun _ : ℝ => ε) y :=
      (ae_restrict_mem measurableSet_Ioi).mono fun y hy => hpt y hy
    calc ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • F y
        ≤ ∫ y in Ioi (0 : ℝ), (Ioo (0 : ℝ) ε).indicator (fun _ : ℝ => ε) y :=
          integral_mono_of_nonneg hnn hint_ind hle
      _ = ε ^ 2 := by
          rw [integral_indicator measurableSet_Ioo, setIntegral_const, Measure.real,
            Measure.restrict_apply measurableSet_Ioo, Set.Ioo_inter_Ioi, sup_idem, Real.volume_Ioo,
            ENNReal.toReal_ofReal (sub_nonneg.2 hε.le), smul_eq_mul]
          ring
  have hI' : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) * F y ≤ ε ^ 2 := by simpa only [smul_eq_mul] using hI
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  nlinarith [mul_le_mul_of_nonneg_left hI' Real.pi_pos.le]

/-- Integrability of `x ↦ |log(|x - z| / ε)|` on `B_ε(z)` (extended by zero). -/
theorem integrable_indicator_ball_abs_log_div {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Integrable ((ball z ε).indicator (fun x : ℂ => |Real.log (‖x - z‖ / ε)|)) (volume : Measure ℂ) := by
  have hdom0 : Integrable ((ball (0 : ℂ) ε).indicator
      (fun v : ℂ => |Real.log ‖v‖| + |Real.log ε|)) (volume : Measure ℂ) :=
    ((integrableOn_abs_log_norm_ball ε).add (integrableOn_const (C := |Real.log ε|)
      measure_ball_lt_top.ne)).integrable_indicator measurableSet_ball
  have hzero : Integrable ((ball (0 : ℂ) ε).indicator (fun v : ℂ => |Real.log (‖v‖ / ε)|))
      (volume : Measure ℂ) := by
    refine hdom0.mono' ?_ (ae_of_all _ fun v => ?_)
    · have hm : Measurable (fun v : ℂ => |Real.log (‖v‖ / ε)|) :=
        continuous_abs.measurable.comp (Real.measurable_log.comp (by fun_prop))
      exact (hm.indicator measurableSet_ball).aestronglyMeasurable
    · by_cases hv : v ∈ ball (0 : ℂ) ε
      · rw [indicator_of_mem hv, indicator_of_mem hv, Real.norm_eq_abs]
        rcases eq_or_ne ‖v‖ 0 with h0 | h0
        · simp [h0]
        · rw [Real.log_div h0 hε.ne']
          simpa using abs_sub_le (Real.log ‖v‖) 0 (Real.log ε)
      · rw [indicator_of_notMem hv (fun v : ℂ => |Real.log (‖v‖ / ε)|),
          indicator_of_notMem hv (fun v : ℂ => |Real.log ‖v‖| + |Real.log ε|)]
        simp
  have htrans := hzero.comp_sub_right z
  refine htrans.congr (ae_of_all _ fun x => ?_)
  show (ball (0 : ℂ) ε).indicator (fun v : ℂ => |Real.log (‖v‖ / ε)|) (x - z)
      = (ball z ε).indicator (fun x : ℂ => |Real.log (‖x - z‖ / ε)|) x
  by_cases hx : x ∈ ball z ε
  · have hx' : x - z ∈ ball (0 : ℂ) ε := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]
      exact mem_ball.1 hx
    rw [indicator_of_mem hx', indicator_of_mem hx]
  · have hx' : x - z ∉ ball (0 : ℂ) ε := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]
      exact fun h => hx (mem_ball.2 h)
    rw [indicator_of_notMem hx', indicator_of_notMem hx]

/-- Integrability of `x ↦ φ(x) log |x - z|` for a bounded compactly supported `φ`. -/
theorem integrable_test_mul_log_sub {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {C : ℝ} (hC0 : ∀ x, |φ x| ≤ C) (z : ℂ) :
    Integrable (fun x => φ x * Real.log ‖x - z‖) (volume : Measure ℂ) := by
  obtain ⟨R₀, hR₀⟩ := (show IsCompact (tsupport φ) from hφs).isBounded.subset_closedBall (0 : ℂ)
  have hg : Integrable ((ball (0 : ℂ) (R₀ + ‖z‖ + 1)).indicator (fun v : ℂ => |Real.log ‖v‖|))
      (volume : Measure ℂ) :=
    (integrableOn_abs_log_norm_ball (R₀ + ‖z‖ + 1)).integrable_indicator measurableSet_ball
  have hgz := hg.comp_sub_right z
  have hmeas : Measurable (fun x : ℂ => φ x * Real.log ‖x - z‖) :=
    hφc.measurable.mul (Real.measurable_log.comp
      ((continuous_norm.comp (continuous_id.sub continuous_const)).measurable))
  refine (hgz.const_mul C).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  show |φ x| * |Real.log ‖x - z‖| ≤ C * (ball (0 : ℂ) (R₀ + ‖z‖ + 1)).indicator
    (fun v : ℂ => |Real.log ‖v‖|) (x - z)
  by_cases hx : x ∈ tsupport φ
  · have hxR : ‖x‖ ≤ R₀ := by
      have h := hR₀ hx
      rwa [mem_closedBall_zero_iff] at h
    have hxz : ‖x - z‖ < R₀ + ‖z‖ + 1 := by
      have := norm_sub_le x z
      linarith
    have hind : (ball (0 : ℂ) (R₀ + ‖z‖ + 1)).indicator (fun v : ℂ => |Real.log ‖v‖|) (x - z)
        = |Real.log ‖x - z‖| := by
      rw [indicator_of_mem (show x - z ∈ ball (0 : ℂ) (R₀ + ‖z‖ + 1) from by
        rw [mem_ball_zero_iff]; exact hxz)]
    rw [hind]
    exact mul_le_mul_of_nonneg_right (hC0 x) (abs_nonneg _)
  · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hφx, abs_zero, zero_mul]
    exact mul_nonneg (le_trans (abs_nonneg _) (hC0 0))
      (indicator_nonneg (fun _ _ => abs_nonneg _) _)

/-- **Covariance shift of the marked circle observable**: for a bounded compactly supported test
function `φ` and a circle `∂B(z,ε)` in the closed unit disk,
`|γ Cov(hC φ, hcirc ε z) - ∫ dmsShift γ z · φ| ≤ |γ| C 2π ε²`, uniformly in `z`. -/
theorem gamma_covariance_sub_dmsShift_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε) (z : ℂ)
    (hdisk : ∀ y ∈ Metric.sphere z ε, ‖y‖ ≤ 1) (γ : ℝ) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) {C : ℝ} (hC0 : ∀ x, |φ x| ≤ C) :
    |γ * ProbabilityTheory.covariance (fun ω => hC ω φ) (fun ω => hcirc ω ε z) P
        - ∫ x, dmsShift γ z x * φ x|
      ≤ |γ| * C * (2 * Real.pi * ε ^ 2) := by
  have hφc : Continuous φ := hφ.1.continuous
  have hφs : HasCompactSupport φ := hφ.2.1
  -- the covariance as a kernel integral (Sec8 circle formula, circle inside the unit disk)
  have hcov : ProbabilityTheory.covariance (fun ω => hC ω φ) (fun ω => hcirc ω ε z) P
      = ∫ x, φ x * (wholePlaneNormalization x - Real.log (max ε ‖z - x‖)) := by
    have h1 := hG.covariance_eq (GFFObservable.pairing φ) (GFFObservable.circle ε z) hφ hε
    rw [show ProbabilityTheory.covariance (fun ω => hC ω φ) (fun ω => hcirc ω ε z) P
        = wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.circle ε z) from h1]
    show ∫ x, φ x * Real.circleAverage (fun y => wholePlaneCov x y) z ε = _
    congr 1
    funext x
    rw [circleAverage_wholePlaneCov_eq hε z x,
      circleAverage_wholePlaneNormalization_eq_zero hε hdisk, add_zero]
  -- the DMS shift pairing
  have hdms : ∫ x, dmsShift γ z x * φ x
      = ∫ x, φ x * (-γ * Real.log ‖x - z‖ + γ * wholePlaneNormalization x) := by
    congr 1
    funext x
    simp only [dmsShift, wholePlaneNormalization]
    ring
  -- integrability of the building blocks
  have hNi : Integrable (fun x => φ x * wholePlaneNormalization x) (volume : Measure ℂ) :=
    (hφc.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hφs.mul_right
  have hLc : Continuous (fun x : ℂ => φ x * Real.log (max ε ‖z - x‖)) :=
    hφc.mul ((continuous_const.max ((continuous_const.sub continuous_id).norm)).log
      (fun x => (lt_of_lt_of_le hε (le_max_left _ _)).ne'))
  have hLi : Integrable (fun x : ℂ => φ x * Real.log (max ε ‖z - x‖)) (volume : Measure ℂ) :=
    hLc.integrable_of_hasCompactSupport hφs.mul_right
  have hli := integrable_test_mul_log_sub hφc hφs hC0 z
  -- splitting the three integrals
  have E1 : ∫ x, φ x * (wholePlaneNormalization x - Real.log (max ε ‖z - x‖))
      = (∫ x, φ x * wholePlaneNormalization x) - (∫ x, φ x * Real.log (max ε ‖z - x‖)) := by
    have hfun : (fun x : ℂ => φ x * (wholePlaneNormalization x - Real.log (max ε ‖z - x‖)))
        = fun x => φ x * wholePlaneNormalization x - φ x * Real.log (max ε ‖z - x‖) := by
      funext x
      ring
    rw [hfun, integral_sub hNi hLi]
  have E2 : (∫ x, dmsShift γ z x * φ x)
      = γ * (∫ x, φ x * wholePlaneNormalization x) - γ * (∫ x, φ x * Real.log ‖x - z‖) := by
    have hfun : (fun x : ℂ => dmsShift γ z x * φ x)
        = fun x => γ * (φ x * wholePlaneNormalization x) - γ * (φ x * Real.log ‖x - z‖) := by
      funext x
      simp only [dmsShift, wholePlaneNormalization]
      ring
    have h := integral_sub (hNi.const_mul γ) (hli.const_mul γ)
    rw [integral_const_mul, integral_const_mul] at h
    rw [hfun, h]
  have E3 : (∫ x, φ x * (γ * (Real.log ‖x - z‖ - Real.log (max ε ‖z - x‖))))
      = γ * (∫ x, φ x * Real.log ‖x - z‖) - γ * (∫ x, φ x * Real.log (max ε ‖z - x‖)) := by
    have hfun : (fun x : ℂ => φ x * (γ * (Real.log ‖x - z‖ - Real.log (max ε ‖z - x‖))))
        = fun x => γ * (φ x * Real.log ‖x - z‖) - γ * (φ x * Real.log (max ε ‖z - x‖)) := by
      funext x
      ring
    have h := integral_sub (hli.const_mul γ) (hLi.const_mul γ)
    rw [integral_const_mul, integral_const_mul] at h
    rw [hfun, h]
  have hdiffeq : γ * ProbabilityTheory.covariance (fun ω => hC ω φ) (fun ω => hcirc ω ε z) P
      - (∫ x, dmsShift γ z x * φ x)
      = ∫ x, φ x * (γ * (Real.log ‖x - z‖ - Real.log (max ε ‖z - x‖))) := by
    rw [hcov, E1, E2, E3]
    ring
  -- pointwise bound off the centre (the centre is a null set)
  have hpt : ∀ᵐ x ∂(volume : Measure ℂ),
      ‖φ x * (γ * (Real.log ‖x - z‖ - Real.log (max ε ‖z - x‖)))‖
        ≤ |γ| * C * (ball z ε).indicator (fun x : ℂ => |Real.log (‖x - z‖ / ε)|) x := by
    have hne : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ z :=
      (ae_iff (p := fun x : ℂ => x ≠ z)).2
        (by simp)
    filter_upwards [hne] with x hx
    have hxz : ‖x - z‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hx)
    have hnorm : ‖z - x‖ = ‖x - z‖ := norm_sub_rev z x
    by_cases hlt : ‖x - z‖ < ε
    · have hxb : x ∈ ball z ε := by
        rw [mem_ball, dist_eq_norm]
        exact hlt
      rw [indicator_of_mem hxb]
      have hmax : max ε ‖z - x‖ = ε := by
        rw [hnorm]
        exact max_eq_left hlt.le
      rw [hmax, ← Real.log_div hxz hε.ne', Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := hC0 x
      have h2 : 0 ≤ |γ| * |Real.log (‖x - z‖ / ε)| := by positivity
      calc |φ x| * (|γ| * |Real.log (‖x - z‖ / ε)|)
          ≤ C * (|γ| * |Real.log (‖x - z‖ / ε)|) := mul_le_mul_of_nonneg_right h1 h2
        _ = |γ| * C * |Real.log (‖x - z‖ / ε)| := by ring
    · have hxb : x ∉ ball z ε := by
        rw [mem_ball, dist_eq_norm]
        exact hlt
      rw [indicator_of_notMem hxb]
      have hmax : max ε ‖z - x‖ = ‖x - z‖ := by
        rw [hnorm]
        exact max_eq_right (not_lt.1 hlt)
      rw [hmax]
      simp
  have hbnd_int := (integrable_indicator_ball_abs_log_div hε z).const_mul (|γ| * C)
  have hint := norm_integral_le_of_norm_le hbnd_int hpt
  have hbound : ∫ x, (ball z ε).indicator (fun x : ℂ => |Real.log (‖x - z‖ / ε)|) x
      ∂(volume : Measure ℂ) ≤ 2 * Real.pi * ε ^ 2 := by
    have htrans : ∫ x, (ball z ε).indicator (fun x : ℂ => |Real.log (‖x - z‖ / ε)|) x
        ∂(volume : Measure ℂ)
        = ∫ x, (ball (0 : ℂ) ε).indicator (fun v : ℂ => |Real.log (‖v‖ / ε)|) (x - z)
          ∂(volume : Measure ℂ) := by
      congr 1
      funext x
      by_cases hx : x ∈ ball z ε
      · have hx' : x - z ∈ ball (0 : ℂ) ε := by
          rw [mem_ball_zero_iff, ← dist_eq_norm]
          exact mem_ball.1 hx
        rw [indicator_of_mem hx', indicator_of_mem hx]
      · have hx' : x - z ∉ ball (0 : ℂ) ε := by
          rw [mem_ball_zero_iff, ← dist_eq_norm]
          exact fun h => hx (mem_ball.2 h)
        rw [indicator_of_notMem hx', indicator_of_notMem hx]
    rw [htrans]
    calc ∫ x, (ball (0 : ℂ) ε).indicator (fun v : ℂ => |Real.log (‖v‖ / ε)|) (x - z)
          ∂(volume : Measure ℂ)
        = ∫ x, (ball (0 : ℂ) ε).indicator (fun v : ℂ => |Real.log (‖v‖ / ε)|) x
          ∂(volume : Measure ℂ) := integral_sub_right_eq_self _ z
      _ = ∫ v in ball (0 : ℂ) ε, |Real.log (‖v‖ / ε)| ∂(volume : Measure ℂ) :=
          integral_indicator measurableSet_ball
      _ ≤ 2 * Real.pi * ε ^ 2 := integral_abs_log_div_ball_le hε
  calc |γ * ProbabilityTheory.covariance (fun ω => hC ω φ) (fun ω => hcirc ω ε z) P
        - ∫ x, dmsShift γ z x * φ x|
      = ‖∫ x, φ x * (γ * (Real.log ‖x - z‖ - Real.log (max ε ‖z - x‖)))‖ := by
        rw [hdiffeq, Real.norm_eq_abs]
    _ ≤ ∫ x, |γ| * C * (ball z ε).indicator (fun x : ℂ => |Real.log (‖x - z‖ / ε)|) x
        ∂(volume : Measure ℂ) := hint
    _ = |γ| * C * ∫ x, (ball z ε).indicator (fun x : ℂ => |Real.log (‖x - z‖ / ε)|) x
        ∂(volume : Measure ℂ) := integral_const_mul _ _
    _ ≤ |γ| * C * (2 * Real.pi * ε ^ 2) :=
        mul_le_mul_of_nonneg_left hbound (mul_nonneg (abs_nonneg γ) (le_trans (abs_nonneg _) (hC0 0)))

end HarmonicBalls

end
