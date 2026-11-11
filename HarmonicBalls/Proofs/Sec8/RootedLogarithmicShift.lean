import HarmonicBalls.Proofs.Sec8.WholePlaneSmoothShift
import HarmonicBalls.Proofs.Sec8.RootedShiftMeasurability

/-! # Root-dependent logarithmic perturbations

The Cameron–Martin theorem in Leonardo Bonanno's whole-plane GFF development
gives a local comparison when a logarithmic singularity stays outside the
observed ball. A second insertion may have a singularity inside that ball.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff

namespace HarmonicBalls

/-- Jointly measurable insertion functions need no separate measurability
assumptions on their local pairing processes. -/
theorem IsWholePlaneGFF.rooted_local_smooth_insertion_law
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] (ρ : Measure Z)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (g k : Z → ℂ → ℝ)
    (hg : Measurable (Function.uncurry g)) (hk : Measurable (Function.uncurry k))
    (hsmooth : ∀ᵐ z ∂ρ, ContDiffOn ℝ ∞ (g z) (ball c R)) :
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + (∫ x, φ.1.1 x * g p.1 x) +
          ∫ x, φ.1.1 x * k p.1 x) ≪
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * k p.1 x) := by
  apply hh.rooted_local_smooth_shift_law ρ hr hrR g
    (fun z φ => ∫ x, φ.1.1 x * k z x) hsmooth
  · apply measurable_pi_iff.mpr
    intro φ
    have hm := measurable_local_pairing_add_root_integral (U := ball c r)
      (Section6.pairingProc hC) (Section6.measurable_pairingProc hh) g hg
    exact ((measurable_pi_apply φ).comp hm).add
      ((measurable_integral_test_mul_root_function k hk φ.1.1).comp measurable_fst)
  · exact measurable_local_pairing_add_root_integral
      (Section6.pairingProc hC) (Section6.measurable_pairingProc hh) k hk

/-- A logarithmic insertion whose singularity stays outside a buffered
observation ball gives a dominated joint field-and-root law, even with a
common logarithmic insertion at the origin. -/
theorem IsWholePlaneGFF.rooted_local_logarithmic_shift_law
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure ℂ)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (a b : ℝ)
    (haway : ∀ᵐ z ∂ρ, ∀ x ∈ ball c R, z + x ≠ 0) :
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + (∫ x, φ.1.1 x * (a * Real.log ‖p.1 + x‖)) +
          ∫ x, φ.1.1 x * (b * Real.log ‖x‖)) ≪
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (b * Real.log ‖x‖)) := by
  apply hh.rooted_local_smooth_insertion_law ρ hr hrR
    (fun z x => a * Real.log ‖z + x‖) (fun _ x => b * Real.log ‖x‖)
  · change Measurable (fun p : ℂ × ℂ => a * Real.log ‖p.1 + p.2‖)
    have h := measurable_translated_log_insertions a 0
    simpa only [zero_mul, add_zero] using h
  · change Measurable (fun p : ℂ × ℂ => b * Real.log ‖p.2‖)
    have h := measurable_translated_log_insertions 0 b
    simpa only [zero_mul, zero_add] using h
  · filter_upwards [haway] with z hz
    exact contDiffOn_const.mul (contDiffOn_log_norm_add hz)

/-- A test function times a translated logarithm is integrable, including at
the logarithmic singularity. -/
theorem integrable_test_mul_translated_log (φ : LQGMetric.TestC) (z : ℂ) (a : ℝ) :
    Integrable (fun x => φ x * (a * Real.log ‖z + x‖)) := by
  have h := (LQGMetric.CircleAvg.integrable_log_mul_test φ (-z)).neg.const_mul a
  convert h using 1
  funext x
  change φ x * (a * Real.log ‖z + x‖) = a * (-(-Real.log ‖-z - x‖ * φ x))
  rw [show -z - x = -(z + x) by abel, norm_neg]
  ring

/-- The two logarithmic insertions may be paired as a single function. -/
theorem integral_test_mul_translated_log_add (φ : LQGMetric.TestC) (z : ℂ) (a b : ℝ) :
    (∫ x, φ x * (a * Real.log ‖z + x‖ + b * Real.log ‖x‖)) =
      (∫ x, φ x * (a * Real.log ‖z + x‖)) +
        ∫ x, φ x * (b * Real.log ‖x‖) := by
  have hz := integrable_test_mul_translated_log φ z a
  have h0 := integrable_test_mul_translated_log φ 0 b
  simp only [zero_add] at h0
  rw [show (fun x => φ x * (a * Real.log ‖z + x‖ + b * Real.log ‖x‖)) =
      (fun x => φ x * (a * Real.log ‖z + x‖) + φ x * (b * Real.log ‖x‖)) by
        funext x; ring, integral_add hz h0]

/-- The rooted comparison for the combined logarithmic insertion. -/
theorem IsWholePlaneGFF.rooted_local_combined_logarithmic_shift_law
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure ℂ)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (a b : ℝ)
    (haway : ∀ᵐ z ∂ρ, ∀ x ∈ ball c R, z + x ≠ 0) :
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x *
          (a * Real.log ‖p.1 + x‖ + b * Real.log ‖x‖)) ≪
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (b * Real.log ‖x‖)) := by
  simpa only [integral_test_mul_translated_log_add, add_assoc] using
    hh.rooted_local_logarithmic_shift_law ρ hr hrR a b haway

/-- If the root stays outside the buffer around the origin, its translated
logarithmic singularity stays outside the observed origin-centered ball. -/
theorem IsWholePlaneGFF.rooted_origin_logarithmic_shift_law
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure ℂ)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (a b : ℝ)
    (hroot : ∀ᵐ z ∂ρ, R ≤ ‖z‖) :
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x *
          (a * Real.log ‖p.1 + x‖ + b * Real.log ‖x‖)) ≪
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (b * Real.log ‖x‖)) := by
  apply hh.rooted_local_combined_logarithmic_shift_law ρ hr hrR a b
  filter_upwards [hroot] with z hz x hx
  have hxnorm : ‖x‖ < R := by simpa [mem_ball, dist_eq_norm] using hx
  intro hzero
  have hxeq : x = -z := by linear_combination hzero
  rw [hxeq, norm_neg] at hxnorm
  exact (not_lt_of_ge hz) hxnorm

end HarmonicBalls
