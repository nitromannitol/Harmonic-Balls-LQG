import HarmonicBalls.Proofs.Sec8.RootedSmoothShiftEquivalence
import HarmonicBalls.Proofs.Sec8.CircleLogPotential

/-! # Local comparison for whole-plane normalization

The unit-circle normalization in the rooted whole-plane field is locally
smooth whenever the observation ball stays on one side of the unit circle.
The imported Cameron–Martin theorem is due to Leonardo Bonanno.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff

namespace HarmonicBalls

/-- The translated unit-circle normalization is smooth on a ball which does
not cross the unit circle. -/
theorem contDiffOn_translated_wholePlane_normalization {z : ℂ} {R : ℝ}
    (hside : ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖) :
    ContDiffOn ℝ ∞ (fun x : ℂ => Real.log (max ‖z + x‖ 1)) (ball 0 R) := by
  rcases hside with hinside | houtside
  · apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℂ => (0 : ℝ)) (ball 0 R)).congr
    intro x hx
    have hxnorm : ‖x‖ < R := by simpa [mem_ball, dist_eq_norm] using hx
    have hnorm : ‖z + x‖ ≤ 1 := by
      calc
        ‖z + x‖ ≤ ‖z‖ + ‖x‖ := norm_add_le _ _
        _ ≤ 1 := by linarith
    simp only [max_eq_right hnorm, Real.log_one]
  · have haway : ∀ x ∈ ball (0 : ℂ) R, z + x ≠ 0 := by
      intro x hx hzero
      have hxnorm : ‖x‖ < R := by simpa [mem_ball, dist_eq_norm] using hx
      have hxeq : x = -z := by linear_combination hzero
      rw [hxeq, norm_neg] at hxnorm
      linarith
    apply (contDiffOn_log_norm_add haway).congr
    intro x hx
    have hxnorm : ‖x‖ < R := by simpa [mem_ball, dist_eq_norm] using hx
    have hnorm : 1 ≤ ‖z + x‖ := by
      have htri : ‖z‖ ≤ ‖z + x‖ + ‖x‖ := by
        simpa only [add_sub_cancel_right] using norm_sub_le (z + x) x
      linarith
    rw [max_eq_left hnorm]

/-- The translated normalization term preserves the joint local rooted law's
null sets, including in the presence of a logarithmic insertion at the root. -/
theorem IsWholePlaneGFF.rooted_normalization_shift_equivalence
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure ℂ)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (a b : ℝ)
    (hside : ∀ᵐ z ∂ρ, ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖) :
    let A := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + (∫ x, φ.1.1 x * (a * Real.log (max ‖p.1 + x‖ 1))) +
          ∫ x, φ.1.1 x * (b * Real.log ‖x‖))
    let B := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (b * Real.log ‖x‖))
    A ≪ B ∧ B ≪ A := by
  apply hh.rooted_local_smooth_insertion_equivalence ρ hr hrR
    (fun z x => a * Real.log (max ‖z + x‖ 1)) (fun _ x => b * Real.log ‖x‖)
  · change Measurable (fun p : ℂ × ℂ => a * Real.log (max ‖p.1 + p.2‖ 1))
    exact (Real.measurable_log.comp ((measurable_fst.add measurable_snd).norm.max
      measurable_const)).const_mul a
  · change Measurable (fun p : ℂ × ℂ => b * Real.log ‖p.2‖)
    simpa only [zero_mul, zero_add] using measurable_translated_log_insertions 0 b
  · filter_upwards [hside] with z hz
    exact contDiffOn_const.mul (contDiffOn_translated_wholePlane_normalization hz)

/-- Pairing the recentered rooted insertion splits into its singular and
normalization parts. -/
theorem integral_recentered_root_insertion_split (φ : LQGMetric.TestC)
    (z : ℂ) (a b : ℝ) :
    (∫ x, φ x * (a * Real.log (max ‖z + x‖ 1) + b * Real.log ‖x‖)) =
      (∫ x, φ x * (a * Real.log (max ‖z + x‖ 1))) +
        ∫ x, φ x * (b * Real.log ‖x‖) := by
  have hcont : Continuous (fun x : ℂ => a * Real.log (max ‖z + x‖ 1)) := by
    exact continuous_const.mul (continuous_wholePlaneNormalization.comp (continuous_const.add continuous_id))
  have hi : Integrable (fun x => φ x * (a * Real.log (max ‖z + x‖ 1))) :=
    (φ.continuous.mul hcont).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  have hj := integrable_test_mul_translated_log φ 0 b
  simp only [zero_add] at hj
  rw [show (fun x => φ x * (a * Real.log (max ‖z + x‖ 1) + b * Real.log ‖x‖)) =
      (fun x => φ x * (a * Real.log (max ‖z + x‖ 1)) + φ x * (b * Real.log ‖x‖)) by
        funext x; ring, integral_add hi hj]

/-- The comparison also applies to the single combined insertion appearing in
the recentered whole-plane rooted-field formula. -/
theorem IsWholePlaneGFF.rooted_combined_normalization_equivalence
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure ℂ)
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (a b : ℝ)
    (hside : ∀ᵐ z ∂ρ, ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖) :
    let A := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x *
          (a * Real.log (max ‖p.1 + x‖ 1) + b * Real.log ‖x‖))
    let B := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (b * Real.log ‖x‖))
    A ≪ B ∧ B ≪ A := by
  simpa only [integral_recentered_root_insertion_split, add_assoc] using
    hh.rooted_normalization_shift_equivalence ρ hr hrR a b hside

#print axioms integral_recentered_root_insertion_split
#print axioms IsWholePlaneGFF.rooted_combined_normalization_equivalence
#print axioms contDiffOn_translated_wholePlane_normalization
#print axioms IsWholePlaneGFF.rooted_normalization_shift_equivalence

end HarmonicBalls
