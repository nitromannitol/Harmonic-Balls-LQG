import HarmonicBalls.Proofs.Sec8.WholePlaneRootInsertion

/-! # Localization of the whole-plane rooted insertion

On a ball contained in the unit disk, the whole-plane normalization term
vanishes. Thus the insertion around a root in that disk reduces locally to the
logarithmic singularity at the root. No rooted-law comparison is assumed.
The imported Section 6 development uses Leonardo Bonanno's whole-plane GFF
formalization.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- A closed ball of radius less than the distance from its center to the
unit circle is contained in the unit disk. -/
theorem closedBall_subset_unitBall_of_norm_add_lt_one {z : ℂ} {r : ℝ}
    (hr : ‖z‖ + r < 1) : closedBall z r ⊆ ball 0 1 := by
  intro x hx
  have hdist : ‖x - z‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hx
  have hnorm : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - z) z
  have : ‖x‖ < 1 := by linarith
  simpa [mem_ball, dist_eq_norm] using this

/-- Every root in the unit disk has a positive closed-ball neighborhood
contained in the unit disk. -/
theorem exists_pos_closedBall_subset_unitBall {z : ℂ} (hz : z ∈ ball 0 1) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ ball 0 1 := by
  have hz' : ‖z‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz
  refine ⟨(1 - ‖z‖) / 2, by linarith, ?_⟩
  apply closedBall_subset_unitBall_of_norm_add_lt_one
  linarith

/-- The unit-circle normalization term disappears on the unit disk. -/
theorem wholePlane_root_insertion_eq_log_on_unitBall (γ : ℝ) (z : ℂ) :
    EqOn (fun x : ℂ => -γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))
      (fun x => -γ * Real.log ‖x - z‖) (ball 0 1) := by
  intro x hx
  have hx' : ‖x‖ ≤ 1 := le_of_lt (by simpa [mem_ball, dist_eq_norm] using hx)
  simp [max_eq_right hx']

/-- Every test supported in the unit disk pairs the whole-plane rooted
insertion exactly as it pairs the pure logarithmic singularity. -/
theorem integral_wholePlane_root_insertion_eq_log
    (γ : ℝ) (z : ℂ) {φ : ℂ → ℝ} (hφ : tsupport φ ⊆ ball 0 1) :
    (∫ x, φ x * (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))) =
      ∫ x, φ x * (-γ * Real.log ‖x - z‖) :=
  integral_mul_eq_of_eqOn_tsupport
    ((wholePlane_root_insertion_eq_log_on_unitBall γ z).mono hφ)

/-- Local observations on a ball contained in the unit disk see precisely
the pure logarithmic rooted singularity. -/
theorem wholePlane_root_inserted_local_pairings_eq_log
    {Ω : Type*} (X : Ω → LQGMetric.TestC0 → ℝ) (γ : ℝ) (z : ℂ) (r : ℝ)
    (hball : ball z r ⊆ ball 0 1) (ω : Ω) :
    (fun φ : Section6.LocalTest (ball z r) =>
      X ω φ.1 + ∫ x, φ.1.1 x *
        (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))) =
    (fun φ : Section6.LocalTest (ball z r) =>
      X ω φ.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x - z‖)) := by
  funext φ
  rw [integral_wholePlane_root_insertion_eq_log γ z (φ.property.trans hball)]

/-- After translating a test to the root, its inserted pairing equals the
pairing with the origin logarithm whenever its translated support stays in
the unit disk. -/
theorem integral_recentered_wholePlane_root_insertion_eq_log
    (γ : ℝ) (z : ℂ) {φ : ℂ → ℝ}
    (hφ : ∀ y ∈ tsupport φ, y + z ∈ ball 0 1) :
    (∫ x, φ (x - z) *
      (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))) =
      ∫ y, φ y * (-γ * Real.log ‖y‖) := by
  have htranslate := integral_add_right_eq_self (μ := volume)
    (fun x : ℂ => φ (x - z) *
      (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))) z
  have heq : EqOn
      (fun y : ℂ => -γ * Real.log ‖(y + z) - z‖ +
        γ * Real.log (max ‖y + z‖ 1))
      (fun y => -γ * Real.log ‖y‖) (tsupport φ) := by
    intro y hy
    have h := wholePlane_root_insertion_eq_log_on_unitBall γ z (hφ y hy)
    simpa using h
  calc
    _ = ∫ y, φ y * (-γ * Real.log ‖(y + z) - z‖ +
          γ * Real.log (max ‖y + z‖ 1)) := by simpa using htranslate.symm
    _ = _ := integral_mul_eq_of_eqOn_tsupport heq

/-- A local test centered at the origin may be translated to any root whose
buffered ball stays in the unit disk. -/
theorem integral_recentered_wholePlane_root_insertion_localTest
    (γ : ℝ) (z : ℂ) {r : ℝ} (hr : ‖z‖ + r < 1)
    (φ : Section6.LocalTest (ball 0 r)) :
    (∫ x, φ.1.1 (x - z) *
      (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))) =
      ∫ y, φ.1.1 y * (-γ * Real.log ‖y‖) := by
  apply integral_recentered_wholePlane_root_insertion_eq_log γ z
  intro y hy
  have hy' : ‖y‖ < r := by
    simpa [mem_ball, dist_eq_norm] using φ.property hy
  have hnorm := norm_add_le y z
  have : ‖y + z‖ < 1 := by linarith
  simpa [mem_ball, dist_eq_norm] using this

#print axioms closedBall_subset_unitBall_of_norm_add_lt_one
#print axioms exists_pos_closedBall_subset_unitBall
#print axioms wholePlane_root_insertion_eq_log_on_unitBall
#print axioms integral_wholePlane_root_insertion_eq_log
#print axioms wholePlane_root_inserted_local_pairings_eq_log
#print axioms integral_recentered_wholePlane_root_insertion_eq_log
#print axioms integral_recentered_wholePlane_root_insertion_localTest

end HarmonicBalls
