import HarmonicBalls.Proofs.Sec6.CollarReturnTransport
import HarmonicBalls.Proofs.Sec6.NearbyAnnulusBoundary

/-! # Annular geometry for translated collar returns -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal

/-- Translating a radially shrunken annulus by less than its margin places it
inside the original annulus. -/
theorem image_add_annulus_subset {z v : ℂ} {r R δ : ℝ}
    (hv : ‖v‖ < δ) :
    (fun w : ℂ => w + v) '' annulus z (r + δ) (R - δ) ⊆ annulus z r R := by
  rintro _ ⟨w, hw, rfl⟩
  simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le] at hw ⊢
  have h₁ := dist_triangle (w + v) w z
  have h₂ := dist_triangle w (w + v) z
  have hd : dist (w + v) w = ‖v‖ := by simp [dist_eq_norm]
  have hd' : dist w (w + v) = ‖v‖ := by rw [dist_comm, hd]
  rw [hd] at h₁
  rw [hd'] at h₂
  constructor <;> linarith [hw.1, hw.2]

/-- The original annulus is contained in any translate, by less than the
margin, of the radially enlarged annulus. -/
theorem annulus_subset_image_add {z v : ℂ} {r R δ : ℝ}
    (hv : ‖v‖ < δ) :
    annulus z r R ⊆ (fun w : ℂ => w + v) '' annulus z (r - δ) (R + δ) := by
  intro w hw
  refine ⟨w - v, ?_, sub_add_cancel w v⟩
  simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le] at hw ⊢
  have h₁ := dist_triangle (w - v) w z
  have h₂ := dist_triangle w (w - v) z
  have hd : dist (w - v) w = ‖v‖ := by simp
  have hd' : dist w (w - v) = ‖v‖ := by rw [dist_comm, hd]
  rw [hd] at h₁
  rw [hd'] at h₂
  constructor <;> linarith [hw.1, hw.2]

/-- The corresponding inclusion for closed annular cores. -/
theorem closed_annular_core_subset_image_add {z v : ℂ} {r R δ : ℝ}
    (hv : ‖v‖ < δ) :
    {w : ℂ | r ≤ dist w z ∧ dist w z ≤ R} ⊆
      (fun w : ℂ => w + v) ''
        {w : ℂ | r - δ ≤ dist w z ∧ dist w z ≤ R + δ} := by
  intro w hw
  refine ⟨w - v, ?_, sub_add_cancel w v⟩
  have h₁ := dist_triangle (w - v) w z
  have h₂ := dist_triangle w (w - v) z
  have hd : dist (w - v) w = ‖v‖ := by simp
  have hd' : dist w (w - v) = ‖v‖ := by rw [dist_comm, hd]
  rw [hd] at h₁
  rw [hd'] at h₂
  constructor <;> linarith [hw.1, hw.2]

/-- A shifted starting point has annular return probability at most the
return probability for the radially enlarged outer annulus and core and the
radially shrunken inner annulus at the original starting point. -/
theorem planarBrownian_annular_core_return_le_of_translation
    (x z v : ℂ) (r R b B s S δ : ℝ) (hv : ‖v‖ < δ) :
    planarBrownianMotion (x + v) {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (annulus z b B) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z r R) ω ∧
      s ≤ dist (ω t) z ∧ dist (ω t) z ≤ S} ≤
    planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (annulus z (b + δ) (B - δ)) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z (r - δ) (R + δ)) ω ∧
      s - δ ≤ dist (ω t) z ∧ dist (ω t) z ≤ S + δ} := by
  simpa only [mem_ofPred_eq] using
    (planarBrownian_core_return_le_of_translation x v
      (annulus z r R) (annulus z b B) {w | s ≤ dist w z ∧ dist w z ≤ S}
      (annulus z (r - δ) (R + δ)) (annulus z (b + δ) (B - δ))
      {w | s - δ ≤ dist w z ∧ dist w z ≤ S + δ}
      (image_add_annulus_subset hv) (annulus_subset_image_add hv)
      (closed_annular_core_subset_image_add hv))

end HarmonicBalls.Section6
