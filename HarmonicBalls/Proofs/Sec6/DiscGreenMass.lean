import HarmonicBalls.Proofs.Sec6.GreenTranslation
import HarmonicBalls.Proofs.Potential.GreenPositivity
import HarmonicBalls.Proofs.Potential.GreenBall

/-! # Lower bounds for disc Green potentials

The disc estimate in the proof of Lemma 6.8 uses a uniform lower bound for
Green's function on the inner half-disc, away from its diagonal junk value.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

/-- The Green function of a disc is symmetric for any centre. -/
theorem greenFunction_ball_center_comm (c : ℂ) (R : ℝ) (x y : ℂ) :
    greenFunction (ball c R) x y = greenFunction (ball c R) y x := by
  have hset : (fun z : ℂ => z + c) '' ball 0 R = ball c R := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw
    · intro hz
      refine ⟨z - c, ?_, sub_add_cancel z c⟩
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hz
  have h := greenFunction_translate (ball 0 R) c (x - c) (y - c)
  have h' := greenFunction_translate (ball 0 R) c (y - c) (x - c)
  rw [hset, sub_add_cancel, sub_add_cancel] at h h'
  exact h.trans ((greenFunction_ball_comm R (x - c) (y - c)).trans h'.symm)

/-- Green's function in a disc of radius `2r`, evaluated at the centre, is
uniformly bounded below on the punctured inner disc of radius `r`. -/
theorem log_three_halves_le_greenFunction_ball_center {c y : ℂ} {r : ℝ}
    (hr : 0 < r) (hy : y ∈ ball c r) (hne : y ≠ c) :
    (2 * Real.pi)⁻¹ * Real.log (3 / 2) ≤ greenFunction (ball c (2 * r)) c y := by
  have hd : ‖y - c‖ < r := by simpa only [mem_ball, dist_eq_norm] using hy
  have hd0 : 0 < ‖y - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hsub : closedBall c (3 * r / 2) ⊆ ball c (2 * r) :=
    closedBall_subset_ball (by linarith)
  have hGreen := log_div_le_greenFunction isBounded_ball (by positivity : 0 < 3 * r / 2)
    hsub hd0 (by linarith : ‖y - c‖ < 3 * r / 2)
  have hratio : (3 / 2 : ℝ) ≤ (3 * r / 2) / ‖y - c‖ := by
    apply (le_div_iff₀ hd0).2
    nlinarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 3 / 2) hratio
  have hfac : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  rw [greenFunction_ball_center_comm c (2 * r) c y]
  exact (mul_le_mul_of_nonneg_left hlog hfac).trans hGreen

/-- A nonatomic measure on the inner disc is controlled by the corresponding
Green potential. The finite-mass and integrability assumptions make this valid
for the real-valued Green kernel, whose value at its pole is zero. -/
theorem inner_disc_mass_le_green_integral {μ : Measure ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) {s : Set ℂ} (hs : MeasurableSet s) (hsball : s ⊆ ball c r)
    (hfinite : μ s ≠ ⊤) (hatom : μ {c} = 0)
    (hint : IntegrableOn (greenFunction (ball c (2 * r)) c) s μ) :
    (2 * Real.pi)⁻¹ * Real.log (3 / 2) * (μ s).toReal ≤
      ∫ y in s, greenFunction (ball c (2 * r)) c y ∂μ := by
  have hne : ∀ᵐ y ∂(μ.restrict s), y ≠ c := by
    apply ae_iff.mpr
    have hzero : (μ.restrict s) {c} = 0 :=
      le_antisymm (((Measure.restrict_le_self : μ.restrict s ≤ μ) {c}).trans_eq hatom) bot_le
    simpa only [not_not, ofPred_eq_eq_singleton] using hzero
  have hpoint : ∀ᵐ y ∂(μ.restrict s),
      (2 * Real.pi)⁻¹ * Real.log (3 / 2) ≤ greenFunction (ball c (2 * r)) c y := by
    filter_upwards [ae_restrict_mem hs, hne] with y hy hyc
    exact log_three_halves_le_greenFunction_ball_center hr (hsball hy) hyc
  have hconst : IntegrableOn (fun _ : ℂ => (2 * Real.pi)⁻¹ * Real.log (3 / 2)) s μ :=
    integrableOn_const hfinite
  have h := integral_mono_ae hconst hint hpoint
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_comm] using h

/-- The inner-disc mass estimate remains valid when the potential is integrated
over a larger set. -/
theorem inner_disc_mass_le_larger_green_integral {μ : Measure ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) {s L : Set ℂ} (hs : MeasurableSet s) (hsball : s ⊆ ball c r)
    (hsL : s ⊆ L) (hfinite : μ s ≠ ⊤) (hatom : μ {c} = 0)
    (hint : IntegrableOn (greenFunction (ball c (2 * r)) c) L μ) :
    (2 * Real.pi)⁻¹ * Real.log (3 / 2) * (μ s).toReal ≤
      ∫ y in L, greenFunction (ball c (2 * r)) c y ∂μ := by
  calc
    _ ≤ ∫ y in s, greenFunction (ball c (2 * r)) c y ∂μ :=
      inner_disc_mass_le_green_integral hr hs hsball hfinite hatom (hint.mono_set hsL)
    _ ≤ ∫ y in L, greenFunction (ball c (2 * r)) c y ∂μ :=
      setIntegral_mono_set hint (Filter.Eventually.of_forall (greenFunction_nonneg isBounded_ball c))
        (Filter.Eventually.of_forall hsL)

/-- The constant in the disc Green lower bound is strictly positive. -/
theorem log_three_halves_green_constant_pos :
    0 < (2 * Real.pi)⁻¹ * Real.log (3 / 2) := by
  exact mul_pos (by positivity) (Real.log_pos (by norm_num))

end HarmonicBalls.Section6
