import Mathlib

/-!
# Radial homeomorphism `ℂ ≃ₜ ball c R`, the identity on `closedBall c ρ`
(fp-S11ah-11-13-steps-4-5, owner n4; auxiliary to `S11ah/LocalMeasurable.lean`).

For `0 < ρ < R` and a centre `c`, the radial profile `radialG` is the identity on `[0, ρ]` and increases
homeomorphically from `[ρ, ∞)` onto `[ρ, R)`; `radialH` is its inverse on `[0, R)`. Their radial lifts
`radialOut x = (radialG |x| / |x|) x` and `radialIn y = (radialH |y| / |y|) y` give a homeomorphism
`radialHomeo c : ℂ ≃ₜ ball c R` (translated by `c`) which is the identity on `closedBall c ρ`.
This transports a length metric given on the disc `ball c R` to a whole-plane one (Lean-only device; no new
mathematics: it is used to reduce the local certificate event to `measurableSet_certificateEvent`).
-/

open Metric Set Filter Topology

noncomputable section

namespace FirstPassS11ah

/-- Radial profile: the identity on `[0, ρ]`, increasing from `ρ` to `R` on `[ρ, ∞)`. -/
def radialG (ρ R t : ℝ) : ℝ :=
  min t ρ + (R - ρ) * max (t - ρ) 0 / (max (t - ρ) 0 + (R - ρ))

/-- Inverse of `radialG` on `[0, R)`. -/
def radialH (ρ R s : ℝ) : ℝ :=
  min s ρ + (R - ρ) * max (s - ρ) 0 / ((R - ρ) - max (s - ρ) 0)

section Profile

variable {ρ R : ℝ}

lemma radialG_of_le (_hρ : 0 < ρ) {t : ℝ} (ht : t ≤ ρ) : radialG ρ R t = t := by
  unfold radialG
  have h0 : max (t - ρ) 0 = 0 := max_eq_right (by linarith)
  rw [h0, min_eq_left ht]
  simp

lemma radialH_of_le (_hρ : 0 < ρ) {s : ℝ} (hs : s ≤ ρ) : radialH ρ R s = s := by
  unfold radialH
  have h0 : max (s - ρ) 0 = 0 := max_eq_right (by linarith)
  rw [h0, min_eq_left hs]
  simp

lemma radialG_nonneg (hρ : 0 < ρ) (hR : ρ < R) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ radialG ρ R t := by
  unfold radialG
  have hu : 0 ≤ max (t - ρ) 0 := le_max_right _ _
  exact add_nonneg (le_min ht hρ.le)
    (div_nonneg (mul_nonneg (by linarith) hu) (by linarith))

lemma radialG_pos (hρ : 0 < ρ) (hR : ρ < R) {t : ℝ} (ht : 0 < t) : 0 < radialG ρ R t := by
  unfold radialG
  have hu : 0 ≤ max (t - ρ) 0 := le_max_right _ _
  exact add_pos_of_pos_of_nonneg (lt_min ht hρ)
    (div_nonneg (mul_nonneg (by linarith) hu) (by linarith))

lemma radialG_lt (hR : ρ < R) (t : ℝ) : radialG ρ R t < R := by
  have ha : 0 < R - ρ := by linarith
  have hu : 0 ≤ max (t - ρ) 0 := le_max_right _ _
  have hX : (R - ρ) * max (t - ρ) 0 / (max (t - ρ) 0 + (R - ρ)) < R - ρ := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [mul_pos ha ha]
  have hm : min t ρ ≤ ρ := min_le_right _ _
  unfold radialG
  linarith

lemma radialH_nonneg (hρ : 0 < ρ) (hR : ρ < R) {s : ℝ} (hs : 0 ≤ s) (hsR : s < R) :
    0 ≤ radialH ρ R s := by
  unfold radialH
  have ha : 0 < R - ρ := by linarith
  have hv : max (s - ρ) 0 < R - ρ := max_lt (by linarith) ha
  exact add_nonneg (le_min hs hρ.le)
    (div_nonneg (mul_nonneg ha.le (le_max_right _ _)) (by linarith))

lemma radialH_pos (hρ : 0 < ρ) (hR : ρ < R) {s : ℝ} (hs : 0 < s) (hsR : s < R) :
    0 < radialH ρ R s := by
  unfold radialH
  have ha : 0 < R - ρ := by linarith
  have hv : max (s - ρ) 0 < R - ρ := max_lt (by linarith) ha
  exact add_pos_of_pos_of_nonneg (lt_min hs hρ)
    (div_nonneg (mul_nonneg ha.le (le_max_right _ _)) (by linarith))

lemma radialH_radialG (hρ : 0 < ρ) (hR : ρ < R) {t : ℝ} (_ht : 0 ≤ t) :
    radialH ρ R (radialG ρ R t) = t := by
  have ha : 0 < R - ρ := by linarith
  rcases le_total t ρ with h | h
  · rw [radialG_of_le hρ h, radialH_of_le hρ h]
  · have hmin : min t ρ = ρ := min_eq_right h
    have hu : max (t - ρ) 0 = t - ρ := max_eq_left (by linarith)
    have hG : radialG ρ R t = ρ + (R - ρ) * (t - ρ) / ((t - ρ) + (R - ρ)) := by
      unfold radialG
      rw [hmin, hu]
    have hv0 : 0 ≤ (R - ρ) * (t - ρ) / ((t - ρ) + (R - ρ)) :=
      div_nonneg (mul_nonneg ha.le (by linarith)) (by linarith)
    rw [hG]
    unfold radialH
    have hmax : max (ρ + (R - ρ) * (t - ρ) / ((t - ρ) + (R - ρ)) - ρ) 0
        = (R - ρ) * (t - ρ) / ((t - ρ) + (R - ρ)) := by
      rw [add_sub_cancel_left]
      exact max_eq_left hv0
    rw [hmax, min_eq_right (by linarith)]
    have hden : (R - ρ) - (R - ρ) * (t - ρ) / ((t - ρ) + (R - ρ))
        = (R - ρ) * (R - ρ) / ((t - ρ) + (R - ρ)) := by
      field_simp
      ring
    rw [hden]
    have hpos1 : (t - ρ) + (R - ρ) ≠ 0 := by linarith
    have hpos2 : R - ρ ≠ 0 := ha.ne'
    field_simp
    ring

lemma radialG_radialH (hρ : 0 < ρ) (hR : ρ < R) {s : ℝ} (_hs : 0 ≤ s) (hsR : s < R) :
    radialG ρ R (radialH ρ R s) = s := by
  have ha : 0 < R - ρ := by linarith
  rcases le_total s ρ with h | h
  · rw [radialH_of_le hρ h, radialG_of_le hρ h]
  · have hmin : min s ρ = ρ := min_eq_right h
    have hu : max (s - ρ) 0 = s - ρ := max_eq_left (by linarith)
    have hH : radialH ρ R s = ρ + (R - ρ) * (s - ρ) / ((R - ρ) - (s - ρ)) := by
      unfold radialH
      rw [hmin, hu]
    have hden0 : 0 < (R - ρ) - (s - ρ) := by linarith
    have hw0 : 0 ≤ (R - ρ) * (s - ρ) / ((R - ρ) - (s - ρ)) :=
      div_nonneg (mul_nonneg ha.le (by linarith)) hden0.le
    rw [hH]
    unfold radialG
    have hmax : max (ρ + (R - ρ) * (s - ρ) / ((R - ρ) - (s - ρ)) - ρ) 0
        = (R - ρ) * (s - ρ) / ((R - ρ) - (s - ρ)) := by
      rw [add_sub_cancel_left]
      exact max_eq_left hw0
    rw [hmax, min_eq_right (by linarith)]
    have hsum : (R - ρ) * (s - ρ) / ((R - ρ) - (s - ρ)) + (R - ρ)
        = (R - ρ) * (R - ρ) / ((R - ρ) - (s - ρ)) := by
      field_simp
      ring
    rw [hsum]
    have hne : (R - ρ) - (s - ρ) ≠ 0 := hden0.ne'
    field_simp
    ring

lemma radialG_continuous (_hρ : 0 < ρ) (hR : ρ < R) : Continuous (radialG ρ R) := by
  unfold radialG
  have hne : ∀ t : ℝ, max (t - ρ) 0 + (R - ρ) ≠ 0 := fun t => by
    have := le_max_right (t - ρ) 0
    have : 0 < R - ρ := by linarith
    linarith
  exact (continuous_id.min continuous_const).add
    (Continuous.div (by fun_prop) (by fun_prop) hne)

lemma radialH_continuousAt (_hρ : 0 < ρ) (hR : ρ < R) {s : ℝ} (hs : s < R) :
    ContinuousAt (radialH ρ R) s := by
  unfold radialH
  have ha : 0 < R - ρ := by linarith
  have hv : max (s - ρ) 0 < R - ρ := max_lt (by linarith) ha
  have hne : (R - ρ) - max (s - ρ) 0 ≠ 0 := by linarith
  exact ContinuousAt.add (by fun_prop)
    (ContinuousAt.div (by fun_prop) (by fun_prop) hne)

end Profile

section Lift

variable {ρ R : ℝ}

/-- The radial lift `x ↦ (radialG |x| / |x|) · x` on the whole plane, centred at `0`. -/
def radialOut (ρ R : ℝ) (x : ℂ) : ℂ := ((radialG ρ R ‖x‖ / ‖x‖ : ℝ) : ℂ) * x

/-- Inverse radial lift `y ↦ (radialH |y| / |y|) · y` (meaningful for `|y| < R`). -/
def radialIn (ρ R : ℝ) (y : ℂ) : ℂ := ((radialH ρ R ‖y‖ / ‖y‖ : ℝ) : ℂ) * y

lemma radialOut_of_le (hρ : 0 < ρ) {x : ℂ} (hx : ‖x‖ ≤ ρ) : radialOut ρ R x = x := by
  by_cases h0 : x = 0
  · subst h0; simp [radialOut]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 h0
    unfold radialOut
    rw [radialG_of_le hρ hx, div_self hn]
    simp

lemma radialIn_of_le (hρ : 0 < ρ) {y : ℂ} (hy : ‖y‖ ≤ ρ) : radialIn ρ R y = y := by
  by_cases h0 : y = 0
  · subst h0; simp [radialIn]
  · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 h0
    unfold radialIn
    rw [radialH_of_le hρ hy, div_self hn]
    simp

lemma norm_radialOut (hρ : 0 < ρ) (hR : ρ < R) (x : ℂ) :
    ‖radialOut ρ R x‖ = radialG ρ R ‖x‖ := by
  by_cases hx : x = 0
  · subst hx
    have h0 : radialG ρ R 0 = 0 := radialG_of_le hρ (by linarith)
    simp [radialOut, h0]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hG := radialG_nonneg hρ hR (norm_nonneg x)
    unfold radialOut
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg hG,
      abs_of_pos hn]
    field_simp

lemma norm_radialIn (hρ : 0 < ρ) (hR : ρ < R) {y : ℂ} (hy : ‖y‖ < R) :
    ‖radialIn ρ R y‖ = radialH ρ R ‖y‖ := by
  by_cases h0 : y = 0
  · subst h0
    have h0' : radialH ρ R 0 = 0 := radialH_of_le hρ (by linarith)
    simp [radialIn, h0']
  · have hn : 0 < ‖y‖ := norm_pos_iff.2 h0
    have hH := radialH_nonneg hρ hR (norm_nonneg y) hy
    unfold radialIn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg hH,
      abs_of_pos hn]
    field_simp

lemma radialIn_radialOut (hρ : 0 < ρ) (hR : ρ < R) (x : ℂ) :
    radialIn ρ R (radialOut ρ R x) = x := by
  by_cases hx : x = 0
  · subst hx; simp [radialOut, radialIn]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hnpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hGne : radialG ρ R ‖x‖ ≠ 0 := (radialG_pos hρ hR hnpos).ne'
    have key : radialIn ρ R (radialOut ρ R x)
        = ((radialH ρ R (radialG ρ R ‖x‖) / radialG ρ R ‖x‖ : ℝ) : ℂ)
          * (((radialG ρ R ‖x‖ / ‖x‖ : ℝ) : ℂ) * x) := by
      unfold radialIn
      rw [norm_radialOut hρ hR x]
      rfl
    rw [key, radialH_radialG hρ hR (norm_nonneg x)]
    rw [← mul_assoc, ← Complex.ofReal_mul]
    have hc : ‖x‖ / radialG ρ R ‖x‖ * (radialG ρ R ‖x‖ / ‖x‖) = 1 := by
      field_simp
    rw [hc, Complex.ofReal_one, one_mul]

lemma radialOut_radialIn (hρ : 0 < ρ) (hR : ρ < R) {y : ℂ} (hy : ‖y‖ < R) :
    radialOut ρ R (radialIn ρ R y) = y := by
  by_cases hy0 : y = 0
  · subst hy0; simp [radialOut, radialIn]
  · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
    have hnpos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hHne : radialH ρ R ‖y‖ ≠ 0 := (radialH_pos hρ hR hnpos hy).ne'
    have key : radialOut ρ R (radialIn ρ R y)
        = ((radialG ρ R (radialH ρ R ‖y‖) / radialH ρ R ‖y‖ : ℝ) : ℂ)
          * (((radialH ρ R ‖y‖ / ‖y‖ : ℝ) : ℂ) * y) := by
      unfold radialOut
      rw [norm_radialIn hρ hR hy]
      rfl
    rw [key, radialG_radialH hρ hR (norm_nonneg y) hy]
    rw [← mul_assoc, ← Complex.ofReal_mul]
    have hc : ‖y‖ / radialH ρ R ‖y‖ * (radialH ρ R ‖y‖ / ‖y‖) = 1 := by
      field_simp
    rw [hc, Complex.ofReal_one, one_mul]

lemma radialOut_continuous (hρ : 0 < ρ) (hR : ρ < R) : Continuous (radialOut ρ R) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x = 0
  · subst hx
    refine continuousAt_id.congr ?_
    exact Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) hρ)
      fun z hz => (radialOut_of_le hρ (le_of_lt (mem_ball_zero_iff.1 hz))).symm
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have h1 : ContinuousAt (fun z : ℂ => radialG ρ R ‖z‖ / ‖z‖) x :=
      ContinuousAt.div (((radialG_continuous hρ hR).comp continuous_norm).continuousAt)
        continuous_norm.continuousAt hn
    exact (Complex.continuous_ofReal.continuousAt.comp h1).mul continuousAt_id

lemma radialIn_continuousAt (hρ : 0 < ρ) (hR : ρ < R) {y : ℂ} (hy : ‖y‖ < R) :
    ContinuousAt (radialIn ρ R) y := by
  by_cases hy0 : y = 0
  · subst hy0
    refine continuousAt_id.congr ?_
    exact Filter.eventually_of_mem (ball_mem_nhds (0 : ℂ) hρ)
      fun z hz => (radialIn_of_le hρ (le_of_lt (mem_ball_zero_iff.1 hz))).symm
  · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
    have h1 : ContinuousAt (fun z : ℂ => radialH ρ R ‖z‖ / ‖z‖) y :=
      ContinuousAt.div
        ((radialH_continuousAt hρ hR hy).comp continuous_norm.continuousAt)
        continuous_norm.continuousAt hn
    exact (Complex.continuous_ofReal.continuousAt.comp h1).mul continuousAt_id

/-- The radial homeomorphism lift of `ℂ` onto `ball c R`, the identity on `closedBall c ρ`. -/
def radialLift (c : ℂ) (ρ R : ℝ) (x : ℂ) : ℂ := c + radialOut ρ R (x - c)

/-- Inverse of `radialLift` on `ball c R`. -/
def radialLiftInv (c : ℂ) (ρ R : ℝ) (y : ℂ) : ℂ := c + radialIn ρ R (y - c)

/-- **Radial homeomorphism** `ℂ ≃ₜ ball c R` (Lean device for `S11ah/LocalMeasurable.lean`). -/
def radialHomeo (c : ℂ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : ρ < R) : ℂ ≃ₜ ball c R where
  toFun x := ⟨radialLift c ρ R x, by
    rw [Metric.mem_ball, dist_eq_norm, radialLift, add_sub_cancel_left,
      norm_radialOut hρ hR]
    exact radialG_lt hR _⟩
  invFun y := radialLiftInv c ρ R y
  left_inv x := by
    have h1 : c + radialOut ρ R (x - c) - c = radialOut ρ R (x - c) := by ring
    simp only [radialLiftInv, radialLift]
    rw [h1, radialIn_radialOut hρ hR]
    ring
  right_inv y := by
    have hy : ‖(y : ℂ) - c‖ < R := by
      have := y.2
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact this
    apply Subtype.ext
    have h1 : c + radialIn ρ R ((y : ℂ) - c) - c = radialIn ρ R ((y : ℂ) - c) := by ring
    simp only [radialLiftInv, radialLift]
    rw [h1, radialOut_radialIn hρ hR hy]
    ring
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.add ((radialOut_continuous hρ hR).comp (continuous_id.sub continuous_const))
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hy : ‖(y : ℂ) - c‖ < R := by
      have := y.2
      rw [Metric.mem_ball, dist_eq_norm] at this
      exact this
    have hsub : ContinuousAt (fun z : ℂ => z - c) (y : ℂ) := continuousAt_id.sub continuousAt_const
    have hrad : ContinuousAt (radialIn ρ R) ((y : ℂ) - c) := radialIn_continuousAt hρ hR hy
    have hg : ContinuousAt (fun z : ℂ => c + radialIn ρ R (z - c)) (y : ℂ) :=
      continuousAt_const.add (ContinuousAt.comp (f := fun z : ℂ => z - c) (x := (y : ℂ)) hrad hsub)
    exact hg.comp continuous_subtype_val.continuousAt

lemma radialHomeo_apply_of_norm_le (c : ℂ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : ρ < R) {x : ℂ}
    (hx : ‖x - c‖ ≤ ρ) : ((radialHomeo c hρ hR x : ball c R) : ℂ) = x := by
  show c + radialOut ρ R (x - c) = x
  rw [radialOut_of_le hρ hx]
  ring

end Lift

end FirstPassS11ah

end
