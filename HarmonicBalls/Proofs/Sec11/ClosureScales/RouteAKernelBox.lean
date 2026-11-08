import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteAKernel

/-! # Route (A) analytic core: the logarithmic kernel on a disc (C2, step K-a and K-b)

The covariance kernel of the whole-plane GFF is `wholePlaneCov z w = log(max(|z|,1) max(|w|,1) / |z - w|)`
(`HarmonicBalls/Defs/GFF.lean:39`). On a disc `ball 0 M` it equals the logarithmic kernel `-log|z - w|` up to the
bounded terms `log max(|z|,1) + log max(|w|,1) ∈ [0, 2 log max(M,1)]`. This file proves the pointwise bound (K-a)
and the uniform bound of the integral of the kernel over a disc (K-b), with the constant `kernelBoxConst M`, which is
finite (`RouteAKernel.lean`). These are the inputs of the Schur test for the pairing covariance.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- The constant `2 log max(M, 1)` bounding the non-logarithmic part of the kernel on `ball 0 M`. -/
def kernelLogConst (M : ℝ) : ℝ := 2 * Real.log (max M 1)

theorem kernelLogConst_nonneg (M : ℝ) : 0 ≤ kernelLogConst M := by
  unfold kernelLogConst
  have h1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  have h2 : 0 ≤ Real.log (max M 1) := Real.log_nonneg h1
  linarith

/-- (K-a) Pointwise kernel bound on a disc:
`|wholePlaneCov x y| ≤ |log ‖x - y‖| + 2 log max(M, 1)` whenever `‖x‖ ≤ M` and `‖y‖ ≤ M`. -/
theorem abs_wholePlaneCov_le_of_norm_le {M : ℝ} {x y : ℂ} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    |wholePlaneCov x y| ≤ |Real.log ‖x - y‖| + kernelLogConst M := by
  by_cases hxy : x = y
  · subst hxy
    have h0 : wholePlaneCov x x = 0 := by
      simp [wholePlaneCov]
    rw [h0, abs_zero]
    exact add_nonneg (abs_nonneg _) (kernelLogConst_nonneg M)
  · have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have h1 : 0 < max ‖x‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have h2 : 0 < max ‖y‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hK : wholePlaneCov x y
        = Real.log (max ‖x‖ 1) + Real.log (max ‖y‖ 1) - Real.log ‖x - y‖ := by
      unfold wholePlaneCov
      rw [Real.log_div (mul_pos h1 h2).ne' hpos.ne', Real.log_mul h1.ne' h2.ne']
    have hA : 0 ≤ Real.log (max ‖x‖ 1) := Real.log_nonneg (le_max_right _ _)
    have hB : 0 ≤ Real.log (max ‖y‖ 1) := Real.log_nonneg (le_max_right _ _)
    have hAM : Real.log (max ‖x‖ 1) ≤ Real.log (max M 1) :=
      Real.log_le_log h1 (max_le_max hx le_rfl)
    have hBM : Real.log (max ‖y‖ 1) ≤ Real.log (max M 1) :=
      Real.log_le_log h2 (max_le_max hy le_rfl)
    unfold kernelLogConst
    rw [hK]
    have hL1 := le_abs_self (Real.log ‖x - y‖)
    have hL2 := neg_abs_le (Real.log ‖x - y‖)
    have hL3 := neg_le_abs (Real.log ‖x - y‖)
    rw [abs_le]
    constructor <;> linarith

/-- (K-b, translation) For `‖x‖ ≤ M`, the logarithmic part of the kernel integrates over `ball 0 M` at most as
over `ball 0 (2M)`: the translation `w = x - y` maps `ball 0 M` into `ball 0 (2M)`. -/
theorem lintegral_ball_ofReal_abs_log_sub_le {M : ℝ} {x : ℂ} (hx : ‖x‖ ≤ M) :
    ∫⁻ y in ball (0 : ℂ) M, ENNReal.ofReal |Real.log ‖x - y‖|
      ≤ ∫⁻ w in ball (0 : ℂ) (2 * M), ENNReal.ofReal |Real.log ‖w‖| := by
  set g : ℂ → ℝ≥0∞ := (ball (0 : ℂ) (2 * M)).indicator fun w => ENNReal.ofReal |Real.log ‖w‖| with hg
  calc ∫⁻ y in ball (0 : ℂ) M, ENNReal.ofReal |Real.log ‖x - y‖|
      = ∫⁻ y in ball (0 : ℂ) M, g (x - y) := by
        refine setLIntegral_congr_fun measurableSet_ball (fun y hy => ?_)
        have hy' : ‖y‖ < M := mem_ball_zero_iff.mp hy
        have hmem : x - y ∈ ball (0 : ℂ) (2 * M) := by
          rw [mem_ball_zero_iff]
          have := norm_sub_le x y
          linarith
        rw [hg, indicator_of_mem hmem]
    _ ≤ ∫⁻ y, g (x - y) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, g y := lintegral_sub_left_eq_self g x
    _ = ∫⁻ w in ball (0 : ℂ) (2 * M), ENNReal.ofReal |Real.log ‖w‖| := by
        rw [hg, lintegral_indicator measurableSet_ball]

/-- The constant `K_M = ∫_{B_{2M}} |log|w|| + 2 log max(M,1) |B_M|` of the Schur bound for the pairing covariance. -/
def kernelBoxConst (M : ℝ) : ℝ≥0∞ :=
  (∫⁻ w in ball (0 : ℂ) (2 * M), ENNReal.ofReal |Real.log ‖w‖|)
    + ENNReal.ofReal (kernelLogConst M) * volume (ball (0 : ℂ) M)

/-- The constant `K_M` is finite. -/
theorem kernelBoxConst_lt_top (M : ℝ) : kernelBoxConst M < ⊤ := by
  unfold kernelBoxConst
  refine ENNReal.add_lt_top.mpr ⟨?_, ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top⟩
  exact (integrableOn_abs_log_norm_ball (2 * M)).lintegral_lt_top

/-- (K-b) For `‖x‖ ≤ M` (and `0 ≤ M`), the covariance kernel integrates over `ball 0 M` with the bound `K_M`. -/
theorem lintegral_ball_ofReal_abs_wholePlaneCov_le {M : ℝ} {x : ℂ} (hx : ‖x‖ ≤ M) :
    ∫⁻ y in ball (0 : ℂ) M, ENNReal.ofReal |wholePlaneCov x y| ≤ kernelBoxConst M := by
  have hpt : ∀ y ∈ ball (0 : ℂ) M, ENNReal.ofReal |wholePlaneCov x y|
      ≤ ENNReal.ofReal |Real.log ‖x - y‖| + ENNReal.ofReal (kernelLogConst M) := by
    intro y hy
    have hy' : ‖y‖ ≤ M := (mem_ball_zero_iff.mp hy).le
    rw [← ENNReal.ofReal_add (abs_nonneg _) (kernelLogConst_nonneg M)]
    exact ENNReal.ofReal_le_ofReal (abs_wholePlaneCov_le_of_norm_le hx hy')
  calc ∫⁻ y in ball (0 : ℂ) M, ENNReal.ofReal |wholePlaneCov x y|
      ≤ ∫⁻ y in ball (0 : ℂ) M,
          (ENNReal.ofReal |Real.log ‖x - y‖| + ENNReal.ofReal (kernelLogConst M)) :=
        setLIntegral_mono' measurableSet_ball hpt
    _ = (∫⁻ y in ball (0 : ℂ) M, ENNReal.ofReal |Real.log ‖x - y‖|)
          + ENNReal.ofReal (kernelLogConst M) * volume (ball (0 : ℂ) M) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ kernelBoxConst M := by
        unfold kernelBoxConst
        exact add_le_add (lintegral_ball_ofReal_abs_log_sub_le hx) le_rfl


/-- Two-term AM-GM in `ℝ≥0∞`: `2 · (√a·√b) ≤ a + b` written with `ofReal`. -/
theorem two_mul_ofReal_mul_ofReal_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (ENNReal.ofReal a * ENNReal.ofReal b)
      ≤ ENNReal.ofReal a * ENNReal.ofReal a + ENNReal.ofReal b * ENNReal.ofReal b := by
  have h1 : ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := (ENNReal.ofReal_mul ha).symm
  have h2 : ENNReal.ofReal a * ENNReal.ofReal a = ENNReal.ofReal (a * a) := (ENNReal.ofReal_mul ha).symm
  have h3 : ENNReal.ofReal b * ENNReal.ofReal b = ENNReal.ofReal (b * b) := (ENNReal.ofReal_mul hb).symm
  have h4 : ENNReal.ofReal (a * a) + ENNReal.ofReal (b * b) = ENNReal.ofReal (a * a + b * b) :=
    (ENNReal.ofReal_add (mul_nonneg ha ha) (mul_nonneg hb hb)).symm
  have h5 : (2 : ℝ≥0∞) * ENNReal.ofReal (a * b) = ENNReal.ofReal (2 * (a * b)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [h1, h2, h3, h4, h5]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (a - b)])

/-- The squared value of a real number as a product of `ofReal |t|`. -/
theorem ofReal_sq_eq_mul_abs (t : ℝ) :
    ENNReal.ofReal (t ^ 2) = ENNReal.ofReal |t| * ENNReal.ofReal |t| := by
  rw [← ENNReal.ofReal_mul (abs_nonneg t), sq, abs_mul_abs_self]

/-- The two cut-off integrands of the Schur test: `(f x)² 1_B(y) |K(x,y)|` and `(f y)² 1_B(x) |K(x,y)|`. -/
def schurT1 (f : ℂ → ℝ) (M : ℝ) (x y : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (f x ^ 2) * ((ball (0 : ℂ) M).indicator (fun _ => (1 : ℝ≥0∞)) y * ENNReal.ofReal |wholePlaneCov x y|)

def schurT2 (f : ℂ → ℝ) (M : ℝ) (x y : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (f y ^ 2) * ((ball (0 : ℂ) M).indicator (fun _ => (1 : ℝ≥0∞)) x * ENNReal.ofReal |wholePlaneCov x y|)

/-- The indicator of a set times a function, integrated over the plane, is the set integral. -/
theorem lintegral_indicator_one_mul_eq {B : Set ℂ} (hB : MeasurableSet B) (g : ℂ → ℝ≥0∞) :
    ∫⁻ y, B.indicator (fun _ => (1 : ℝ≥0∞)) y * g y = ∫⁻ y in B, g y := by
  have h : ∀ y, B.indicator (fun _ => (1 : ℝ≥0∞)) y * g y = B.indicator g y := fun y => by
    by_cases hy : y ∈ B <;> simp [hy]
  simp_rw [h]
  exact lintegral_indicator hB g

/-- (Schur test, lintegral form) For a measurable `f` supported in `ball 0 M`, the logarithmic Schur integral of
`|f|` against the covariance kernel is bounded by `K_M ∫ f²` (Schur test; the kernel is symmetric). -/
theorem lintegral_schur_wholePlaneCov {M : ℝ} {f : ℂ → ℝ} (hfm : Measurable f)
    (hsupp : ∀ x, x ∉ ball (0 : ℂ) M → f x = 0) :
    ∫⁻ x, ENNReal.ofReal |f x| * ∫⁻ y, ENNReal.ofReal |f y| * ENNReal.ofReal |wholePlaneCov x y|
      ≤ (2 * kernelBoxConst M) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
  have hKm : Measurable fun p : ℂ × ℂ => wholePlaneCov p.1 p.2 := by
    unfold wholePlaneCov
    refine Real.measurable_log.comp ?_
    exact ((measurable_fst.norm.max measurable_const).mul (measurable_snd.norm.max measurable_const)).div
      (measurable_fst.sub measurable_snd).norm
  have hk : Measurable fun p : ℂ × ℂ => ENNReal.ofReal |wholePlaneCov p.1 p.2| :=
    (continuous_abs.measurable.comp hKm).ennreal_ofReal
  have hχm : Measurable ((ball (0 : ℂ) M).indicator fun _ => (1 : ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_ball
  have hfsq : Measurable fun x => ENNReal.ofReal (f x ^ 2) := (hfm.pow_const 2).ennreal_ofReal
  have hT1 : Measurable fun p : ℂ × ℂ => schurT1 f M p.1 p.2 := by
    unfold schurT1
    exact (hfsq.comp measurable_fst).mul ((hχm.comp measurable_snd).mul hk)
  have hT2 : Measurable fun p : ℂ × ℂ => schurT2 f M p.1 p.2 := by
    unfold schurT2
    exact (hfsq.comp measurable_snd).mul ((hχm.comp measurable_fst).mul hk)
  -- pointwise Schur inequality with the cut-off `1_B`
  have hpt : ∀ x y : ℂ,
      2 * (ENNReal.ofReal |f x| * (ENNReal.ofReal |f y| * ENNReal.ofReal |wholePlaneCov x y|))
        ≤ schurT1 f M x y + schurT2 f M x y := by
    intro x y
    unfold schurT1 schurT2
    by_cases hx : x ∈ ball (0 : ℂ) M
    · by_cases hy : y ∈ ball (0 : ℂ) M
      · simp only [indicator_of_mem hx, indicator_of_mem hy, one_mul]
        rw [ofReal_sq_eq_mul_abs (f x), ofReal_sq_eq_mul_abs (f y)]
        calc 2 * (ENNReal.ofReal |f x| * (ENNReal.ofReal |f y| * ENNReal.ofReal |wholePlaneCov x y|))
            = (2 * (ENNReal.ofReal |f x| * ENNReal.ofReal |f y|)) * ENNReal.ofReal |wholePlaneCov x y| := by
              ring
          _ ≤ (ENNReal.ofReal |f x| * ENNReal.ofReal |f x| + ENNReal.ofReal |f y| * ENNReal.ofReal |f y|)
                * ENNReal.ofReal |wholePlaneCov x y| := by
              gcongr
              exact two_mul_ofReal_mul_ofReal_le _ _ (abs_nonneg _) (abs_nonneg _)
          _ = _ := by ring
      · have hy0 : f y = 0 := hsupp y hy
        simp [hy0]
    · have hx0 : f x = 0 := hsupp x hx
      simp [hx0]
  -- Step 1: twice the Schur integral is at most the integral of the two cut-off integrands
  have h2I : 2 * ∫⁻ x, ENNReal.ofReal |f x| * ∫⁻ y, ENNReal.ofReal |f y| * ENNReal.ofReal |wholePlaneCov x y|
      ≤ ∫⁻ x, ∫⁻ y, (schurT1 f M x y + schurT2 f M x y) := by
    rw [← lintegral_const_mul' 2 _ (by simp)]
    refine lintegral_mono fun x => ?_
    calc 2 * (ENNReal.ofReal |f x| * ∫⁻ y, ENNReal.ofReal |f y| * ENNReal.ofReal |wholePlaneCov x y|)
        = ∫⁻ y, 2 * (ENNReal.ofReal |f x|
            * (ENNReal.ofReal |f y| * ENNReal.ofReal |wholePlaneCov x y|)) := by
          rw [lintegral_const_mul' 2 _ (by simp),
            lintegral_const_mul' (ENNReal.ofReal |f x|) _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ y, (schurT1 f M x y + schurT2 f M x y) := lintegral_mono fun y => hpt x y
  -- Step 2: splitting the sum
  have hA : Measurable fun x => ∫⁻ y, schurT1 f M x y := hT1.lintegral_prod_right'
  have hsplit : ∫⁻ x, ∫⁻ y, (schurT1 f M x y + schurT2 f M x y)
      = (∫⁻ x, ∫⁻ y, schurT1 f M x y) + ∫⁻ x, ∫⁻ y, schurT2 f M x y := by
    rw [← lintegral_add_left hA]
    refine lintegral_congr fun x => ?_
    have hT1x : Measurable fun y : ℂ => schurT1 f M x y :=
      hT1.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_add_left hT1x]
  -- Step 3: the first integrand, using the bound of K-b at `x`
  have hT1b : ∫⁻ x, ∫⁻ y, schurT1 f M x y ≤ kernelBoxConst M * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
    have hinner : ∀ x, ∫⁻ y, schurT1 f M x y ≤ ENNReal.ofReal (f x ^ 2) * kernelBoxConst M := by
      intro x
      by_cases hx : x ∈ ball (0 : ℂ) M
      · have hxM : ‖x‖ ≤ M := (mem_ball_zero_iff.mp hx).le
        have hstep : ∫⁻ y, schurT1 f M x y
            = ENNReal.ofReal (f x ^ 2) * ∫⁻ y in ball (0 : ℂ) M, ENNReal.ofReal |wholePlaneCov x y| := by
          unfold schurT1
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one_mul_eq measurableSet_ball]
        rw [hstep]
        gcongr
        exact lintegral_ball_ofReal_abs_wholePlaneCov_le hxM
      · have hx0 : f x = 0 := hsupp x hx
        simp [schurT1, hx0]
    calc ∫⁻ x, ∫⁻ y, schurT1 f M x y ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) * kernelBoxConst M :=
          lintegral_mono hinner
      _ = (∫⁻ x, ENNReal.ofReal (f x ^ 2)) * kernelBoxConst M :=
          lintegral_mul_const' _ _ (kernelBoxConst_lt_top M).ne
      _ = kernelBoxConst M * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := mul_comm _ _
  -- Step 4: the second integrand, after exchanging the integrals and using the symmetry of the kernel
  have hT2b : ∫⁻ x, ∫⁻ y, schurT2 f M x y ≤ kernelBoxConst M * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
    rw [lintegral_lintegral_swap hT2.aemeasurable]
    have hinner : ∀ y, ∫⁻ x, schurT2 f M x y ≤ ENNReal.ofReal (f y ^ 2) * kernelBoxConst M := by
      intro y
      by_cases hy : y ∈ ball (0 : ℂ) M
      · have hyM : ‖y‖ ≤ M := (mem_ball_zero_iff.mp hy).le
        have hstep : ∫⁻ x, schurT2 f M x y
            = ENNReal.ofReal (f y ^ 2) * ∫⁻ x in ball (0 : ℂ) M, ENNReal.ofReal |wholePlaneCov y x| := by
          unfold schurT2
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_one_mul_eq measurableSet_ball]
          congr 1
          refine setLIntegral_congr_fun measurableSet_ball (fun x _ => ?_)
          rw [wholePlaneCov_comm x y]
        rw [hstep]
        gcongr
        exact lintegral_ball_ofReal_abs_wholePlaneCov_le hyM
      · have hy0 : f y = 0 := hsupp y hy
        simp [schurT2, hy0]
    calc ∫⁻ y, ∫⁻ x, schurT2 f M x y ≤ ∫⁻ y, ENNReal.ofReal (f y ^ 2) * kernelBoxConst M :=
          lintegral_mono hinner
      _ = (∫⁻ y, ENNReal.ofReal (f y ^ 2)) * kernelBoxConst M :=
          lintegral_mul_const' _ _ (kernelBoxConst_lt_top M).ne
      _ = kernelBoxConst M * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := mul_comm _ _
  -- Step 5: combine and cancel the factor 2
  have htwo : 2 * ∫⁻ x, ENNReal.ofReal |f x| * ∫⁻ y, ENNReal.ofReal |f y| * ENNReal.ofReal |wholePlaneCov x y|
      ≤ 2 * (kernelBoxConst M * ∫⁻ x, ENNReal.ofReal (f x ^ 2)) := by
    refine h2I.trans ?_
    rw [hsplit, two_mul]
    exact add_le_add hT1b hT2b
  calc ∫⁻ x, ENNReal.ofReal |f x| * ∫⁻ y, ENNReal.ofReal |f y| * ENNReal.ofReal |wholePlaneCov x y|
      ≤ 2 * ∫⁻ x, ENNReal.ofReal |f x| * ∫⁻ y, ENNReal.ofReal |f y| * ENNReal.ofReal |wholePlaneCov x y| :=
        le_mul_of_one_le_left zero_le one_le_two
    _ ≤ 2 * (kernelBoxConst M * ∫⁻ x, ENNReal.ofReal (f x ^ 2)) := htwo
    _ = (2 * kernelBoxConst M) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by ring


/-- `∫ f²` is finite (in lintegral form) for a bounded function supported in `ball 0 M`. -/
theorem lintegral_ofReal_sq_lt_top {M B : ℝ} {f : ℂ → ℝ} (hsupp : ∀ x, x ∉ ball (0 : ℂ) M → f x = 0)
    (hB : ∀ x, |f x| ≤ B) : ∫⁻ x, ENNReal.ofReal (f x ^ 2) < ⊤ := by
  calc ∫⁻ x, ENNReal.ofReal (f x ^ 2)
      ≤ ∫⁻ x, (ball (0 : ℂ) M).indicator (fun _ => ENNReal.ofReal (B ^ 2)) x := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ ball (0 : ℂ) M
        · rw [indicator_of_mem hx]
          apply ENNReal.ofReal_le_ofReal
          nlinarith [abs_nonneg (f x), sq_abs (f x), hB x]
        · rw [indicator_of_notMem hx, hsupp x hx]
          simp
    _ = ENNReal.ofReal (B ^ 2) * volume (ball (0 : ℂ) M) := by
        rw [lintegral_indicator measurableSet_ball, setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- **Variance bound for the pairings of the whole-plane GFF (C2).** For a bounded measurable `f` supported in
`ball 0 M`, the covariance of the pairing `(h, f)` is bounded by `2 K_M ∫ f²` (Schur test for the logarithmic
kernel `wholePlaneCov`, `HarmonicBalls/Defs/GFF.lean:39`). -/
theorem abs_wholePlaneGFFCov_pairing_le {M B : ℝ} {f : ℂ → ℝ} (hfm : Measurable f)
    (hsupp : ∀ x, x ∉ ball (0 : ℂ) M → f x = 0) (hB : ∀ x, |f x| ≤ B) :
    |wholePlaneGFFCov (GFFObservable.pairing f) (GFFObservable.pairing f)|
      ≤ (2 * kernelBoxConst M).toReal * ∫ x, f x ^ 2 := by
  have hcov : wholePlaneGFFCov (GFFObservable.pairing f) (GFFObservable.pairing f)
      = ∫ x, f x * ∫ y, f y * wholePlaneCov x y := rfl
  rw [hcov]
  have hstep : ∀ x, ‖f x * ∫ y, f y * wholePlaneCov x y‖ₑ
      ≤ ENNReal.ofReal |f x| * ∫⁻ y, ENNReal.ofReal |f y| * ENNReal.ofReal |wholePlaneCov x y| := by
    intro x
    rw [enorm_mul, Real.enorm_eq_ofReal_abs (f x)]
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
    rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  have hlint : ∫⁻ x, ‖f x * ∫ y, f y * wholePlaneCov x y‖ₑ
      ≤ (2 * kernelBoxConst M) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) :=
    (lintegral_mono hstep).trans (lintegral_schur_wholePlaneCov hfm hsupp)
  have hfin : (2 * kernelBoxConst M) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (kernelBoxConst_lt_top M))
      (lintegral_ofReal_sq_lt_top hsupp hB)).ne
  calc |∫ x, f x * ∫ y, f y * wholePlaneCov x y|
      = ‖∫ x, f x * ∫ y, f y * wholePlaneCov x y‖ := (Real.norm_eq_abs _).symm
    _ ≤ (∫⁻ x, ‖f x * ∫ y, f y * wholePlaneCov x y‖ₑ).toReal := by
        simpa only [ofReal_norm] using
          norm_integral_le_lintegral_norm (fun x => f x * ∫ y, f y * wholePlaneCov x y)
    _ ≤ ((2 * kernelBoxConst M) * ∫⁻ x, ENNReal.ofReal (f x ^ 2)).toReal :=
        ENNReal.toReal_mono hfin hlint
    _ = (2 * kernelBoxConst M).toReal * (∫⁻ x, ENNReal.ofReal (f x ^ 2)).toReal := ENNReal.toReal_mul
    _ = (2 * kernelBoxConst M).toReal * ∫ x, f x ^ 2 := by
        rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (f x))
          (hfm.pow_const 2).aestronglyMeasurable]

end HarmonicBalls

end
