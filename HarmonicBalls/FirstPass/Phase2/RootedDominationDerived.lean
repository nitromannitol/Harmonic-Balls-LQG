import HarmonicBalls.FirstPass.S8c.LocalObservation
import HarmonicBalls.Proposed.DuplantierMillerSheffield
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.CircleAverage

/-! # Deterministic steps of the derivation of `LocalRootedFieldMeasureDomination` (Lemma 8.2)

Task `fp-audit-r1-b2-rooted-domination` (worker z3). Route: notes/fp-gaps/CHATGPT-219-hb-8-2-R9-hL1-hWeyl-PRO.md,
section 5 ("Lean-sized derivation of `hL1` from the repaired marked DMS input"). This file proves the steps of that
route that need no probabilistic input:

* Step 1 (local geometry): for `z ∈ D_j = {3 r_j < |z| < 1 - 3 r_j}` the ball `B_{2 r_j}(z)` lies in `B_1(0)` and avoids `0`.
* Step 7 (field after the DMS shift): on `B_{r}(0)`, `dmsShift γ z (x + z) = -γ log |x|`, since `|x + z| < 1`.
* Step 8 (Cameron-Martin correction): the smooth compactly supported `f_z(x) = -α₀ χ(x) log |x + z|`, with `χ = 1` on
  `B_r(0)` and `supp χ ⊆ B̄_{2r}(0)`, is smooth, jointly measurable in `(z, x)`, equal to `-α₀ log |x + z|` on
  `B̄_r(0)`, and has `circleAverage f_z 0 1 = 0`.
* Step 9 (normalisation): `massNormalize r (c • η) = massNormalize r η` for `0 < c < ∞` (the random positive constants
  of the DMS and affine normalisations disappear from the observation).

Not here (BLOCKED, see reports/z3.md): Steps 4-5 (the marked DMS identity must see the circle profile `hcirc`, not only
the pairings `hC`) and the transfer in Steps 10-11 (law identity of the circle profile under the Cameron-Martin measure).
Step 3 is `localRootKernel_ac_ae` (`FirstPass/Closure/LocalRootKernelAc.lean:32`), reused.
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-! ## Step 1: geometry of the local domain -/

/-- The radius `r_j = 1/(16 j)` is positive for `j ≥ 1`. -/
lemma localRadius_pos {j : ℕ} (hj : 1 ≤ j) : 0 < localRadius j := by
  have : (1 : ℝ) ≤ j := by exact_mod_cast hj
  unfold localRadius
  positivity

/-- `r_j ≤ 1/16` for `j ≥ 1`, so `2 r_j < 1`. -/
lemma localRadius_le_sixteenth {j : ℕ} (hj : 1 ≤ j) : localRadius j ≤ 1 / 16 := by
  have : (1 : ℝ) ≤ j := by exact_mod_cast hj
  unfold localRadius
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- `2 r_j < 1` for `j ≥ 1`. -/
lemma two_mul_localRadius_lt_one {j : ℕ} (hj : 1 ≤ j) : 2 * localRadius j < 1 := by
  linarith [localRadius_le_sixteenth hj]

/-- For `z` in the local domain, `B_{2 r_j}(z) ⊆ B_1(0)`. -/
lemma ball_two_mul_localRadius_subset_ball_one {j : ℕ} (hj : 1 ≤ j) {z : ℂ} (hz : z ∈ localDomain j) :
    ball z (2 * localRadius j) ⊆ ball (0 : ℂ) 1 := by
  intro w hw
  have hr := localRadius_pos hj
  have hz2 : ‖z‖ < 1 - 3 * localRadius j := hz.2
  rw [mem_ball, dist_eq_norm] at hw
  rw [mem_ball, dist_zero_right]
  have h1 : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
  linarith

/-- For `z` in the local domain, `0 ∉ B_{2 r_j}(z)`. -/
lemma zero_notMem_ball_two_mul_localRadius {j : ℕ} (hj : 1 ≤ j) {z : ℂ} (hz : z ∈ localDomain j) :
    (0 : ℂ) ∉ ball z (2 * localRadius j) := by
  intro h
  have hr := localRadius_pos hj
  have hz1 : 3 * localRadius j < ‖z‖ := hz.1
  rw [mem_ball, dist_eq_norm, zero_sub, norm_neg] at h
  linarith

/-- For `z` in the local domain and `‖x‖ < r_j`, `‖x + z‖ ≤ 1` (indeed `< 1 - 2 r_j`). -/
lemma norm_add_le_one_of_mem_localDomain {j : ℕ} (hj : 1 ≤ j) {z x : ℂ} (hz : z ∈ localDomain j)
    (hx : ‖x‖ < localRadius j) : ‖x + z‖ ≤ 1 := by
  have hr := localRadius_pos hj
  have hz2 : ‖z‖ < 1 - 3 * localRadius j := hz.2
  have h1 : ‖x + z‖ ≤ ‖x‖ + ‖z‖ := norm_add_le _ _
  linarith

/-! ## Step 7: the DMS shift at the rooted point -/

/-- On `B_r(0)` (for `z` with `‖x + z‖ ≤ 1`), the DMS shift `dmsShift γ z` at the point `x + z` is `-γ log |x|`:
the term `γ log max{|x+z|, 1}` vanishes. -/
lemma dmsShift_add_root {γ : ℝ} {z x : ℂ} (hle : ‖x + z‖ ≤ 1) :
    dmsShift γ z (x + z) = -γ * Real.log ‖x‖ := by
  unfold dmsShift
  rw [add_sub_cancel_right, max_eq_right hle, Real.log_one, mul_zero, add_zero]

/-! ## Step 8: the Cameron-Martin correction `f_z(x) = -α₀ χ(x) log |x + z|` -/

/-- The smooth radial cutoff `χ` of Step 8: `χ = 1` on `B̄_r(0)` and `χ = 0` off `B_{2r}(0)`. -/
noncomputable def cmCutoff {r : ℝ} (hr : 0 < r) : ContDiffBump (0 : ℂ) where
  rIn := r
  rOut := 2 * r
  rIn_pos := hr
  rIn_lt_rOut := by linarith

/-- The Cameron-Martin correction `f_z(x) = -α₀ χ(x) log |x + z|` of Step 8 (Lemma 8.2 route). -/
noncomputable def cmCorrection {r : ℝ} (hr : 0 < r) (α₀ : ℝ) (z : ℂ) : ℂ → ℝ :=
  fun x => -α₀ * (cmCutoff hr x * Real.log ‖x + z‖)

lemma cmCutoff_eq_zero {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : 2 * r ≤ ‖x‖) : cmCutoff hr x = 0 := by
  apply (cmCutoff hr).zero_of_le_dist
  show 2 * r ≤ dist x 0
  rw [dist_zero_right]
  exact hx

lemma cmCutoff_eq_one {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : ‖x‖ ≤ r) : cmCutoff hr x = 1 := by
  apply (cmCutoff hr).one_of_mem_closedBall
  show x ∈ closedBall (0 : ℂ) r
  rw [mem_closedBall_zero_iff]
  exact hx

/-- The Cameron-Martin correction is smooth in `x` for each fixed `z` with `3 r < |z|`
(its only singularity `x = -z` lies outside `B̄_{2r}(0)`, where `χ` vanishes). -/
lemma cmCorrection_contDiff {r : ℝ} (hr : 0 < r) (α₀ : ℝ) {z : ℂ} (hz : 3 * r < ‖z‖) :
    ContDiff ℝ (⊤ : ℕ∞) (cmCorrection hr α₀ z) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x + z = 0
  · -- here `‖x‖ = ‖z‖ > 3 r`, so `χ` vanishes on a neighbourhood of `x`
    have hxn : 2 * r < ‖x‖ := by
      have hxz : x = -z := eq_neg_of_add_eq_zero_left hx
      rw [hxz, norm_neg]
      linarith
    have hev : ∀ᶠ y in 𝓝 x, cmCutoff hr y = 0 := by
      have hnot : x ∉ tsupport (cmCutoff hr) := by
        rw [(cmCutoff hr).tsupport_eq, mem_closedBall, dist_zero_right, not_le]
        exact hxn
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
      exact hy
    have hcst : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : ℂ => (0 : ℝ)) x := contDiffAt_const
    refine hcst.congr_of_eventuallyEq ?_
    filter_upwards [hev] with y hy
    simp [cmCorrection, hy]
  · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => y + z) x := contDiffAt_id.add contDiffAt_const
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => ‖y + z‖) x := ContDiffAt.norm ℝ h1 hx
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => Real.log ‖y + z‖) x :=
      h2.log (norm_ne_zero_iff.mpr hx)
    exact contDiffAt_const.mul ((cmCutoff hr).contDiffAt.mul h3)

/-- The Cameron-Martin correction has compact support (contained in `B̄_{2r}(0)`). -/
lemma cmCorrection_hasCompactSupport {r : ℝ} (hr : 0 < r) (α₀ : ℝ) (z : ℂ) :
    HasCompactSupport (cmCorrection hr α₀ z) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * r))
  intro x hx
  have hx' : 2 * r < ‖x‖ := by
    by_contra h
    apply hx
    rw [mem_closedBall_zero_iff]
    linarith [not_lt.mp h]
  simp [cmCorrection, cmCutoff_eq_zero hr hx'.le]

/-- `f_z` is equal to `-α₀ log |x + z|` on the closed ball `B̄_r(0)`. -/
lemma cmCorrection_eq_log_of_norm_le {r : ℝ} (hr : 0 < r) (α₀ : ℝ) {z x : ℂ} (hx : ‖x‖ ≤ r) :
    cmCorrection hr α₀ z x = -α₀ * Real.log ‖x + z‖ := by
  simp [cmCorrection, cmCutoff_eq_one hr hx]

/-- The circle average of `f_z` over the unit circle vanishes, since `f_z = 0` on `∂B_1(0)` when `2 r < 1`. -/
lemma cmCorrection_circleAverage_zero {r : ℝ} (hr : 0 < r) (hr2 : 2 * r < 1) (α₀ : ℝ) (z : ℂ) :
    Real.circleAverage (cmCorrection hr α₀ z) 0 1 = 0 := by
  have hcongr : Set.EqOn (cmCorrection hr α₀ z) (fun _ : ℂ => (0 : ℝ)) (sphere (0 : ℂ) |(1 : ℝ)|) := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, abs_one] at hx
    simp [cmCorrection, cmCutoff_eq_zero hr (by rw [hx]; linarith)]
  rw [Real.circleAverage_congr_sphere hcongr]
  exact Real.circleAverage_const 0 0 1

/-- Joint measurability of `(z, x) ↦ f_z(x)` (the cutoff `χ` is fixed, so this is measurable in `(z, x)`). -/
lemma measurable_cmCorrection {r : ℝ} (hr : 0 < r) (α₀ : ℝ) :
    Measurable (fun p : ℂ × ℂ => cmCorrection hr α₀ p.1 p.2) := by
  have hχ : Measurable (fun x : ℂ => cmCutoff hr x) := (cmCutoff hr).continuous.measurable
  have hlog : Measurable (fun p : ℂ × ℂ => Real.log ‖p.2 + p.1‖) :=
    Real.measurable_log.comp (continuous_norm.measurable.comp (measurable_snd.add measurable_fst))
  exact measurable_const.mul ((hχ.comp measurable_snd).mul hlog)

/-- Step 8 for the local domain: all properties of `f_z` at `r = r_j`, `z ∈ D_j`. -/
lemma cmCorrection_props_of_mem_localDomain {j : ℕ} (hj : 1 ≤ j) (α₀ : ℝ) {z : ℂ} (hz : z ∈ localDomain j) :
    ContDiff ℝ (⊤ : ℕ∞) (cmCorrection (localRadius_pos hj) α₀ z) ∧
      HasCompactSupport (cmCorrection (localRadius_pos hj) α₀ z) ∧
      Real.circleAverage (cmCorrection (localRadius_pos hj) α₀ z) 0 1 = 0 ∧
      ∀ x : ℂ, ‖x‖ ≤ localRadius j → cmCorrection (localRadius_pos hj) α₀ z x = -α₀ * Real.log ‖x + z‖ := by
  have hz1 : 3 * localRadius j < ‖z‖ := hz.1
  exact ⟨cmCorrection_contDiff _ α₀ hz1, cmCorrection_hasCompactSupport _ α₀ z,
    cmCorrection_circleAverage_zero _ (two_mul_localRadius_lt_one hj) α₀ z,
    fun x hx => cmCorrection_eq_log_of_norm_le _ α₀ hx⟩

/-! ## Step 9: the normalisation removes positive finite constants -/

/-- `massNormalize r (c • η) = massNormalize r η` for a constant `0 < c < ∞`. -/
lemma massNormalize_smul_eq {r : ℝ} (η : Measure ℂ) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) :
    massNormalize r (c • η) = massNormalize r η := by
  unfold massNormalize
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hc), smul_smul]
  congr 1
  rw [mul_right_comm, ENNReal.inv_mul_cancel hc0 hc, one_mul]

end HarmonicBalls
