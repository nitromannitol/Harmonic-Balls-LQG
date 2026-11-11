import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGKernelBorel

/-! # Route (A), Step M: inner approximations of open subsets of the unit disk by `C_c(B₁)` functions

For an open set `U ⊆ ℂ`, the functions `innerApprox U m = openApprox (U ∩ B₁) m · ballCut m` are continuous, nonnegative,
bounded by one, supported in a closed disk of radius `1 - 1/(m+1) < 1` (so in `C_c(B₁)`), increasing in `m`, and increase
to the indicator of `U ∩ B₁`. They give the monotone approximations used to pass the Palm identity
(`palm_test_identity`, test functions in `C_c(B₁)`) to indicators of open subsets of `B₁`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- Cutoff near the unit circle: zero for `‖z‖ ≥ 1 - 1/(m+1)`, one for `‖z‖ ≤ 1 - 2/(m+1)`. -/
def ballCut (m : ℕ) (z : ℂ) : ℝ :=
  max 0 (min 1 (((m : ℝ) + 1) * (1 - ‖z‖) - 1))

theorem ballCut_nonneg (m : ℕ) (z : ℂ) : 0 ≤ ballCut m z :=
  le_max_left _ _

theorem ballCut_le_one (m : ℕ) (z : ℂ) : ballCut m z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem ballCut_eq_zero_of_le (m : ℕ) {z : ℂ} (h : ((m : ℝ) + 1) * (1 - ‖z‖) ≤ 1) :
    ballCut m z = 0 :=
  max_eq_left ((min_le_right _ _).trans (by linarith))

theorem ballCut_eq_zero_of_one_le (m : ℕ) {z : ℂ} (h : 1 ≤ ‖z‖) : ballCut m z = 0 :=
  ballCut_eq_zero_of_le m (by nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])

theorem ballCut_eq_one (m : ℕ) {z : ℂ} (h : 2 ≤ ((m : ℝ) + 1) * (1 - ‖z‖)) : ballCut m z = 1 := by
  unfold ballCut
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem ballCut_mono (z : ℂ) : Monotone fun m : ℕ => ballCut m z := by
  intro m m' hmm
  by_cases hz : ‖z‖ ≤ 1
  · have hm : (m : ℝ) ≤ (m' : ℝ) := Nat.cast_le.2 hmm
    have h1 : 0 ≤ 1 - ‖z‖ := by linarith
    have h2 : ((m : ℝ) + 1) * (1 - ‖z‖) ≤ ((m' : ℝ) + 1) * (1 - ‖z‖) :=
      mul_le_mul_of_nonneg_right (by linarith) h1
    unfold ballCut
    exact max_le_max le_rfl (min_le_min le_rfl (by linarith))
  · have hz' : 1 ≤ ‖z‖ := le_of_lt (not_le.1 hz)
    show ballCut m z ≤ ballCut m' z
    rw [ballCut_eq_zero_of_one_le m hz', ballCut_eq_zero_of_one_le m' hz']

theorem ballCut_continuous (m : ℕ) : Continuous fun z : ℂ => ballCut m z := by
  unfold ballCut
  exact continuous_const.max (continuous_const.min
    ((continuous_const.mul (continuous_const.sub continuous_norm)).sub continuous_const))

/-- The inner approximation of an open set `U` by cutoff functions in `C_c(B₁)`. -/
def innerApprox (U : Set ℂ) (m : ℕ) (z : ℂ) : ℝ :=
  openApprox (U ∩ ball (0 : ℂ) 1) m z * ballCut m z

theorem innerApprox_nonneg (U : Set ℂ) (m : ℕ) (z : ℂ) : 0 ≤ innerApprox U m z :=
  mul_nonneg (openApprox_nonneg _ _ _) (ballCut_nonneg _ _)

theorem innerApprox_le_one (U : Set ℂ) (m : ℕ) (z : ℂ) : innerApprox U m z ≤ 1 :=
  calc innerApprox U m z ≤ 1 * 1 :=
        mul_le_mul (openApprox_le_one _ _ _) (ballCut_le_one _ _) (ballCut_nonneg _ _) zero_le_one
    _ = 1 := one_mul 1

theorem innerApprox_mono (U : Set ℂ) (z : ℂ) : Monotone fun m : ℕ => innerApprox U m z := by
  intro m m' hmm
  exact mul_le_mul (openApprox_mono _ z hmm) (ballCut_mono z hmm) (ballCut_nonneg _ _)
    (openApprox_nonneg _ _ _)

theorem innerApprox_continuous (U : Set ℂ) (m : ℕ) : Continuous (innerApprox U m) :=
  (openApprox_continuous _ m).mul (ballCut_continuous m)

/-- The support of `innerApprox U m` lies in the closed disk of radius `1 - 1/(m+1)`. -/
theorem innerApprox_hasCompactSupport (U : Set ℂ) (m : ℕ) :
    HasCompactSupport (innerApprox U m) := by
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (1 - 1 / ((m : ℝ) + 1))) fun z hz => ?_
  have hz' : 1 - 1 / ((m : ℝ) + 1) < ‖z‖ := by
    rw [mem_closedBall_zero_iff] at hz
    exact lt_of_not_ge hz
  have h1 : 1 - ‖z‖ < 1 / ((m : ℝ) + 1) := by linarith
  have h2 : ((m : ℝ) + 1) * (1 - ‖z‖) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h1.le hpos.le
    rwa [mul_one_div_cancel hpos.ne'] at this
  unfold innerApprox
  rw [ballCut_eq_zero_of_le m h2, mul_zero]

/-- The inner approximations are supported in the open unit disk. -/
theorem innerApprox_tsupport (U : Set ℂ) (m : ℕ) : tsupport (innerApprox U m) ⊆ ball (0 : ℂ) 1 := by
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have hsub : tsupport (innerApprox U m) ⊆ closedBall (0 : ℂ) (1 - 1 / ((m : ℝ) + 1)) := by
    refine closure_minimal ?_ isClosed_closedBall
    intro z hz
    rw [mem_closedBall_zero_iff]
    by_contra h
    have hlt : 1 - 1 / ((m : ℝ) + 1) < ‖z‖ := lt_of_not_ge h
    have h1 : 1 - ‖z‖ < 1 / ((m : ℝ) + 1) := by linarith
    have hpos' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h2 : ((m : ℝ) + 1) * (1 - ‖z‖) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h1.le hpos'.le
      rwa [mul_one_div_cancel hpos'.ne'] at this
    apply hz
    unfold innerApprox
    rw [ballCut_eq_zero_of_le m h2, mul_zero]
  exact hsub.trans (closedBall_subset_ball (by linarith))

/-- For `V` open with nonempty complement and `z ∈ V`, the cutoff approximation of `V` equals one eventually. -/
theorem openApprox_eq_one_eventually {V : Set ℂ} (hV : IsOpen V) (hVc : Vᶜ.Nonempty) {z : ℂ} (hz : z ∈ V) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → openApprox V m z = 1 := by
  have hcl : IsClosed Vᶜ := hV.isClosed_compl
  have hd : 0 < Metric.infDist z Vᶜ := (IsClosed.notMem_iff_infDist_pos hcl hVc).1 (fun h => h hz)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / Metric.infDist z Vᶜ) (‖z‖ + 1))
  refine ⟨N, fun m hm => ?_⟩
  have hm' : (N : ℝ) ≤ m := Nat.cast_le.2 hm
  have hm1 : 1 / Metric.infDist z Vᶜ < (m : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hN) hm'
  have hm2 : ‖z‖ + 1 < (m : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hm'
  have h3 : 1 < (m : ℝ) * Metric.infDist z Vᶜ := by
    have := mul_lt_mul_of_pos_right hm1 hd
    rwa [one_div_mul_cancel hd.ne'] at this
  unfold openApprox
  rw [min_eq_left h3.le, min_eq_left (show (1 : ℝ) ≤ (m : ℝ) - ‖z‖ by linarith),
    max_eq_right zero_le_one, mul_one]

/-- The inner approximations increase to the indicator of `U ∩ B₁` (for `U` open). -/
theorem innerApprox_iSup {U : Set ℂ} (hU : IsOpen U) (z : ℂ) :
    (U ∩ ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞) z = ⨆ m : ℕ, ENNReal.ofReal (innerApprox U m z) := by
  by_cases hz : z ∈ U ∩ ball (0 : ℂ) 1
  · have hV : IsOpen (U ∩ ball (0 : ℂ) 1) := hU.inter isOpen_ball
    obtain ⟨N₁, hN₁⟩ := openApprox_eq_one_eventually hV (compl_inter_ball_nonempty U) hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz.2
    have hpos : 0 < 1 - ‖z‖ := by linarith
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / (1 - ‖z‖))
    have h2 : ∀ m : ℕ, N₂ ≤ m → 2 ≤ ((m : ℝ) + 1) * (1 - ‖z‖) := by
      intro m hm
      have hm' : (N₂ : ℝ) ≤ m := Nat.cast_le.2 hm
      have h4 : 2 < (N₂ : ℝ) * (1 - ‖z‖) := by
        have := mul_lt_mul_of_pos_right hN₂ hpos
        rwa [div_mul_cancel₀ _ hpos.ne'] at this
      have h5 : (N₂ : ℝ) * (1 - ‖z‖) ≤ (m : ℝ) * (1 - ‖z‖) := mul_le_mul_of_nonneg_right hm' hpos.le
      have h6 : (m : ℝ) * (1 - ‖z‖) ≤ ((m : ℝ) + 1) * (1 - ‖z‖) :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
      linarith
    have hval1 : ∀ m : ℕ, max N₁ N₂ ≤ m → innerApprox U m z = 1 := fun m hm => by
      unfold innerApprox
      rw [hN₁ m (le_trans (le_max_left _ _) hm), ballCut_eq_one m (h2 m (le_trans (le_max_right _ _) hm)),
        mul_one]
    rw [Set.indicator_of_mem hz, Pi.one_apply]
    apply le_antisymm
    · have h1 : ENNReal.ofReal (innerApprox U (max N₁ N₂) z) = 1 := by
        rw [hval1 (max N₁ N₂) le_rfl]
        simp
      calc (1 : ℝ≥0∞) = ENNReal.ofReal (innerApprox U (max N₁ N₂) z) := h1.symm
        _ ≤ ⨆ m : ℕ, ENNReal.ofReal (innerApprox U m z) :=
          le_iSup (fun m : ℕ => ENNReal.ofReal (innerApprox U m z)) (max N₁ N₂)
    · exact iSup_le fun m => ENNReal.ofReal_le_one.2 (innerApprox_le_one U m z)
  · rw [Set.indicator_of_notMem hz]
    have hval : ∀ m : ℕ, innerApprox U m z = 0 := by
      intro m
      unfold innerApprox
      by_cases hzb : z ∈ ball (0 : ℂ) 1
      · have hz0 : Metric.infDist z (U ∩ ball (0 : ℂ) 1)ᶜ = 0 :=
          Metric.infDist_zero_of_mem (show z ∈ (U ∩ ball (0 : ℂ) 1)ᶜ from hz)
        have hO : openApprox (U ∩ ball (0 : ℂ) 1) m z = 0 := by
          unfold openApprox
          rw [hz0]
          simp
        rw [hO, zero_mul]
      · rw [ballCut_eq_zero_of_one_le m (not_lt.1 (fun h => hzb (mem_ball_zero_iff.2 h))), mul_zero]
    simp [hval]

end HarmonicBalls

end
