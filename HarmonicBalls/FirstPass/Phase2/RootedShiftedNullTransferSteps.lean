import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec8.CircleLogPotential
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmDMSConstant
import HarmonicBalls.FirstPass.S8c.LocalObservation
import HarmonicBalls.Proofs.Sec8.LocalSmoothShiftCutoff

/-! # Shifted-root null transfer: the local steps L1, L2 and L5 (MQ-lh-29)

Steps of the corrected null-transfer statement `RootedShiftedDecoderNullTransfer`
(`FirstPass/Phase2/RootedDominationJoint.lean`), following `notes/fp-gaps/MATH-ANSWERS.md`, section MQ-lh-29:

* L1: almost surely the DMS constant vanishes, so the DMS-shifted circle profile is the field plus the
  shift `Av_{∂B_s(x)} dmsShift`; the unit-circle average of `dmsShift γ z` is zero (Duplantier-Miller-Sheffield,
  arXiv:1409.7055, Lemma A.10; `dmsConstant_ae_zero`).
* L2: on a small sphere inside the unit disc the normalisation `γ log max(|w|,1)` vanishes, so the circle
  average of `dmsShift γ z` is `-γ log max(ρ, |c - z|)` (Jensen's formula for `log|w - z|`, which is
  `circleAverage_log_norm_sub_eq_log_max`), and the α₀-field of the shifted profile is an explicit local
  expression (Lemma 8.2 of Bou-Rabee and Gwynne, proof, printed `h̃|_{B_r}` decomposition).
* L5: mass normalisation `N_r(η) = η(B_{r/2}(0))⁻¹ • η` removes a constant factor `c ∈ (0, ∞)`.

Terminology: Duplantier-Sheffield (LQG measures from the GFF), Armitage-Gardiner (circle averages).
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- **L1.** Almost surely the DMS constant `dmsConstant γ z (h₁(0))` vanishes for `|z| ≤ 1`, so the DMS-shifted
circle profile `hc r x + Av_{∂B_r(x)} dmsShift γ z + κ` equals the field plus the shift. -/
theorem ae_dmsShiftedCircle_eq_field {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (γ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ∀ᵐ ω ∂P, (fun s x => hcirc ω s x + Real.circleAverage (dmsShift γ z) x s
        + dmsConstant γ z (hcirc ω 1 0)) =
      fun s x => hcirc ω s x + Real.circleAverage (dmsShift γ z) x s := by
  filter_upwards [dmsConstant_ae_zero hG γ hz] with ω hω
  funext s x
  simp [hω]

/-- **L2 (sphere average of the DMS shift).** On a sphere `∂B_ρ(c)` contained in the closed unit disc, the
normalisation `γ log max(|w|,1)` of `dmsShift γ z` vanishes, and the circle average is
`-γ log max(ρ, |c - z|)`. -/
theorem circleAverage_dmsShift_of_sphere_le_one {γ : ℝ} {z c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ‖c‖ + ρ ≤ 1) :
    Real.circleAverage (dmsShift γ z) c ρ = -γ * Real.log (max ρ ‖c - z‖) := by
  have hs : Set.EqOn (dmsShift γ z) (fun w => (-γ) • Real.log ‖w - z‖) (sphere c |ρ|) := by
    intro w hw
    rw [mem_sphere, dist_eq_norm, abs_of_pos hρ] at hw
    have hn : ‖w‖ ≤ 1 := by
      calc ‖w‖ = ‖c + (w - c)‖ := by simp
        _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
        _ ≤ 1 := by rw [hw]; linarith
    simp only [dmsShift, max_eq_right hn, Real.log_one, mul_zero, add_zero, smul_eq_mul]
  rw [Real.circleAverage_congr_sphere hs, Real.circleAverage_fun_smul,
    circleAverage_log_norm_sub_eq_log_max hρ c z, smul_eq_mul]

/-- **L2 (local form of the shifted α₀-field).** For a sphere `∂B_ρ(c)` in the unit disc, with `ρ ≤ |c|`, the
α₀-field circle average of the DMS-shifted profile is `p ρ c - γ log max(ρ, |c - z|) - α₀ log |c|`. -/
theorem fieldCircleAverage_dmsShift_add {α₀ γ : ℝ} {z c : ℂ} (p : ℝ → ℂ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcρ : ρ ≤ ‖c‖) (hc : ‖c‖ + ρ ≤ 1) :
    fieldCircleAverage α₀ (fun s x => p s x + Real.circleAverage (dmsShift γ z) x s) ρ c =
      p ρ c - γ * Real.log (max ρ ‖c - z‖) - α₀ * Real.log ‖c‖ := by
  have hA := circleAverage_dmsShift_of_sphere_le_one (γ := γ) (z := z) hρ hc
  have hB : Real.circleAverage (fun x : ℂ => Real.log ‖x‖) c ρ = Real.log ‖c‖ := by
    have h := circleAverage_log_norm_sub_eq_log_max hρ c 0
    simp only [sub_zero] at h
    rw [h, max_eq_right hcρ]
  simp only [fieldCircleAverage]
  rw [hA, hB]
  ring

/-- **L5 (mass normalisation removes constants).** For a constant `c ∈ (0, ∞)`, `N_r(c • η) = N_r(η)`. -/
theorem massNormalize_smul_const {r : ℝ} {c : ℝ≥0∞} (η : Measure ℂ) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    massNormalize r (c • η) = massNormalize r η := by
  unfold massNormalize
  refine Measure.ext fun s _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  calc c⁻¹ * (η (ball 0 (r / 2)))⁻¹ * (c * η s)
      = (η (ball 0 (r / 2)))⁻¹ * (c⁻¹ * c) * η s := by ring
    _ = (η (ball 0 (r / 2)))⁻¹ * η s := by rw [ENNReal.inv_mul_cancel hc0 hct, mul_one]

/-- **L3 (smooth Cameron-Martin shift).** For `3r < |z|`, the function `y ↦ -a₀ log|y + z|` is smooth on
`B_{2r}(0)` (it avoids `-z`), so the cutoff lemma `exists_testFunction_eqOn_closedBall_of_contDiffOn_ball`
gives a test function supported in `B_{2r}(0)` that equals it on `B_{3r/2}(0)`. -/
theorem exists_testFunction_logShift {a0 r : ℝ} {z : ℂ} (hr : 0 < r) (hz : 3 * r < ‖z‖) :
    ∃ gt : ℂ → ℝ, IsTestFunction (ball (0 : ℂ) (2 * r)) gt ∧
      EqOn gt (fun y => -a0 * Real.log ‖y + z‖) (closedBall (0 : ℂ) (3 * r / 2)) := by
  have hne : ∀ y ∈ ball (0 : ℂ) (2 * r), y + z ≠ 0 := by
    intro y hy h
    rw [mem_ball_zero_iff] at hy
    have h3 : ‖z‖ ≤ ‖y + z‖ + ‖y‖ := by
      calc ‖z‖ = ‖(y + z) - y‖ := by simp
        _ ≤ ‖y + z‖ + ‖y‖ := norm_sub_le _ _
    rw [h, norm_zero] at h3
    linarith
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℂ => -a0 * Real.log ‖y + z‖) (ball (0 : ℂ) (2 * r)) := by
    intro y hy
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => ‖w + z‖) y :=
      (contDiffAt_norm ℝ (n := (⊤ : ℕ∞)) (hne y hy)).comp y (contDiffAt_id.add contDiffAt_const)
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => Real.log ‖w + z‖) y :=
      h1.log (norm_ne_zero_iff.2 (hne y hy))
    exact (contDiffAt_const.mul h2).contDiffWithinAt
  obtain ⟨f, hf, hfg⟩ := exists_testFunction_eqOn_closedBall_of_contDiffOn_ball (c := 0)
    (r := 3 * r / 2) (R := 2 * r) (by linarith) (by linarith) hg
  exact ⟨f, hf, hfg⟩

/-- The test shift of L3 has zero unit-circle average: its support lies in `B_{2r}(0)` with `2r ≤ 1`. -/
theorem circleAverage_testShift_unit {r : ℝ} {gt : ℂ → ℝ}
    (hgt : IsTestFunction (ball (0 : ℂ) (2 * r)) gt) (h2r : 2 * r ≤ 1) :
    Real.circleAverage gt 0 1 = 0 := by
  have h0 : Set.EqOn gt (fun _ => (0 : ℝ)) (sphere (0 : ℂ) |1|) := by
    intro w hw
    rw [mem_sphere, dist_zero_right, abs_one] at hw
    by_contra h
    have hmem : w ∈ tsupport gt := subset_tsupport gt (Function.mem_support.2 h)
    have hball := hgt.2.2 hmem
    rw [mem_ball_zero_iff, hw] at hball
    linarith
  rw [Real.circleAverage_congr_sphere h0, Real.circleAverage_const]

/-- The test shift of L3 is the logarithm on small spheres: for `|y| < 5r/4` and `0 < e < r/4`, its circle
average is `-a₀ log|y + z|`, because the sphere `∂B_e(y)` lies in `B_{3r/2}(0)` and `e < |y + z|`. -/
theorem circleAverage_testShift_eq {a0 r : ℝ} {z : ℂ} {gt : ℂ → ℝ} (hz : 3 * r < ‖z‖)
    (hEq : EqOn gt (fun y => -a0 * Real.log ‖y + z‖) (closedBall (0 : ℂ) (3 * r / 2)))
    {y : ℂ} {e : ℝ} (hy : ‖y‖ < 5 * r / 4) (he : 0 < e) (he' : e < r / 4) :
    Real.circleAverage gt y e = -a0 * Real.log ‖y + z‖ := by
  have hs : Set.EqOn gt (fun w => (-a0) • Real.log ‖w - -z‖) (sphere y |e|) := by
    intro w hw
    rw [mem_sphere, dist_eq_norm, abs_of_pos he] at hw
    have hw' : w ∈ closedBall (0 : ℂ) (3 * r / 2) := by
      rw [mem_closedBall_zero_iff]
      calc ‖w‖ = ‖y + (w - y)‖ := by simp
        _ ≤ ‖y‖ + ‖w - y‖ := norm_add_le _ _
        _ ≤ 3 * r / 2 := by rw [hw]; linarith
    rw [hEq hw']
    simp [smul_eq_mul, sub_neg_eq_add]
  have h3 : ‖z‖ ≤ ‖y + z‖ + ‖y‖ := by
    calc ‖z‖ = ‖(y + z) - y‖ := by simp
      _ ≤ ‖y + z‖ + ‖y‖ := norm_sub_le _ _
  have hle : e ≤ ‖y + z‖ := by linarith
  rw [Real.circleAverage_congr_sphere hs, Real.circleAverage_fun_smul,
    circleAverage_log_norm_sub_eq_log_max he y (-z), smul_eq_mul, sub_neg_eq_add, max_eq_right hle]

end HarmonicBalls
