import HarmonicBalls.FirstPass.S11c.ShiftObs11_7
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Lemma 11.7, Cameron-Martin transfer to the Campbell reference observation (B2 sec 5.2, option A)

* `abs_log_sub_log_le_of_ge`: `|log x - log y| ≤ |x - y| / ε` for `x, y ≥ ε > 0`.
* `log_max_lipschitz`: `w ↦ log max(ε, |w|)` is Lipschitz on the plane.
* `exists_campbellShift_cut`: for a disc `ball c r` with `0 ∉ closedBall c r`, a smooth cut-off `χ` (`ContDiffBump`) with
  `χ = 1` on `ball c r`, supported in a closed ball avoiding `0`, such that `b χ` (`campbellShift · χ`) is locally Lipschitz
  with compact support. On the support of `χ`, `b` equals `log max(ε, |·|)`, so `b χ = χ · H` with `H` locally Lipschitz
  (no smoothness of `b` across `|w| = 1` is needed).
* `campbellRef_absCont_of_CM`: the frozen Cameron-Martin input `CameronMartinLocallyLipschitzShiftAbsCont` (pending truth
  check, option A) turns a null rooted observation event into a null reference observation event: the hypothesis `hAC`
  of `lintegral_localBadSet_campbellRef_eq_zero` (ShiftObs11_7.lean).
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

namespace HarmonicBalls.S11c

/-- Elementary estimate: `|log x - log y| ≤ |x - y| / ε` for `x, y ≥ ε > 0`, from `log t ≤ t - 1`. -/
lemma abs_log_sub_log_le_of_ge {ε x y : ℝ} (hε : 0 < ε) (hx : ε ≤ x) (hy : ε ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / ε := by
  have hx0 : 0 < x := lt_of_lt_of_le hε hx
  have hy0 : 0 < y := lt_of_lt_of_le hε hy
  have hxne : x ≠ 0 := hx0.ne'
  have hyne : y ≠ 0 := hy0.ne'
  have h1 : Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
  have h2 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  have h3 : Real.log (y / x) = -Real.log (x / y) := by
    rw [← Real.log_inv, inv_div]
  have hA : |x / y - 1| ≤ |x - y| / ε := by
    have e : x / y - 1 = (x - y) / y := by field_simp
    rw [e, abs_div, abs_of_pos hy0]
    gcongr
  have hB : |y / x - 1| ≤ |x - y| / ε := by
    have e : y / x - 1 = (y - x) / x := by field_simp
    rw [e, abs_div, abs_of_pos hx0, abs_sub_comm]
    gcongr
  rw [← Real.log_div hxne hyne, abs_le]
  constructor
  · have h4 : -|y / x - 1| ≤ -(y / x - 1) := by linarith [le_abs_self (y / x - 1)]
    linarith [h2, h3, hB, h4]
  · linarith [le_abs_self (x / y - 1), hA, h1]

/-- `w ↦ log max(ε, |w|)` is Lipschitz on `ℂ` with constant `1 / ε`. -/
lemma log_max_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (1 / ε)) (fun w : ℂ => Real.log (max ε ‖w‖)) := by
  refine LipschitzWith.of_dist_le' fun w w' => ?_
  rw [Real.dist_eq, dist_eq_norm, one_div]
  calc |Real.log (max ε ‖w‖) - Real.log (max ε ‖w'‖)|
      ≤ |max ε ‖w‖ - max ε ‖w'‖| / ε :=
        abs_log_sub_log_le_of_ge hε (le_max_left _ _) (le_max_left _ _)
    _ ≤ ‖w - w'‖ / ε := by
        have hm : |max ε ‖w‖ - max ε ‖w'‖| ≤ |‖w‖ - ‖w'‖| := by
          rw [max_comm ε ‖w‖, max_comm ε ‖w'‖]
          exact abs_max_sub_max_le_abs _ _ _
        gcongr
        exact hm.trans (abs_norm_sub_norm_le w w')
    _ = ε⁻¹ * ‖w - w'‖ := by ring

/-- A product of two real-valued locally Lipschitz functions on `ℂ` is locally Lipschitz. (`LocallyLipschitz.mul` is the
group version and does not apply to real multiplication.) Near a point both factors are bounded and Lipschitz. -/
lemma locallyLipschitz_mul_real {f g : ℂ → ℝ} (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun w => f w * g w) := by
  intro x
  obtain ⟨Kf, tf, htf, hKf⟩ := hf x
  obtain ⟨Kg, tg, htg, hKg⟩ := hg x
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem htf htg)
  have hcl : closedBall x (r / 2) ⊆ tf ∩ tg := (closedBall_subset_ball (half_lt_self hr)).trans hsub
  have hclf : closedBall x (r / 2) ⊆ tf := hcl.trans inter_subset_left
  have hclg : closedBall x (r / 2) ⊆ tg := hcl.trans inter_subset_right
  obtain ⟨Cf, hCf⟩ := (isCompact_closedBall x (r / 2)).exists_bound_of_continuousOn
    (hKf.continuousOn.mono hclf)
  obtain ⟨Cg, hCg⟩ := (isCompact_closedBall x (r / 2)).exists_bound_of_continuousOn
    (hKg.continuousOn.mono hclg)
  refine ⟨Real.toNNReal (|Cf| * Kg + |Cg| * Kf), ball x (r / 2), ball_mem_nhds x (half_pos hr), ?_⟩
  refine LipschitzOnWith.of_dist_le' fun y hy z hz => ?_
  have hy' : y ∈ closedBall x (r / 2) := ball_subset_closedBall hy
  have hz' : z ∈ closedBall x (r / 2) := ball_subset_closedBall hz
  have h1 : |f y - f z| ≤ (Kf : ℝ) * dist y z := by
    rw [← Real.dist_eq]
    exact hKf.dist_le_mul y (hclf hy') z (hclf hz')
  have h2 : |g y - g z| ≤ (Kg : ℝ) * dist y z := by
    rw [← Real.dist_eq]
    exact hKg.dist_le_mul y (hclg hy') z (hclg hz')
  have hfy : |f y| ≤ |Cf| := by
    have := hCf y hy'
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hgz : |g z| ≤ |Cg| := by
    have := hCg z hz'
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  rw [Real.dist_eq, show f y * g y - f z * g z = f y * (g y - g z) + g z * (f y - f z) by ring]
  calc |f y * (g y - g z) + g z * (f y - f z)|
      ≤ |f y * (g y - g z)| + |g z * (f y - f z)| := abs_add_le _ _
    _ = |f y| * |g y - g z| + |g z| * |f y - f z| := by rw [abs_mul, abs_mul]
    _ ≤ |Cf| * ((Kg : ℝ) * dist y z) + |Cg| * ((Kf : ℝ) * dist y z) :=
        add_le_add (mul_le_mul hfy h2 (abs_nonneg _) (abs_nonneg _))
          (mul_le_mul hgz h1 (abs_nonneg _) (abs_nonneg _))
    _ = (|Cf| * (Kg : ℝ) + |Cg| * (Kf : ℝ)) * dist y z := by ring

/-- A smooth cut-off: for `0 < r < R`, a `C¹` function equal to `1` on `closedBall c r` with support in `closedBall c R`. -/
lemma exists_cut_ball (c : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ closedBall c R ∧
      ∀ w ∈ closedBall c r, χ w = 1 := by
  let f : ContDiffBump c := ⟨r, R, hr, hrR⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, fun w hw => f.one_of_mem_closedBall hw⟩
  rw [f.tsupport_eq]

/-- The cut-off form of the shift `b` (B2 sec 5.2): for a disc `ball c r` with `0 ∉ closedBall c r` there is `χ` with
`χ = 1` on the disc such that the compactly supported function `b χ` is locally Lipschitz. -/
theorem exists_campbellShift_cut (γ α₀ : ℝ) {c : ℂ} {r : ℝ} (hr : 0 < r) (h0 : (0 : ℂ) ∉ closedBall c r) :
    ∃ χ : ℂ → ℝ, (∀ w ∈ ball c r, χ w = 1) ∧
      HasCompactSupport (fun w => campbellShift γ α₀ w * χ w) ∧
      LocallyLipschitz (fun w => campbellShift γ α₀ w * χ w) := by
  have hrc : r < ‖c‖ := by
    have h : ¬ (dist (0 : ℂ) c ≤ r) := fun h => h0 (Metric.mem_closedBall.mpr h)
    rw [dist_zero_left] at h
    exact not_le.mp h
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (r + ‖c‖) / 2 := ⟨_, rfl⟩
  have hrR : r < R := by rw [hRdef]; linarith
  have hRc : R < ‖c‖ := by rw [hRdef]; linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = ‖c‖ - R := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨χ, hcd, hcs, hsupp, hone⟩ := exists_cut_ball c hr hrR
  have hnorm : ∀ w ∈ tsupport χ, ε ≤ ‖w‖ := by
    intro w hw
    have hw' : dist w c ≤ R := Metric.mem_closedBall.mp (hsupp hw)
    rw [dist_eq_norm] at hw'
    have h1 : ‖c‖ - ‖w‖ ≤ ‖c - w‖ := norm_sub_norm_le c w
    rw [norm_sub_rev] at h1
    linarith
  have hpt : ∀ w, campbellShift γ α₀ w * χ w
      = χ w * (-α₀ * Real.log (max ε ‖w‖) + γ * Real.log (max 1 ‖w‖)) := by
    intro w
    by_cases hw : w ∈ tsupport χ
    · have hmax : max ε ‖w‖ = ‖w‖ := max_eq_right (hnorm w hw)
      unfold campbellShift
      rw [hmax]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hw]
      ring
  have hfun : (fun w => campbellShift γ α₀ w * χ w)
      = fun w => χ w * (-α₀ * Real.log (max ε ‖w‖) + γ * Real.log (max 1 ‖w‖)) := funext hpt
  have hL1 : LocallyLipschitz (fun w : ℂ => Real.log (max ε ‖w‖)) :=
    (log_max_lipschitz hε).locallyLipschitz
  have hL2 : LocallyLipschitz (fun w : ℂ => Real.log (max 1 ‖w‖)) :=
    (log_max_lipschitz one_pos).locallyLipschitz
  have hH : LocallyLipschitz (fun w : ℂ => -α₀ * Real.log (max ε ‖w‖) + γ * Real.log (max 1 ‖w‖)) :=
    (locallyLipschitz_mul_real (show ContDiff ℝ 1 (fun _ : ℂ => -α₀) from contDiff_const).locallyLipschitz hL1).add
      (locallyLipschitz_mul_real (show ContDiff ℝ 1 (fun _ : ℂ => γ) from contDiff_const).locallyLipschitz hL2)
  have hχLL : LocallyLipschitz χ := hcd.locallyLipschitz
  refine ⟨χ, fun w hw => hone w (ball_subset_closedBall hw), ?_, ?_⟩
  · rw [hfun]
    exact hcs.mul_right
  · rw [hfun]
    exact locallyLipschitz_mul_real hχLL hH

/-- Cameron-Martin transfer (B2 sec 5.2, option A): under the frozen Cameron-Martin input for locally Lipschitz compactly
supported shifts, a null rooted observation event (`P {O₀ ∈ S} = 0`, the insertion-zero rooted observation at `z`) gives a
null reference observation event (`P {O_b ∈ S} = 0`, the Campbell reference observation with the shift `b χ`). This is the
hypothesis `hAC` of `lintegral_localBadSet_campbellRef_eq_zero` (ShiftObs11_7.lean). -/
theorem campbellRef_absCont_of_CM (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α₀ : ℝ} {D : Set ℂ} {z : ℂ} (χ : ℂ → ℝ) (hχ : ∀ w ∈ D, χ w = 1)
    (hLL : LocallyLipschitz (fun w => campbellShift γ α₀ w * χ w))
    (hcs : HasCompactSupport (fun w => campbellShift γ α₀ w * χ w))
    (S : Set ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ)) (hS : MeasurableSet S)
    (h : P {ω | rootedMeanZeroObs 0 γ D z (hC ω) ∈ S} = 0) :
    P {ω | (campbellReferenceObs γ α₀ D (hC ω) z).2 ∈ S} = 0 := by
  let T : ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ) →
      ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ) :=
    fun x φ => x φ - γ * ∫ w, Real.log ‖w - z‖ * φ.1 w
  have hT : Measurable T :=
    Measurable.of_eval fun φ => (measurable_pi_apply φ).sub_const _
  have hint : ∀ φ : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0},
      ∫ w, campbellShift γ α₀ w * χ w * φ.1 w = ∫ x, φ.1 x * (campbellShift γ α₀ x * χ x) := by
    intro φ
    congr 1
    funext w
    ring
  have hrootEq : ∀ ω, rootedMeanZeroObs 0 γ D z (hC ω) = T (fun φ => hC ω φ.1) := by
    intro ω
    funext φ
    simp only [rootedMeanZeroObs, fieldPairing, T, zero_mul, sub_zero]
  have hobsEq : ∀ ω, (campbellReferenceObs γ α₀ D (hC ω) z).2 =
      T (fun φ => hC ω φ.1 + ∫ x, φ.1 x * (campbellShift γ α₀ x * χ x)) := by
    intro ω
    funext φ
    rw [campbellReferenceObs_snd_apply_of_cut γ α₀ (hC ω) z χ hχ φ, hint φ]
    simp only [rootedMeanZeroObs, fieldPairing, T, zero_mul, sub_zero]
    ring
  have e1 : {ω | rootedMeanZeroObs 0 γ D z (hC ω) ∈ S} = {ω | (fun φ => hC ω φ.1) ∈ T ⁻¹' S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hrootEq]
  have e2 : {ω | (campbellReferenceObs γ α₀ D (hC ω) z).2 ∈ S} =
      {ω | (fun φ => hC ω φ.1 + ∫ x, φ.1 x * (campbellShift γ α₀ x * χ x)) ∈ T ⁻¹' S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hobsEq]
  have hCM' := hCM Ω P hC hcirc D (fun w => campbellShift γ α₀ w * χ w) hh hLL hcs (T ⁻¹' S)
    (hS.preimage hT) (by rw [← e1]; exact h)
  rw [e2]
  exact hCM'

end HarmonicBalls.S11c
