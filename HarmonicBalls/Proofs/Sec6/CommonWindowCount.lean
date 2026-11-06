import HarmonicBalls.Proofs.Sec6.CommonScaledCriterionCount

/-! # Comparing common-radius counts across windows

The underlying annulus count uses Leonardo Bonanno's iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

/-- A fixed enlargement of a small parameter has its entire three-quarter
power window inside the square-root window of the original parameter. -/
theorem eventually_mul_window_inside_sqrt {C : ℝ} (hC : 1 ≤ C) :
    ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      ε ≤ C * ε ∧ C * ε ≤ Real.sqrt ε ∧
        (C * ε) ^ (3 / 4 : ℝ) ≤ Real.sqrt ε := by
  have hCpos : 0 < C := by linarith
  have hpow : 0 < C ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hCpos _
  obtain ⟨η, hη, hsmall⟩ := exists_pos_forall_rpow_le
    (a := (1 / 4 : ℝ)) (c := (C ^ (3 / 4 : ℝ))⁻¹) (by norm_num) (inv_pos.mpr hpow)
  refine ⟨min η (1 / C), lt_min hη (by positivity), ?_⟩
  intro ε hε hεη
  have hsmall' := hsmall ε hε (hεη.trans_le (min_le_left _ _))
  have hCe : C * ε ≤ 1 := by
    have := hεη.trans_le (min_le_right _ _)
    have h := (lt_div_iff₀ hCpos).mp this
    nlinarith
  have hu : (C * ε) ^ (3 / 4 : ℝ) ≤ Real.sqrt ε := by
    rw [Real.mul_rpow hCpos.le hε.le, Real.sqrt_eq_rpow]
    have heq : ε ^ (3 / 4 : ℝ) = ε ^ (1 / 2 : ℝ) * ε ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hε]
      congr 1; norm_num
    rw [heq]
    have hprod : C ^ (3 / 4 : ℝ) * ε ^ (1 / 4 : ℝ) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hsmall' hpow.le
      simpa only [mul_inv_cancel₀ hpow.ne'] using h
    have hsqrt : 0 ≤ ε ^ (1 / 2 : ℝ) := Real.rpow_nonneg hε.le _
    nlinarith
  refine ⟨?_, ?_, hu⟩
  · nlinarith
  · calc
      C * ε = (C * ε) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (C * ε) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (mul_pos hCpos hε) hCe (by norm_num)
      _ ≤ Real.sqrt ε := hu

/-- A common seven-adic count on a smaller window transfers to the wider
criterion-three window, provided the smaller lower endpoint is at most
`sqrt ε`. The same radii and both centres are preserved. -/
theorem common_count_wider_window
    {μ : Measure ℂ} {a₁ a₂ b₁ b₂ c s ε t : ℝ} {z w : ℂ}
    (hc : 0 ≤ c) (hε : 0 < ε) (ht : 0 < t)
    (hlo : ε ≤ t) (htsqrt : t ≤ Real.sqrt ε)
    (hupper : t ^ (3 / 4 : ℝ) ≤ Real.sqrt ε)
    (hcount : c * Real.logb 7 (t ^ (-1 : ℝ)) ≤
      ({r : ℝ | r ∈ Icc t (t ^ (3 / 4 : ℝ)) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ (s*r) z a₁ b₁ ∧ IsGoodAnnulus μ (s*r) w a₂ b₂}.ncard : ℝ)) :
    c * Real.logb 7 (ε ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc ε (Real.sqrt ε) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ (s*r) z a₁ b₁ ∧ IsGoodAnnulus μ (s*r) w a₂ b₂}.ncard : ℝ) := by
  have hsqrt : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hlog : Real.logb 7 (ε ^ (-(1 / 2 : ℝ))) ≤ Real.logb 7 (t ^ (-1 : ℝ)) := by
    rw [Real.rpow_neg hε.le, Real.rpow_neg ht.le, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    exact Real.logb_le_logb_of_le (by norm_num) (inv_pos.mpr hsqrt)
      (inv_le_inv₀ hsqrt ht |>.2 htsqrt)
  have hfin : {r : ℝ | r ∈ Icc ε (Real.sqrt ε) ∧
      (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus μ (s*r) z a₁ b₁ ∧ IsGoodAnnulus μ (s*r) w a₂ b₂}.Finite := by
    refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := ε)
      (by norm_num) (by norm_num) hε ?_
    intro r hr
    obtain ⟨k, hk⟩ := hr.2.1
    exact ⟨hr.1.1, k, by simpa only [one_mul] using hk⟩
  have hcard := Set.ncard_le_ncard (s := {r : ℝ | r ∈ Icc t (t ^ (3 / 4 : ℝ)) ∧
      (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus μ (s*r) z a₁ b₁ ∧ IsGoodAnnulus μ (s*r) w a₂ b₂})
    (t := {r : ℝ | r ∈ Icc ε (Real.sqrt ε) ∧
      (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus μ (s*r) z a₁ b₁ ∧ IsGoodAnnulus μ (s*r) w a₂ b₂})
    (fun r hr => ⟨⟨hlo.trans hr.1.1, hr.1.2.trans hupper⟩, hr.2⟩) hfin
  exact (mul_le_mul_of_nonneg_left hlog hc).trans (hcount.trans (by exact_mod_cast hcard))

end HarmonicBalls.Section6
