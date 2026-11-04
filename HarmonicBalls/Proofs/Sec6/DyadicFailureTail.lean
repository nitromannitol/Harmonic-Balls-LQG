import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-! # Uniform dyadic tails for dominated failure events -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter
open scoped ENNReal

/-- A polynomial failure bound controls the dyadic tail uniformly over all
families whose individual failure probabilities are dominated by that bound.
The events may vary arbitrarily with the dyadic scale. -/
theorem dyadic_tail_of_failure_probability_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {E : ℝ → Set Ω}
    (h : PolyHighProb P E) {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, ∃ r₀ > 0,
      ∀ F : ℕ → Set Ω, (∀ n : ℕ, P (F n)ᶜ ≤ P (E ((2 : ℝ)⁻¹ ^ n))ᶜ) →
      ∀ r : ℝ, 0 < r → r < r₀ →
        P {ω | ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ c * r ^ a → ω ∈ F j}ᶜ ≤
          ENNReal.ofReal (C * r ^ p) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  set q : ℝ := (2 : ℝ)⁻¹ ^ p with hq_def
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  obtain ⟨r₁, hr₁, hsmall⟩ :=
    exists_pos_forall_rpow_le ha (div_pos hr₀ (by positivity : (0 : ℝ) < 2 * c))
  refine ⟨a * p, mul_pos ha hp, max C 0 / (1 - q) * c ^ p, r₁, hr₁, fun F hF r hr hrr => ?_⟩
  set x : ℝ := c * r ^ a with hx_def
  have hx0 : 0 < x := mul_pos hc (Real.rpow_pos_of_pos hr _)
  have hxr₀ : x < r₀ := by
    have := hsmall r hr hrr
    calc x ≤ c * (r₀ / (2 * c)) := mul_le_mul_of_nonneg_left this hc.le
      _ = r₀ / 2 := by field_simp
      _ < r₀ := by linarith
  have hex : ∃ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx0 (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact ⟨n, hn.le⟩
  classical
  set J := Nat.find hex with hJ
  have hJx : (2 : ℝ)⁻¹ ^ J ≤ x := Nat.find_spec hex
  have hsub : {ω | ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ c * r ^ a → ω ∈ F j}ᶜ ⊆
      ⋃ n : ℕ, (F (J + n))ᶜ := by
    intro ω hω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall] at hω
    obtain ⟨j, hj, hjE⟩ := hω
    have hJj : J ≤ j := Nat.find_min' hex hj
    exact mem_iUnion.2 ⟨j - J, by rwa [Nat.add_sub_cancel' hJj]⟩
  have hterm : ∀ n : ℕ, P (F (J + n))ᶜ ≤
      ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ J) ^ p) * ENNReal.ofReal q ^ n := by
    intro n
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (J + n) := by positivity
    have hlt : (2 : ℝ)⁻¹ ^ (J + n) < r₀ :=
      ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right J n)).trans hJx).trans_lt hxr₀
    calc P (F (J + n))ᶜ ≤ ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ (J + n)) ^ p) := (hF _).trans (hE _ hpos hlt)
      _ ≤ ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ (J + n)) ^ p) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      _ = _ := by
          rw [← ENNReal.ofReal_pow hq0, ← ENNReal.ofReal_mul (by positivity), pow_add,
            Real.mul_rpow (by positivity) (by positivity), hq_def, Real.rpow_pow_comm (by norm_num)]
          ring_nf
  calc P {ω | ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ c * r ^ a → ω ∈ F j}ᶜ
      ≤ ∑' n : ℕ, P (F (J + n))ᶜ := (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ J) ^ p) * ENNReal.ofReal q ^ n :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ J) ^ p) * (1 - ENNReal.ofReal q)⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ J) ^ p / (1 - q)) := by
        rw [div_eq_mul_inv, ENNReal.ofReal_mul' (q := (1 - q)⁻¹) (inv_nonneg.2 (by linarith)),
          ENNReal.ofReal_inv_of_pos (by linarith), ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (max C 0 / (1 - q) * c ^ p * r ^ (a * p)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hxp : ((2 : ℝ)⁻¹ ^ J) ^ p ≤ x ^ p := Real.rpow_le_rpow (by positivity) hJx hp.le
        have hxp' : x ^ p = c ^ p * r ^ (a * p) := by
          rw [hx_def, Real.mul_rpow hc.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le]
        have h1q : 0 < 1 - q := by linarith
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_assoc, ← hxp']
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxp (le_max_right _ _)) h1q.le

end HarmonicBalls.Section6
