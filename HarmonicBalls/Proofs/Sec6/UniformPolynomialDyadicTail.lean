import HarmonicBalls.Proofs.Sec6.DyadicFailureTail

/-! # Dyadic tails from uniform polynomial estimates -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter
open scoped ENNReal

universe u

/-- A numerical polynomial bound controls the tail of any family of events,
including families which depend on a physical scale or a lattice phase. -/
theorem dyadic_tail_of_uniform_polynomial_bounds
    {p C r₀ : ℝ} (hp : 0 < p) (hr₀ : 0 < r₀)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ p' : ℝ, 0 < p' ∧ ∃ C' : ℝ, ∃ r₁ > 0,
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (F : ℕ → Set Ω),
      (∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < r₀ →
        P (F n)ᶜ ≤ ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ n) ^ p)) →
      ∀ r : ℝ, 0 < r → r < r₁ →
        P {ω | ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ c * r ^ a → ω ∈ F j}ᶜ ≤
          ENNReal.ofReal (C' * r ^ p') := by
  set q : ℝ := (2 : ℝ)⁻¹ ^ p with hq_def
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  obtain ⟨r₁, hr₁, hsmall⟩ :=
    exists_pos_forall_rpow_le ha (div_pos hr₀ (by positivity : (0 : ℝ) < 2 * c))
  refine ⟨a * p, mul_pos ha hp, max C 0 / (1 - q) * c ^ p, r₁, hr₁, fun Ω _ P F hF r hr hrr => ?_⟩
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
    have hlt : (2 : ℝ)⁻¹ ^ (J + n) < r₀ :=
      ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right J n)).trans hJx).trans_lt hxr₀
    calc P (F (J + n))ᶜ ≤ ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ (J + n)) ^ p) := hF _ hlt
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



/-- A single index controls the probability of every dyadic failure family
with a common polynomial bound. -/
theorem exists_uniform_dyadic_polynomial_tail_bound
    {p₀ C₀ r₀ : ℝ} (hp₀ : 0 < p₀) (hr₀ : 0 < r₀)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (F : ℕ → Set Ω),
      (∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < r₀ →
        P (F n)ᶜ ≤ ENNReal.ofReal (C₀ * ((2 : ℝ)⁻¹ ^ n) ^ p₀)) →
      P {ω | ∀ n : ℕ, N ≤ n → ω ∈ F n}ᶜ ≤ δ := by
  by_cases hδtop : δ = ∞
  · exact ⟨9, le_rfl, fun N hN Ω _ P F hF => by rw [hδtop]; exact le_top⟩
  have hδreal : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  obtain ⟨p, hp, C, r₁, hr₁, htail⟩ :=
    dyadic_tail_of_uniform_polynomial_bounds hp₀ hr₀ (a := 1) (c := 1) one_pos one_pos
  obtain ⟨r₂, hr₂, hrpow⟩ := exists_pos_forall_rpow_le hp
    (div_pos hδreal (by positivity : 0 < max C 0 + 1))
  let r : ℝ := min r₁ r₂ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr₁ : r < r₁ := by dsimp [r]; linarith [min_le_left r₁ r₂, lt_min hr₁ hr₂]
  have hrr₂ : r < r₂ := by dsimp [r]; linarith [min_le_right r₁ r₂, lt_min hr₁ hr₂]
  have hreal : C * r ^ p ≤ δ.toReal := by
    have hrp := hrpow r hr hrr₂
    have hrp0 : 0 ≤ r ^ p := Real.rpow_nonneg hr.le _
    have hC : C ≤ max C 0 + 1 := by linarith [le_max_left C 0]
    have hmul := mul_le_mul_of_nonneg_right hC hrp0
    have hm := mul_le_mul_of_nonneg_left hrp (by positivity : 0 ≤ max C 0 + 1)
    have heq : (max C 0 + 1) * (δ.toReal / (max C 0 + 1)) = δ.toReal := by
      field_simp
    linarith
  have hsmall : ENNReal.ofReal (C * r ^ p) ≤ δ := by
    calc ENNReal.ofReal (C * r ^ p) ≤ ENNReal.ofReal δ.toReal := ENNReal.ofReal_le_ofReal hreal
      _ = δ := ENNReal.ofReal_toReal hδtop
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨max M 9, le_max_right M 9, fun N hN Ω _ P F hF => ?_⟩
  calc P {ω | ∀ n : ℕ, N ≤ n → ω ∈ F n}ᶜ ≤
      P {ω | ∀ j : ℕ, (2 : ℝ)⁻¹ ^ j ≤ 1 * r ^ (1 : ℝ) → ω ∈ F j}ᶜ := by
        apply measure_mono
        intro ω hbad hgood
        apply hbad
        intro n hn
        have hnM : M ≤ n := (le_max_left M 9).trans (hN.trans hn)
        have hpow : (2 : ℝ)⁻¹ ^ n ≤ r :=
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hnM).trans hM.le
        apply hgood n
        simpa only [Real.rpow_one, one_mul] using hpow
    _ ≤ ENNReal.ofReal (C * r ^ p) := htail Ω P F hF r hr hrr₁
    _ ≤ δ := hsmall

end HarmonicBalls.Section6
