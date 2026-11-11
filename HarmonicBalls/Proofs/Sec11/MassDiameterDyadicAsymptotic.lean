import HarmonicBalls.Proofs.Sec11.MassDiameterDyadicCount

/-! # Asymptotic dyadic square estimates -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

/-- Exponents above two beat the growth of a planar dyadic square grid. -/
theorem dyadic_decay_rate_lt_quarter (p : ℝ) (hp : 2 < p) :
    4 * ENNReal.ofReal ((1 / 2 : ℝ) ^ p) < 1 := by
  have h : (1 / 2 : ℝ) ^ p < 1 / 4 := by
    have h' := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hp
    norm_num [Real.rpow_two] at h' ⊢
    exact h'
  have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) _
  have hreal : (4 : ℝ) * (1 / 2 : ℝ) ^ p < 1 := by linarith
  have := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).2 hreal
  simpa [ENNReal.ofReal_mul, hnonneg] using this

/-- The small-box exponent from the square-diameter estimate exceeds the
planar dimension when the comparison exponent is below `ξ (Q - 2)`. -/
theorem square_diameter_exponent_gt_two
    (ξ Q s : ℝ) (hξ : 0 < ξ) (hs : 0 < s)
    (hsupper : s < ξ * (Q - 2)) :
    0 < s ∧ s < ξ * Q ∧ 2 < (ξ * Q - s) ^ 2 / (2 * ξ ^ 2) := by
  have hden : 0 < 2 * ξ ^ 2 := by positivity
  have hlarge : 2 * ξ < ξ * Q - s := by nlinarith
  have hsum : 0 < (ξ * Q - s) + 2 * ξ := by linarith
  have hdiff : 0 < (ξ * Q - s) - 2 * ξ := by linarith
  have hprod := mul_pos hdiff hsum
  refine ⟨hs, ?_, ?_⟩
  · linarith
  · rw [lt_div_iff₀ hden]
    nlinarith


/-- A vanishing exponent error can be absorbed into any smaller fixed
exponent along dyadic scales. -/
theorem dyadic_power_error_eventually_le (p p' : ℝ) (hp : p' < p)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n)) ≤
      (ENNReal.ofReal ((1 / 2 : ℝ) ^ p')) ^ n := by
  have hnear : ∀ᶠ n in atTop, p' - p < e n :=
    (tendsto_order.1 he).1 _ (by linarith)
  filter_upwards [hnear] with n hn
  have hpower : (1 / 2 : ℝ) ^ ((p + e n) * n) ≤
      (1 / 2 : ℝ) ^ (p' * n) := by
    apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
  have hh := ENNReal.ofReal_le_ofReal hpower
  calc
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (p' * n)) := hh
    _ = _ := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_natCast,
        ENNReal.ofReal_pow (by positivity)]


/-- Only sufficiently fine scales need satisfy the per-square geometric
estimate; the finitely many coarser scales do not affect the limit. -/
theorem tendsto_dyadic_square_failure_sum_of_eventually
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Set Ω)
    (C q : ℝ≥0∞) (hC : C ≠ ∞) (hq : 4 * q < 1)
    (hbound : ∀ᶠ n in atTop, ∀ i, P (B n i) ≤ C * q ^ n) :
    Tendsto (fun n => ∑ i : Fin (2 ^ n) × Fin (2 ^ n), P (B n i)) atTop (𝓝 0) := by
  classical
  let B' : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Set Ω :=
    fun n i => if ∀ i, P (B n i) ≤ C * q ^ n then B n i else ∅
  have hb : ∀ n i, P (B' n i) ≤ C * q ^ n := by
    intro n i
    by_cases hn : ∀ i, P (B n i) ≤ C * q ^ n
    · change P (if ∀ i, P (B n i) ≤ C * q ^ n then B n i else ∅) ≤ _
      rw [ite_eq_left hn]
      exact hn i
    · change P (if ∀ i, P (B n i) ≤ C * q ^ n then B n i else ∅) ≤ _
      rw [ite_eq_right hn, measure_empty]
      exact zero_le
  have hlim := tendsto_dyadic_square_failure_sum P B' C q hC hq hb
  apply hlim.congr'
  filter_upwards [hbound] with n hn
  simp [B', hn]

/-- A uniform dyadic power estimate with limiting exponent above two
makes the total square-failure probability tend to zero. -/
theorem tendsto_dyadic_square_failure_sum_of_power_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Set Ω)
    (p : ℝ) (hp : 2 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ i, P (B n i) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    Tendsto (fun n => ∑ i : Fin (2 ^ n) × Fin (2 ^ n), P (B n i)) atTop (𝓝 0) := by
  let p' : ℝ := (2 + p) / 2
  have hp' : 2 < p' := by dsimp [p']; linarith
  have hlt : p' < p := by dsimp [p']; linarith
  apply tendsto_dyadic_square_failure_sum_of_eventually P B 1
    (ENNReal.ofReal ((1 / 2 : ℝ) ^ p')) (by simp)
    (dyadic_decay_rate_lt_quarter p' hp')
  filter_upwards [hbound, dyadic_power_error_eventually_le p p' hlt e he] with n hn he'
  intro i
  simpa only [one_mul] using (hn i).trans he'


/-- A sufficiently fine-scale geometric estimate gives simultaneous control
of all dyadic square observables for a pinned whole-plane GFF. -/
theorem IsWholePlaneGFF.tendsto_dyadic_square_diameters_of_eventually
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ)
    (X : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ≥0∞)
    (a : ℕ → ℝ≥0∞) (d C q : ℝ≥0∞)
    (hCfinite : C ≠ ∞) (hq : 4 * q < 1) (hmargin : ∀ n, a n < d)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | a n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < X n i ω} ≤ C * q ^ n) :
    Tendsto (fun n => P {ω | ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      X n i ω < d}ᶜ) atTop (𝓝 0) := by
  apply h.tendsto_all_tiles_failure_of_pinned_circle_factor ξ
    (fun n => Fin (2 ^ n) × Fin (2 ^ n)) X a d hmargin
  exact tendsto_dyadic_square_failure_sum_of_eventually P _ C q hCfinite hq hbound

/-- The diameter threshold need only dominate the comparison scale eventually. -/
theorem IsWholePlaneGFF.tendsto_dyadic_square_diameters_of_eventual_margin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ)
    (X : ∀ n, Fin (2 ^ n) × Fin (2 ^ n) → Ω → ℝ≥0∞)
    (a : ℕ → ℝ≥0∞) (d C q : ℝ≥0∞)
    (hCfinite : C ≠ ∞) (hq : 4 * q < 1)
    (hmargin : ∀ᶠ n in atTop, a n < d)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | a n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < X n i ω} ≤ C * q ^ n) :
    Tendsto (fun n => P {ω | ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      X n i ω < d}ᶜ) atTop (𝓝 0) := by
  classical
  obtain ⟨n, hn⟩ := hmargin.exists
  have hd : 0 < d := lt_of_le_of_lt (zero_le) hn
  let a' : ℕ → ℝ≥0∞ := fun n => if a n < d then a n else 0
  have hm : ∀ n, a' n < d := by
    intro k
    by_cases hk : a k < d
    · simp [a', hk]
    · simp [a', hk, hd]
  apply h.tendsto_dyadic_square_diameters_of_eventually ξ X a' d C q hCfinite hq hm
  filter_upwards [hmargin, hbound] with k hk hb
  simpa only [a', ite_eq_left hk] using hb

end HarmonicBalls
