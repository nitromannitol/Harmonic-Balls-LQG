import LatticeProb.Gauss.CircleAverageModulusUniform

/-! # Simultaneous circle-average box modulus

The box-event estimate follows the summability argument of
`LatticeProb.Gauss.IsWholePlaneGFF.ae_eventually_abs_circle_sub_le`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open LatticeProb.LQG (dyadicScale)
open LatticeProb.Gauss

namespace HarmonicBalls

/-- The full rescaled spatial-radius box modulus holds eventually on one event. -/
theorem ae_eventually_not_circleBadEvent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {a : ℝ} (ha : 0 < a) (R₀ : ℝ) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ω ∉ circleBadEvent hcirc ((2⁻¹ : ℝ) ^ (1 / 4 : ℝ)) (dyadicScale k)
        ⌈max R₀ 0 * 2 ^ k⌉₊ (max ⌊a * k⌋₊ 1) := by
  have := hh.isProbabilityMeasure
  set b : ℝ := 2⁻¹ with hbdef
  have hb0 : 0 < b := by norm_num [hbdef]
  have hb1 : b < 1 := by norm_num [hbdef]
  set p : ℝ := 12 + 12 / a with hpdef
  have hp : 0 < p := by positivity
  set c : ℝ := b ^ (1 / 4 : ℝ) with hcdef
  have hc0 : 0 < c := Real.rpow_pos_of_pos hb0 _
  have hc1 : c < 1 := Real.rpow_lt_one hb0.le hb1 (by norm_num)
  set θ : ℝ := (2 : ℝ) ^ ((3 : ℝ) - p / 2) / c ^ p with hθdef
  have hθb : θ = b ^ (3 / a) := by
    rw [hθdef, hcdef, ← Real.rpow_mul hb0.le, hbdef, Real.inv_rpow (by norm_num),
      Real.inv_rpow (by norm_num), div_inv_eq_mul, ← Real.rpow_add (by norm_num),
      ← Real.rpow_neg (by norm_num)]
    congr 1
    rw [hpdef]
    ring
  have hθ0 : 0 < θ := by rw [hθb]; exact Real.rpow_pos_of_pos hb0 _
  have hθ1 : θ < 1 := by rw [hθb]; exact Real.rpow_lt_one hb0.le hb1 (by positivity)
  set K : ℝ := (∫ t, |t| ^ p ∂(gaussianReal 0 1)) * 12 ^ (p / 2) * 3 * 3 ^ 3 *
    (∑' j : ℕ, ((j : ℝ) + 1) ^ 3 * θ ^ j) with hKdef
  have hK : 0 ≤ K := by
    have h1 : 0 ≤ ∫ t, |t| ^ p ∂(gaussianReal 0 1) := integral_nonneg fun t => by positivity
    have h2 : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 1) ^ 3 * θ ^ j := tsum_nonneg fun j => by positivity
    positivity
  have hB : ∀ n : ℕ, circleModulusBound p c n = K * ((n : ℝ) + 1) ^ 3 * θ ^ n := fun n => rfl
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  set L : ℕ → ℕ := fun k => ⌈R * 2 ^ k⌉₊ with hLdef
  set M : ℕ → ℕ := fun k => max ⌊a * k⌋₊ 1 with hMdef
  have hMge : ∀ k : ℕ, a * k - 1 ≤ (M k : ℝ) := by
    intro k
    have h1 := (Nat.lt_floor_add_one (a * k)).le
    have h2 : (⌊a * (k : ℝ)⌋₊ : ℝ) ≤ (M k : ℝ) := by exact_mod_cast le_max_left _ _
    linarith
  set E : ℕ → Set Ω := fun k => circleBadEvent hcirc c (dyadicScale k) (L k) (M k) with hEdef
  have hεpos : ∀ k : ℕ, 0 < dyadicScale k := fun k => by simp only [dyadicScale]; positivity
  have hE : ∀ k, P (E k) ≤ ENNReal.ofReal ((2 * (L k : ℝ) + 1) ^ 2 * circleModulusBound p c (M k)) :=
    fun k => hh.measure_circleBadEvent_le (hεpos k) hp hc0 hc1 hθ1 (L k) (le_max_right _ _)
  set C : ℝ := (2 * R + 3) ^ 2 * K * (a + 2) ^ 3 * b ^ (-(3 / a)) with hCdef
  have hC : 0 ≤ C := by
    have : 0 < b ^ (-(3 / a)) := Real.rpow_pos_of_pos hb0 _
    positivity
  have hterm : ∀ k : ℕ, (2 * (L k : ℝ) + 1) ^ 2 * circleModulusBound p c (M k)
      ≤ C * ((k : ℝ) + 1) ^ 3 * (1 / 2) ^ k := by
    intro k
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hL : 2 * (L k : ℝ) + 1 ≤ (2 * R + 3) * 2 ^ k := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ R * 2 ^ k by positivity)
      have : (L k : ℝ) = (⌈R * 2 ^ k⌉₊ : ℝ) := rfl
      nlinarith
    have h4 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hL2 : (2 * (L k : ℝ) + 1) ^ 2 ≤ (2 * R + 3) ^ 2 * 4 ^ k := by
      rw [← h4, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hL 2
    have hM1 : (M k : ℝ) + 1 ≤ (a + 2) * ((k : ℝ) + 1) := by
      have h1 : (M k : ℝ) ≤ a * k + 1 := by
        rcases le_total ⌊a * (k : ℝ)⌋₊ 1 with h | h
        · have : M k = 1 := max_eq_right h
          rw [this]
          push_cast
          nlinarith [ha.le, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
        · have : M k = ⌊a * (k : ℝ)⌋₊ := max_eq_left h
          rw [this]
          have := Nat.floor_le (show 0 ≤ a * (k : ℝ) by positivity)
          linarith
      nlinarith [ha.le, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hM3 : ((M k : ℝ) + 1) ^ 3 ≤ (a + 2) ^ 3 * ((k : ℝ) + 1) ^ 3 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hM1 3
    have hθM : θ ^ M k ≤ b ^ (-(3 / a)) * (1 / 8) ^ k := by
      rw [hθb, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
      calc b ^ (3 / a * (M k : ℝ)) ≤ b ^ (3 / a * (a * k - 1)) :=
            Real.rpow_le_rpow_of_exponent_ge hb0 hb1.le
              (mul_le_mul_of_nonneg_left (hMge k) (by positivity))
        _ = b ^ (-(3 / a)) * (1 / 8) ^ k := by
            rw [show 3 / a * (a * k - 1) = -(3 / a) + 3 * (k : ℝ) by field_simp; ring,
              Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le]
            congr 2
            rw [hbdef]
            norm_num
    rw [hB]
    calc (2 * (L k : ℝ) + 1) ^ 2 * (K * ((M k : ℝ) + 1) ^ 3 * θ ^ M k)
        ≤ ((2 * R + 3) ^ 2 * 4 ^ k) *
            (K * ((a + 2) ^ 3 * ((k : ℝ) + 1) ^ 3) * (b ^ (-(3 / a)) * (1 / 8) ^ k)) := by
          apply mul_le_mul hL2 _ (mul_nonneg (mul_nonneg hK (by positivity)) (by positivity))
            (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hM3 hK) hθM (by positivity)
            (mul_nonneg hK (by positivity))
      _ = C * ((k : ℝ) + 1) ^ 3 * (4 * (1 / 8)) ^ k := by
          rw [hCdef, mul_pow]
          ring
      _ = C * ((k : ℝ) + 1) ^ 3 * (1 / 2) ^ k := by norm_num
  have hsum : Summable (fun k : ℕ => C * ((k : ℝ) + 1) ^ 3 * (1 / 2) ^ k) :=
    LatticeProb.summable_polynomial_geometric 3 (by norm_num) (by norm_num)
  have htsum : ∑' k, P (E k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (ENNReal.ofReal_ne_top (r := ∑' k : ℕ, C * ((k : ℝ) + 1) ^ 3 * (1 / 2) ^ k)) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsum]
    exact ENNReal.tsum_le_tsum fun k => (hE k).trans (ENNReal.ofReal_le_ofReal (hterm k))
  simpa only [E, L, M, R, c, b] using ae_eventually_notMem htsum

end HarmonicBalls
