import HarmonicBalls.Proofs.Sec6.GeometricCounts

/-! # Geometric scales in a logarithmic window -/

namespace HarmonicBalls.Section6

open Set

/-- A positive fraction of a long interval of real exponents contains a
spaced sequence of natural-number exponents. -/
theorem exists_spaced_exponents_in_three_quarter_window
    (t : ℝ) (stride : ℕ) (hstride : 0 < stride)
    (ht : 16 * (stride : ℝ) ≤ t) :
    ∃ n₀ K : ℕ, t / (16 * stride) ≤ (K : ℝ) ∧
      ∀ k ∈ Finset.range K, 3 * t / 4 ≤ (n₀ + stride * k : ℕ) ∧
        (n₀ + stride * k : ℕ) ≤ t := by
  let S : ℝ := stride
  have hS : 1 ≤ S := by
    dsimp [S]
    exact_mod_cast (show 1 ≤ stride by omega)
  have hSpos : 0 < S := by linarith
  have ht' : 16 * S ≤ t := ht
  have htpos : 0 ≤ t := by nlinarith
  let n₀ : ℕ := ⌈3 * t / 4⌉₊
  let K : ℕ := ⌊t / (8 * S)⌋₊
  have hden : 0 < 8 * S := by positivity
  have hstartlo : 3 * t / 4 ≤ (n₀ : ℝ) := Nat.le_ceil _
  have hstarthi : (n₀ : ℝ) < 3 * t / 4 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hKhi : (K : ℝ) ≤ t / (8 * S) := Nat.floor_le (by positivity)
  have hKlo : t / (8 * S) < (K : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmulhi : S * K ≤ t / 8 := by
    have h := (le_div_iff₀ hden).mp hKhi
    nlinarith
  have hmullo : t / 16 ≤ S * K := by
    have h := (div_lt_iff₀ hden).mp hKlo
    nlinarith
  have hlen : t / (16 * S) ≤ (K : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * S)).2
    nlinarith
  refine ⟨n₀, K, hlen, ?_⟩
  intro k hk
  have hkK : (k : ℝ) ≤ K := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hk))
  have hmul : S * k ≤ S * K := mul_le_mul_of_nonneg_left hkK hSpos.le
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hcast : ((n₀ + stride * k : ℕ) : ℝ) = (n₀ : ℝ) + S * k := by simp [S]
  rw [hcast]
  constructor <;> nlinarith

/-- A logarithmic window contains many geometric radii, even after taking
only every `stride`-th radius. -/
theorem exists_geometric_scales_in_three_quarter_window
    {q ε : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hε : 0 < ε)
    (stride : ℕ) (hstride : 0 < stride)
    (ht : 16 * (stride : ℝ) ≤ Real.logb q ε) :
    ∃ n₀ K : ℕ, Real.logb q ε / (16 * stride) ≤ (K : ℝ) ∧
      ∀ k ∈ Finset.range K, q ^ (n₀ + stride * k) ∈ Icc ε (ε ^ (3 / 4 : ℝ)) := by
  obtain ⟨n₀, K, hK, hrange⟩ :=
    exists_spaced_exponents_in_three_quarter_window (Real.logb q ε) stride hstride ht
  refine ⟨n₀, K, hK, ?_⟩
  intro k hk
  obtain ⟨hlo, hhi⟩ := hrange k hk
  have hpow : q ^ Real.logb q ε = ε := Real.rpow_logb hq0 (ne_of_lt hq1) hε
  constructor
  · rw [← hpow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le hhi
  · rw [← hpow, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le
    linarith

/-- The same geometric window stated in the logarithmic convention of the
prevalence statements, with base `b > 1` and inverse powers of `b`. -/
theorem exists_inverse_geometric_scales_in_three_quarter_window
    {b ε : ℝ} (hb : 1 < b) (hε : 0 < ε)
    (stride : ℕ) (hstride : 0 < stride)
    (ht : 16 * (stride : ℝ) ≤ Real.logb b (ε ^ (-1 : ℝ))) :
    ∃ n₀ K : ℕ, Real.logb b (ε ^ (-1 : ℝ)) / (16 * stride) ≤ (K : ℝ) ∧
      ∀ k ∈ Finset.range K,
        b⁻¹ ^ (n₀ + stride * k) ∈ Icc ε (ε ^ (3 / 4 : ℝ)) := by
  have hlog : Real.logb b⁻¹ ε = Real.logb b (ε ^ (-1 : ℝ)) := by
    rw [Real.rpow_neg_one, Real.logb_inv, Real.logb_inv_base]
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hq0 : 0 < b⁻¹ := inv_pos.mpr hb0
  have hq1 : b⁻¹ < 1 := (inv_lt_one₀ hb0).2 hb
  rw [← hlog] at ht ⊢
  exact exists_geometric_scales_in_three_quarter_window hq0 hq1 hε stride hstride ht


end HarmonicBalls.Section6
