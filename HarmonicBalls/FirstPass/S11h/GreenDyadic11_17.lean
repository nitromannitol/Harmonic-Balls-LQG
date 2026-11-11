import HarmonicBalls.FirstPass.S11h.GreenPotential11_17

/-!
# Lemma 11.17: the dyadic level-set formula for lower semicontinuous integrals

For a lower semicontinuous `κ : ℂ → ℝ≥0∞` and a measure `μ`, the integral `∫_A κ dμ` over a set `A` is the supremum over
`n` of the dyadic sums `∑_{k < n 2^n} 2^{-n} μ(A ∩ {(k+1)/2^n < κ})` (layer-cake approximation from below). For open `A`
each level set `A ∩ {(k+1)/2^n < κ}` is open, so each summand is the mass of an open set and the field-level mass decoder
`exists_mass_open_functional` applies to it (GreenField11_17.lean). The proof here is elementary (counting, and Fatou's lemma as in GreenPotential11_17.lean).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Topology
open scoped ENNReal

/-- The `n`-th dyadic approximation of `κ`: the simple function `∑_{k < n 2^n} 2^{-n} 1{(k+1)/2^n < κ}`. -/
noncomputable def dyadicFun (κ : ℂ → ℝ≥0∞) (n : ℕ) (y : ℂ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (n * 2 ^ n),
    if ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < κ y then ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) else 0

/-- The level set `{y | (k+1)/2^n < κ y}` of the `n`-th dyadic approximation. -/
def dyadicLevel (κ : ℂ → ℝ≥0∞) (n k : ℕ) : Set ℂ :=
  {y | ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < κ y}

/-- Counting, upper bound: at most `m` naturals `k < N` satisfy `k + 1 < m`, for `m ≥ 0`. -/
theorem card_filter_succ_lt_le {m : ℝ} (hm : 0 ≤ m) (N : ℕ) :
    ((Finset.range N).filter (fun k : ℕ => (k : ℝ) + 1 < m)).card ≤ m := by
  have hsub : (Finset.range N).filter (fun k : ℕ => (k : ℝ) + 1 < m) ⊆ Finset.range ⌊m⌋₊ := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have h1 : ((k + 1 : ℕ) : ℝ) ≤ m := by push_cast; exact hk.2.le
    rw [Finset.mem_range]
    have := Nat.le_floor h1
    omega
  have h1 : ((Finset.range N).filter (fun k : ℕ => (k : ℝ) + 1 < m)).card ≤ ⌊m⌋₊ := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_range] at this
  exact le_trans (by exact_mod_cast h1) (Nat.floor_le hm)

/-- Counting, lower bound: if `m ≥ 0` and `⌊m⌋₊ ≤ N + 1`, then `m < #{k < N : k + 1 < m} + 2`. -/
theorem lt_card_filter_succ_lt_add_two {m : ℝ} (hm : 0 ≤ m) (N : ℕ) (hN : ⌊m⌋₊ ≤ N + 1) :
    m < (((Finset.range N).filter (fun k : ℕ => (k : ℝ) + 1 < m)).card : ℝ) + 2 := by
  have hfl : m < (⌊m⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one m
  rcases Nat.lt_or_ge ⌊m⌋₊ 2 with h2 | h2
  · have h0 : (0 : ℝ) ≤ (((Finset.range N).filter (fun k : ℕ => (k : ℝ) + 1 < m)).card : ℝ) :=
      Nat.cast_nonneg _
    have h1 : (⌊m⌋₊ : ℝ) ≤ 1 := by exact_mod_cast (by omega : ⌊m⌋₊ ≤ 1)
    linarith
  · have hsub : Finset.range (⌊m⌋₊ - 1) ⊆ (Finset.range N).filter (fun k : ℕ => (k : ℝ) + 1 < m) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      have h1 : ((k + 2 : ℕ) : ℝ) ≤ (⌊m⌋₊ : ℝ) := by exact_mod_cast (by omega : k + 2 ≤ ⌊m⌋₊)
      have h3 : (⌊m⌋₊ : ℝ) ≤ m := Nat.floor_le hm
      push_cast at h1
      linarith
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    have hc' : ((⌊m⌋₊ - 1 : ℕ) : ℝ) ≤
        (((Finset.range N).filter (fun k : ℕ => (k : ℝ) + 1 < m)).card : ℝ) := by
      exact_mod_cast hc
    have hsub1 : ((⌊m⌋₊ - 1 : ℕ) : ℝ) = (⌊m⌋₊ : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    linarith

/-- The dyadic sum is the number of admissible levels times the weight `2^{-n}`. -/
theorem dyadicFun_eq_card (κ : ℂ → ℝ≥0∞) (n : ℕ) (y : ℂ) :
    dyadicFun κ n y = (((Finset.range (n * 2 ^ n)).filter
      (fun k : ℕ => ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < κ y)).card : ℝ≥0∞) *
      ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) := by
  unfold dyadicFun
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

/-- Upper bound: the `n`-th dyadic approximation lies below `κ`. -/
theorem dyadicFun_le (κ : ℂ → ℝ≥0∞) (n : ℕ) (y : ℂ) : dyadicFun κ n y ≤ κ y := by
  rcases eq_or_ne (κ y) ⊤ with h | h
  · rw [h]
    exact le_top
  have hκr : κ y = ENNReal.ofReal (κ y).toReal := (ENNReal.ofReal_toReal h).symm
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  rw [dyadicFun_eq_card, hκr]
  have hsub : (Finset.range (n * 2 ^ n)).filter
      (fun k : ℕ => ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < ENNReal.ofReal (κ y).toReal) ⊆
      (Finset.range (n * 2 ^ n)).filter (fun k : ℕ => (k : ℝ) + 1 < 2 ^ n * (κ y).toReal) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have ht := (ENNReal.ofReal_lt_ofReal_iff'.1 hk.2).1
    rw [div_lt_iff₀ hn] at ht
    rw [mul_comm]
    exact ht
  have hcard : ((((Finset.range (n * 2 ^ n)).filter
      (fun k : ℕ => ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < ENNReal.ofReal (κ y).toReal)).card : ℕ) : ℝ) ≤
      2 ^ n * (κ y).toReal :=
    le_trans (by exact_mod_cast Finset.card_le_card hsub)
      (card_filter_succ_lt_le (m := 2 ^ n * (κ y).toReal) (by positivity) (n * 2 ^ n))
  have hdiv : (((Finset.range (n * 2 ^ n)).filter
      (fun k : ℕ => ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < ENNReal.ofReal (κ y).toReal)).card : ℝ) *
      (2 ^ n : ℝ)⁻¹ ≤ (κ y).toReal := by
    rw [← div_eq_mul_inv, div_le_iff₀ hn, mul_comm (κ y).toReal]
    exact hcard
  calc _ = ENNReal.ofReal ((((Finset.range (n * 2 ^ n)).filter
          (fun k : ℕ => ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < ENNReal.ofReal (κ y).toReal)).card : ℝ) *
          (2 ^ n : ℝ)⁻¹) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (κ y).toReal := ENNReal.ofReal_le_ofReal hdiv

/-- Lower bound: if `0 ≤ c < κ y` and `c ≤ n`, the `n`-th dyadic approximation is at least `c - 2 · 2^{-n}`. -/
theorem ofReal_sub_le_dyadicFun (κ : ℂ → ℝ≥0∞) (y : ℂ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ENNReal.ofReal c < κ y) (n : ℕ) (hcn : c ≤ n) :
    ENNReal.ofReal (c - 2 * (2 ^ n : ℝ)⁻¹) ≤ dyadicFun κ n y := by
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  have he : (2 ^ n : ℝ)⁻¹ * 2 ^ n = 1 := inv_mul_cancel₀ hn.ne'
  have hm0 : 0 ≤ (2 ^ n : ℝ) * c := by positivity
  have hfl : ((⌊(2 ^ n : ℝ) * c⌋₊ : ℕ) : ℝ) ≤ ((n * 2 ^ n : ℕ) : ℝ) := by
    refine (Nat.floor_le hm0).trans ?_
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hcn hn.le]
  have hfl' : ⌊(2 ^ n : ℝ) * c⌋₊ ≤ n * 2 ^ n := by exact_mod_cast hfl
  have hcount := lt_card_filter_succ_lt_add_two hm0 (n * 2 ^ n) (by omega)
  have hsub : (Finset.range (n * 2 ^ n)).filter (fun k : ℕ => (k : ℝ) + 1 < (2 ^ n : ℝ) * c) ⊆
      (Finset.range (n * 2 ^ n)).filter
        (fun k : ℕ => ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < κ y) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have ht : ((k : ℝ) + 1) / 2 ^ n < c := by
      rw [div_lt_iff₀ hn, mul_comm]
      exact hk.2
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.le) hc
  rw [dyadicFun_eq_card]
  have hcardQ : (2 ^ n : ℝ) * c - 2 < (((Finset.range (n * 2 ^ n)).filter
      (fun k : ℕ => (k : ℝ) + 1 < (2 ^ n : ℝ) * c)).card : ℝ) := by
    linarith [hcount]
  have hid : ((2 ^ n : ℝ) * c - 2) * (2 ^ n : ℝ)⁻¹ = c - 2 * (2 ^ n : ℝ)⁻¹ := by
    linear_combination c * he
  have hsubcard : (((Finset.range (n * 2 ^ n)).filter
      (fun k : ℕ => (k : ℝ) + 1 < (2 ^ n : ℝ) * c)).card : ℝ≥0∞) ≤
      ((Finset.range (n * 2 ^ n)).filter
        (fun k : ℕ => ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n) < κ y)).card :=
    by exact_mod_cast Finset.card_le_card hsub
  have hineq : c - 2 * (2 ^ n : ℝ)⁻¹ ≤
      (((Finset.range (n * 2 ^ n)).filter
        (fun k : ℕ => (k : ℝ) + 1 < (2 ^ n : ℝ) * c)).card : ℝ) * (2 ^ n : ℝ)⁻¹ := by
    rw [← hid]
    exact mul_le_mul_of_nonneg_right hcardQ.le (inv_nonneg.2 hn.le)
  calc ENNReal.ofReal (c - 2 * (2 ^ n : ℝ)⁻¹)
      ≤ ENNReal.ofReal ((((Finset.range (n * 2 ^ n)).filter
        (fun k : ℕ => (k : ℝ) + 1 < (2 ^ n : ℝ) * c)).card : ℝ) * (2 ^ n : ℝ)⁻¹) :=
        ENNReal.ofReal_le_ofReal hineq
    _ = (((Finset.range (n * 2 ^ n)).filter
        (fun k : ℕ => (k : ℝ) + 1 < (2 ^ n : ℝ) * c)).card : ℝ≥0∞) *
        ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by gcongr

/-- Lower semicontinuity of the dyadic approximations: `κ y ≤ liminf_n dyadicFun κ n y` for every `y`. -/
theorem le_liminf_dyadicFun (κ : ℂ → ℝ≥0∞) (y : ℂ) :
    κ y ≤ liminf (fun n : ℕ => dyadicFun κ n y) atTop := by
  refine le_of_forall_lt fun t ht => ?_
  obtain ⟨t', ht1, ht2⟩ := exists_between ht
  have hfin : t' ≠ ⊤ := ne_top_of_lt ht2
  have hct : ENNReal.ofReal t'.toReal = t' := ENNReal.ofReal_toReal hfin
  have hc0 : 0 ≤ t'.toReal := ENNReal.toReal_nonneg
  have hcy : ENNReal.ofReal t'.toReal < κ y := by rw [hct]; exact ht2
  have hev : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (t'.toReal - 2 * (2 ^ n : ℝ)⁻¹) ≤ dyadicFun κ n y := by
    filter_upwards [eventually_ge_atTop ⌈t'.toReal⌉₊] with n hn
    exact ofReal_sub_le_dyadicFun κ y hc0 hcy n (le_trans (Nat.le_ceil _) (by exact_mod_cast hn))
  have h0 : Tendsto (fun n : ℕ => (2 ^ n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have h1 : Tendsto (fun n : ℕ => t'.toReal - 2 * (2 ^ n : ℝ)⁻¹) atTop (𝓝 t'.toReal) := by
    simpa using (tendsto_const_nhds (x := t'.toReal)).sub (h0.const_mul 2)
  have hL : Tendsto (fun n : ℕ => ENNReal.ofReal (t'.toReal - 2 * (2 ^ n : ℝ)⁻¹)) atTop (𝓝 t') := by
    have hcomp := (ENNReal.continuous_ofReal.tendsto _).comp h1
    rw [hct] at hcomp
    exact hcomp
  have h2 : t' ≤ liminf (fun n : ℕ => dyadicFun κ n y) atTop := by
    rw [← hL.liminf_eq]
    exact liminf_le_liminf hev
  exact lt_of_lt_of_le ht1 h2

/-- The dyadic approximations are measurable (finite sums of indicators of open level sets). -/
theorem measurable_dyadicFun (κ : ℂ → ℝ≥0∞) (hκ : LowerSemicontinuous κ) (n : ℕ) :
    Measurable (dyadicFun κ n) := by
  unfold dyadicFun
  refine Finset.measurable_sum _ fun k _ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (hκ.isOpen_preimage (ENNReal.ofReal (((k : ℝ) + 1) / 2 ^ n))).measurableSet

/-- Layer-cake approximation of a lower semicontinuous integral over a set:
`∫_A κ dμ = sup_n ∫_A (dyadicFun κ n) dμ`. -/
theorem lintegral_restrict_eq_iSup_dyadic (μ : Measure ℂ) (A : Set ℂ) {κ : ℂ → ℝ≥0∞}
    (hκ : LowerSemicontinuous κ) :
    ∫⁻ y in A, κ y ∂μ = ⨆ n : ℕ, ∫⁻ y in A, dyadicFun κ n y ∂μ := by
  apply le_antisymm
  · calc ∫⁻ y in A, κ y ∂μ ≤ ∫⁻ y in A, liminf (fun n : ℕ => dyadicFun κ n y) atTop ∂μ :=
          lintegral_mono fun y => le_liminf_dyadicFun κ y
      _ ≤ liminf (fun n : ℕ => ∫⁻ y in A, dyadicFun κ n y ∂μ) atTop :=
          lintegral_liminf_le fun n => measurable_dyadicFun κ hκ n
      _ ≤ ⨆ n : ℕ, ∫⁻ y in A, dyadicFun κ n y ∂μ := le_trans liminf_le_limsup limsup_le_iSup
  · exact iSup_le fun n => lintegral_mono fun y => dyadicFun_le κ n y

end HarmonicBalls
