import HarmonicBalls.Defs.Notation

/-!
# Events with polynomially high probability

Elementary closure properties of `PolyHighProb` ("with polynomially high probability as `ε → 0`", line 336 of
paper/lqg_harmonic_ball-corrected.tex): monotonicity, finite intersections, linear reparametrization of the scale,
and the Borel-Cantelli lemma along the dyadic scales `ε = 2^{-k}` (the step from Lemma 2.4 to the a.s. statement
eq:volume-growth, line 3529).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- For `a > 0` and `c > 0`, `ε^a ≤ c` for all small `ε > 0`. -/
theorem exists_pos_forall_rpow_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∃ r₁ > 0, ∀ r : ℝ, 0 < r → r < r₁ → r ^ a ≤ c := by
  refine ⟨c ^ a⁻¹, Real.rpow_pos_of_pos hc _, fun r hr hr₁ => ?_⟩
  calc r ^ a ≤ (c ^ a⁻¹) ^ a := Real.rpow_le_rpow hr.le hr₁.le ha.le
    _ = c := by rw [← Real.rpow_mul hc.le, inv_mul_cancel₀ ha.ne', Real.rpow_one]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F : ℝ → Set Ω}

/-- An event containing, at all small scales, an event of polynomially high probability has polynomially high
probability. -/
theorem PolyHighProb.mono_of_small (h : PolyHighProb P E) {r₁ : ℝ} (hr₁ : 0 < r₁)
    (hEF : ∀ r, 0 < r → r < r₁ → E r ⊆ F r) : PolyHighProb P F := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨p, hp, C, min r₀ r₁, lt_min hr₀ hr₁, fun r hr hrr => ?_⟩
  calc P (F r)ᶜ ≤ P (E r)ᶜ :=
        measure_mono (compl_subset_compl.2 (hEF r hr (hrr.trans_le (min_le_right _ _))))
    _ ≤ _ := hE r hr (hrr.trans_le (min_le_left _ _))

theorem PolyHighProb.mono (h : PolyHighProb P E) (hEF : ∀ r, E r ⊆ F r) : PolyHighProb P F :=
  h.mono_of_small one_pos fun r _ _ => hEF r

/-- Linear reparametrization of the scale: `ε ↦ E(c ε)` for a constant `c > 0`. -/
theorem PolyHighProb.comp_mul (h : PolyHighProb P E) {c : ℝ} (hc : 0 < c) :
    PolyHighProb P fun r => E (c * r) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  refine ⟨p, hp, C * c ^ p, r₀ / c, div_pos hr₀ hc, fun r hr hrr => ?_⟩
  have hcr : c * r < r₀ := by rwa [lt_div_iff₀ hc, mul_comm] at hrr
  calc P (E (c * r))ᶜ ≤ ENNReal.ofReal (C * (c * r) ^ p) := hE _ (mul_pos hc hr) hcr
    _ = ENNReal.ofReal (C * c ^ p * r ^ p) := by rw [Real.mul_rpow hc.le hr.le, mul_assoc]

/-- The intersection of two events of polynomially high probability. -/
theorem PolyHighProb.inter (hE : PolyHighProb P E) (hF : PolyHighProb P F) :
    PolyHighProb P fun r => E r ∩ F r := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := hE
  obtain ⟨q, hq, D, s₀, hs₀, hF⟩ := hF
  refine ⟨min p q, lt_min hp hq, max C 0 + max D 0, min (min r₀ s₀) 1,
    lt_min (lt_min hr₀ hs₀) one_pos, fun r hr hrr => ?_⟩
  have hr₀' : r < r₀ := hrr.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hs₀' : r < s₀ := hrr.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hr1 : r < 1 := hrr.trans_le (min_le_right _ _)
  have hpr : r ^ p ≤ r ^ min p q := Real.rpow_le_rpow_of_exponent_ge hr hr1.le (min_le_left _ _)
  have hqr : r ^ q ≤ r ^ min p q := Real.rpow_le_rpow_of_exponent_ge hr hr1.le (min_le_right _ _)
  have hC : C * r ^ p ≤ max C 0 * r ^ min p q :=
    mul_le_mul (le_max_left _ _) hpr (by positivity) (le_max_right _ _)
  have hD : D * r ^ q ≤ max D 0 * r ^ min p q :=
    mul_le_mul (le_max_left _ _) hqr (by positivity) (le_max_right _ _)
  rw [compl_inter]
  calc P ((E r)ᶜ ∪ (F r)ᶜ) ≤ P (E r)ᶜ + P (F r)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C * r ^ p) + ENNReal.ofReal (D * r ^ q) :=
        add_le_add (hE r hr hr₀') (hF r hr hs₀')
    _ ≤ ENNReal.ofReal (max C 0 * r ^ min p q) + ENNReal.ofReal (max D 0 * r ^ min p q) :=
        add_le_add (ENNReal.ofReal_le_ofReal hC) (ENNReal.ofReal_le_ofReal hD)
    _ = ENNReal.ofReal ((max C 0 + max D 0) * r ^ min p q) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

/-- **Borel-Cantelli along the dyadic scales.** If `E` has polynomially high probability, then almost surely
`ω ∈ E(2^{-k})` for all large `k`: the failure probabilities `O(2^{-kp})` are summable. -/
theorem PolyHighProb.ae_eventually_dyadic (h : PolyHighProb P E) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ω ∈ E ((2 : ℝ)⁻¹ ^ k) := by
  obtain ⟨p, hp, C, r₀, hr₀, hE⟩ := h
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hr₀ (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hq : (2 : ℝ)⁻¹ ^ p < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hterm : ∀ n : ℕ, P (E ((2 : ℝ)⁻¹ ^ (n + k₀)))ᶜ ≤
      ENNReal.ofReal (max C 0) * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ p) ^ n := by
    intro n
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (n + k₀) := by positivity
    have hlt : (2 : ℝ)⁻¹ ^ (n + k₀) < r₀ :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left k₀ n)).trans_lt hk₀
    have hle : ((2 : ℝ)⁻¹ ^ (n + k₀)) ^ p ≤ ((2 : ℝ)⁻¹ ^ p) ^ n := by
      rw [← Real.rpow_pow_comm (by norm_num)]
      exact pow_le_pow_of_le_one (Real.rpow_nonneg (by norm_num) _) hq.le (Nat.le_add_right n k₀)
    calc P (E ((2 : ℝ)⁻¹ ^ (n + k₀)))ᶜ ≤ ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ (n + k₀)) ^ p) :=
          hE _ hpos hlt
      _ ≤ ENNReal.ofReal (max C 0 * ((2 : ℝ)⁻¹ ^ p) ^ n) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul (le_max_left _ _) hle
            (by positivity) (le_max_right _ _))
      _ = _ := by
          rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_pow (by positivity)]
  have hsum : ∑' n : ℕ, P (E ((2 : ℝ)⁻¹ ^ (n + k₀)))ᶜ ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
    exact (tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hq)).ne'
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  rw [eventually_atTop] at hω ⊢
  obtain ⟨N, hN⟩ := hω
  refine ⟨N + k₀, fun k hk => ?_⟩
  have h' := hN (k - k₀) (by omega)
  rw [Nat.sub_add_cancel (by omega : k₀ ≤ k)] at h'
  simpa using h'

end HarmonicBalls
