import HarmonicBalls.Proofs.Potential.BrownianSharpLogOccupationTail

/-! # Brownian occupation on finite grids

Logarithmic occupation tail bounds extend to finite grids and varying moment orders.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped Interval NNReal ENNReal

namespace HarmonicBalls

/-- A finite family of balls satisfies the logarithmic occupation tail bound. -/
theorem planarBrownianMotion_occupation_finite_union_le_log_kernel
    (x : ℂ) (G : Finset ℂ) (n : ℕ) {r : ℝ} (hr : 0 < r)
    (ha1 : (2 / Real.pi) * (2 * r) ^ 2 ≤ 1)
    (ε : ℝ≥0∞) (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    let a := (2 / Real.pi) * (2 * r) ^ 2
    planarBrownianMotion x {b | ∃ z ∈ G, ε ≤ ν {t | ‖b t - z‖ < r}} ≤
      (G.card : ℝ≥0∞) *
        (((Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) *
          ENNReal.ofReal (2 * (a * (1 + Real.log (1 / a)))) ^ n) / ε ^ (n + 1)) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let a := (2 / Real.pi) * (2 * r) ^ 2
  let R := ((Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ≥0∞) *
    ENNReal.ofReal (2 * (a * (1 + Real.log (1 / a)))) ^ n) / ε ^ (n + 1)
  calc
    _ = planarBrownianMotion x (⋃ z ∈ G, {b | ε ≤ ν {t | ‖b t - z‖ < r}}) := by
      congr 1; ext b; simp [ν]
    _ ≤ ∑ z ∈ G, planarBrownianMotion x {b | ε ≤ ν {t | ‖b t - z‖ < r}} :=
      measure_biUnion_finset_le G _
    _ ≤ ∑ _z ∈ G, R := by
      apply Finset.sum_le_sum
      intro z hz
      exact planarBrownianMotion_occupation_tail_le_log_kernel x z n hr ha1 ε hε0 hεtop
    _ = _ := by simp [R, a]

/-- Summable logarithmic tails give eventual occupation bounds on each finite grid. -/
theorem planarBrownianMotion_occupation_eventually_lt_of_log_kernel_summable
    (x : ℂ) (G : ℕ → Finset ℂ) (n : ℕ → ℕ) (r : ℕ → ℝ) (ε : ℕ → ℝ≥0∞)
    (hr : ∀ k, 0 < r k) (ha1 : ∀ k, (2 / Real.pi) * (2 * r k) ^ 2 ≤ 1)
    (hε0 : ∀ k, ε k ≠ 0) (hεtop : ∀ k, ε k ≠ ∞)
    (hsum : (∑' k, ((G k).card : ℝ≥0∞) *
      (((Fintype.card (Equiv.Perm (Fin (n k + 1))) : ℝ≥0∞) *
        ENNReal.ofReal (2 * (((2 / Real.pi) * (2 * r k) ^ 2) *
          (1 + Real.log (1 / ((2 / Real.pi) * (2 * r k) ^ 2))))) ^ (n k)) /
            ε k ^ (n k + 1))) ≠ ∞) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ᶠ k in Filter.atTop, ∀ z ∈ G k,
      ν {t | ‖b t - z‖ < r k} < ε k := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let E : ℕ → Set (ContinuousPath ℂ) :=
    fun k => {b | ∃ z ∈ G k, ε k ≤ ν {t | ‖b t - z‖ < r k}}
  have hsum' : (∑' k, planarBrownianMotion x (E k)) ≠ ∞ := by
    apply ne_top_of_le_ne_top hsum
    apply ENNReal.tsum_le_tsum
    intro k
    exact planarBrownianMotion_occupation_finite_union_le_log_kernel x (G k) (n k)
      (hr k) (ha1 k) (ε k) (hε0 k) (hεtop k)
  filter_upwards [ae_eventually_notMem hsum'] with b hb
  filter_upwards [hb] with k hk z hz
  exact lt_of_not_ge (fun h => hk ⟨z, hz, h⟩)

/-- The factorial growth in varying-order moment bounds is dominated by a geometric series. -/
theorem tsum_factorial_geometric_lt_top {q : ℝ} (hq : 0 ≤ q) (hqsmall : 32 * q < 1) :
    (∑' k : ℕ, ENNReal.ofReal ((16 : ℝ) ^ k * ((k + 1).factorial : ℝ) *
      (q / (k + 1 : ℝ)) ^ k)) < ∞ := by
  have hbase : ENNReal.ofReal (32 * q) < 1 := ENNReal.ofReal_lt_one.mpr hqsmall
  apply lt_of_le_of_lt _ (tsum_geometric_lt_top.mpr hbase)
  apply ENNReal.tsum_le_tsum
  intro k
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ 32 * q)]
  apply ENNReal.ofReal_le_ofReal
  have hf : (((k + 1).factorial : ℕ) : ℝ) ≤ (k + 1 : ℝ) ^ (k + 1) := by
    exact_mod_cast Nat.factorial_le_pow (k + 1)
  have htwo : k + 1 ≤ 2 ^ k := by
    clear hf
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      have hp : 0 < 2 ^ k := by positivity
      nlinarith
  have htwo' : (k + 1 : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast htwo
  have hk : (0 : ℝ) < k + 1 := by positivity
  calc
    _ ≤ (16 : ℝ) ^ k * (k + 1 : ℝ) ^ (k + 1) * (q / (k + 1 : ℝ)) ^ k := by
      gcongr
    _ = (k + 1 : ℝ) * (16 * q) ^ k := by
      rw [pow_succ, div_pow, mul_pow]
      field_simp
    _ ≤ (2 : ℝ) ^ k * (16 * q) ^ k := by gcongr
    _ = (32 * q) ^ k := by rw [← mul_pow]; congr 1; ring

/-- The logarithmic kernel at geometric scales grows at most linearly in the scale index. -/
theorem log_kernel_le_geometric (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (k : ℕ) :
    2 * (c * ((1 / 4 : ℝ) ^ k) *
      (1 + Real.log (1 / (c * ((1 / 4 : ℝ) ^ k))))) ≤
    2 * c * (1 + Real.log (1 / c) + Real.log 4) * (k + 1) * ((1 / 4 : ℝ) ^ k) := by
  have hl : 0 ≤ Real.log (1 / c) := Real.log_nonneg (one_le_div hc |>.2 hc1)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog : Real.log (1 / (c * ((1 / 4 : ℝ) ^ k))) =
      Real.log (1 / c) + k * Real.log 4 := by
    rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hc) (by positivity), Real.log_pow,
      one_div, Real.log_inv]
    rw [one_div, Real.log_inv]
    ring
  rw [hlog]
  have hscale : 0 ≤ c * ((1 / 4 : ℝ) ^ k) := by positivity
  have hindex : 0 ≤ (k : ℝ) := by positivity
  have hbound : 1 + Real.log (1 / c) + (k : ℝ) * Real.log 4 ≤
      (1 + Real.log (1 / c) + Real.log 4) * (k + 1) := by nlinarith
  nlinarith [mul_nonneg hscale (sub_nonneg.mpr hbound)]

/-- A pair of scale bounds implies summability of the varying-order tail series. -/
theorem tsum_varying_factorial_tail_lt_top (g v ε : ℕ → ℝ) (C q : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hqsmall : 32 * q < 1)
    (hv : ∀ k, 0 ≤ v k) (hε : ∀ k, 0 < ε k)
    (hgrid : ∀ k, g k / ε k ≤ C * (16 : ℝ) ^ k)
    (hkernel : ∀ k, v k / ε k ≤ q / (k + 1 : ℝ)) :
    (∑' k : ℕ, ENNReal.ofReal (g k * (((k + 1).factorial : ℝ) *
      (v k) ^ k / (ε k) ^ (k + 1)))) < ∞ := by
  have hsum : (∑' k : ℕ, ENNReal.ofReal C *
      ENNReal.ofReal ((16 : ℝ) ^ k * ((k + 1).factorial : ℝ) *
        (q / (k + 1 : ℝ)) ^ k)) < ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (tsum_factorial_geometric_lt_top hq hqsmall)
  apply lt_of_le_of_lt _ hsum
  apply ENNReal.tsum_le_tsum
  intro k
  rw [← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  have hratio : 0 ≤ v k / ε k := div_nonneg (hv k) (hε k).le
  calc
    _ = (g k / ε k) * ((k + 1).factorial : ℝ) * (v k / ε k) ^ k := by
      rw [div_pow, pow_succ]
      field_simp
    _ ≤ (C * (16 : ℝ) ^ k) * ((k + 1).factorial : ℝ) *
        (v k / ε k) ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hgrid k) (by positivity))
        (pow_nonneg hratio _)
    _ ≤ (C * (16 : ℝ) ^ k) * ((k + 1).factorial : ℝ) *
        (q / (k + 1 : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hratio (hkernel k) k) (by positivity)
    _ = _ := by ring

/-- Geometric grid growth and logarithmic kernels give summable moment tails. -/
theorem tsum_log_kernel_geometric_tail_lt_top (g : ℕ → ℝ) (B c D : ℝ)
    (hB : 0 ≤ B) (hc : 0 < c) (hc1 : c ≤ 1)
    (hD : 32 * (2 * c * (1 + Real.log (1 / c) + Real.log 4)) < D)
    (hg : ∀ k, g k ≤ B * (4 : ℝ) ^ k) :
    (∑' k : ℕ, ENNReal.ofReal (g k * (((k + 1).factorial : ℝ) *
      (2 * (c * (1 / 4 : ℝ) ^ k *
        (1 + Real.log (1 / (c * (1 / 4 : ℝ) ^ k))))) ^ k /
      (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) ^ (k + 1)))) < ∞ := by
  let A := 2 * c * (1 + Real.log (1 / c) + Real.log 4)
  have hlog : 0 ≤ Real.log (1 / c) := Real.log_nonneg (one_le_div hc |>.2 hc1)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  change 32 * A < D at hD
  have hDpos : 0 < D := by nlinarith [hD]
  apply tsum_varying_factorial_tail_lt_top g
    (fun k => 2 * (c * (1 / 4 : ℝ) ^ k *
      (1 + Real.log (1 / (c * (1 / 4 : ℝ) ^ k)))))
    (fun k => D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) (B / D) (A / D)
  · positivity
  · positivity
  · rw [← mul_div_assoc]
    exact (div_lt_one hDpos).2 hD
  · intro k
    have ha : c * (1 / 4 : ℝ) ^ k ≤ 1 := by
      calc
        _ ≤ c * 1 := by gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
        _ ≤ 1 := by simpa using hc1
    have hl : 0 ≤ Real.log (1 / (c * (1 / 4 : ℝ) ^ k)) :=
      Real.log_nonneg (one_le_div (by positivity) |>.2 ha)
    positivity
  · intro k; positivity
  · intro k
    have hk : (1 : ℝ) ≤ k + 1 := by exact_mod_cast (Nat.le_add_left 1 k)
    have hδ : (0 : ℝ) < (1 / 4 : ℝ) ^ k := by positivity
    have hid : (4 : ℝ) ^ k * (1 / 4 : ℝ) ^ k = 1 := by
      rw [← mul_pow]; norm_num
    have hlow : D * (1 / 4 : ℝ) ^ k ≤ D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k := by
      have hs : (1 : ℝ) ≤ (k + 1 : ℝ) ^ 2 := by nlinarith
      have hm := mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg hDpos.le hδ.le)
      nlinarith
    calc
      _ ≤ (B * (4 : ℝ) ^ k) / (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) := by
        gcongr; exact hg k
      _ ≤ (B * (4 : ℝ) ^ k) / (D * (1 / 4 : ℝ) ^ k) := by
        gcongr
      _ = (B / D) * (16 : ℝ) ^ k := by
        have h16 : (16 : ℝ) ^ k = ((4 : ℝ) ^ k) ^ 2 := by
          calc
            _ = (4 * 4 : ℝ) ^ k := by norm_num
            _ = _ := by rw [mul_pow]; ring
        rw [h16]
        field_simp
        nlinarith [hid]
  · intro k
    have hk : (0 : ℝ) < k + 1 := by positivity
    have hδ : (0 : ℝ) < (1 / 4 : ℝ) ^ k := by positivity
    calc
      _ ≤ (A * (k + 1 : ℝ) * (1 / 4 : ℝ) ^ k) /
          (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact log_kernel_le_geometric c hc hc1 k
      _ = (A / D) / (k + 1 : ℝ) := by field_simp

/-- The logarithmic finite-grid tail series is summable at geometric scales. -/
theorem tsum_log_kernel_grid_tail_lt_top (G : ℕ → Finset ℂ) (B c D : ℝ)
    (hB : 0 ≤ B) (hc : 0 < c) (hc1 : c ≤ 1)
    (hD : 32 * (2 * c * (1 + Real.log (1 / c) + Real.log 4)) < D)
    (hG : ∀ k, ((G k).card : ℝ) ≤ B * (4 : ℝ) ^ k) :
    (∑' k : ℕ, ((G k).card : ℝ≥0∞) *
      (((Fintype.card (Equiv.Perm (Fin (k + 1))) : ℝ≥0∞) *
        ENNReal.ofReal (2 * (c * (1 / 4 : ℝ) ^ k *
          (1 + Real.log (1 / (c * (1 / 4 : ℝ) ^ k))))) ^ k) /
        ENNReal.ofReal (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) ^ (k + 1))) < ∞ := by
  have hlog : 0 ≤ Real.log (1 / c) := Real.log_nonneg (one_le_div hc |>.2 hc1)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hDpos : 0 < D := by nlinarith [mul_pos hc (show 0 < 1 + Real.log (1 / c) + Real.log 4 by positivity)]
  have hv (k : ℕ) : 0 ≤ 2 * (c * (1 / 4 : ℝ) ^ k *
      (1 + Real.log (1 / (c * (1 / 4 : ℝ) ^ k)))) := by
    have ha : c * (1 / 4 : ℝ) ^ k ≤ 1 := by
      calc
        _ ≤ c * 1 := by gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
        _ ≤ 1 := by simpa using hc1
    have hl : 0 ≤ Real.log (1 / (c * (1 / 4 : ℝ) ^ k)) :=
      Real.log_nonneg (one_le_div (by positivity) |>.2 ha)
    positivity
  have hε (k : ℕ) : 0 < D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k := by positivity
  have heq (k : ℕ) : ENNReal.ofReal (((G k).card : ℝ) * (((k + 1).factorial : ℝ) *
      (2 * (c * (1 / 4 : ℝ) ^ k *
        (1 + Real.log (1 / (c * (1 / 4 : ℝ) ^ k))))) ^ k /
      (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) ^ (k + 1))) =
      ((G k).card : ℝ≥0∞) *
      (((Fintype.card (Equiv.Perm (Fin (k + 1))) : ℝ≥0∞) *
        ENNReal.ofReal (2 * (c * (1 / 4 : ℝ) ^ k *
          (1 + Real.log (1 / (c * (1 / 4 : ℝ) ^ k))))) ^ k) /
        ENNReal.ofReal (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) ^ (k + 1)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos (pow_pos (hε k) _),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (hv k),
      ENNReal.ofReal_pow (hε k).le]
    simp [Fintype.card_perm]
  simp_rw [← heq]
  exact tsum_log_kernel_geometric_tail_lt_top (fun k => ((G k).card : ℝ)) B c D hB hc hc1 hD hG

/-- The endpoint kernel parameter at enlarged dyadic radii. -/
theorem dyadic_log_kernel_parameter (k : ℕ) :
    (2 / Real.pi) * (2 * (2 * (2 : ℝ)⁻¹ ^ (k + 3))) ^ 2 =
      (1 / (2 * Real.pi)) * (1 / 4 : ℝ) ^ k := by
  have hp : (2 : ℝ)⁻¹ ^ (k + 3) = (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ k := by
    rw [pow_add]
    norm_num
    ring
  have hpow : ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 4 : ℝ) ^ k := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [hp, ← hpow]
  field_simp
  ring

/-- The shifted dyadic square grid has geometric cardinality growth. -/
theorem squareGrid_shifted_card_le_geometric (N k : ℕ) :
    ((squareGrid N (2 ^ (k + 3 + 1))).card : ℝ) ≤
      (64 * ((4 * N + 1 : ℕ) : ℝ) ^ 2) * (4 : ℝ) ^ k := by
  have h := squareGrid_dyadic_card_le N (k + 3)
  have h' : ((squareGrid N (2 ^ (k + 3 + 1))).card : ℝ) ≤
      (((4 * N + 1) ^ 2 * (2 ^ (k + 3)) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
  convert h' using 1
  push_cast
  rw [pow_add]
  norm_num
  have hpow : ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [mul_pow, hpow]
  ring

/-- Fine dyadic occupation bounds hold at all centres in any bounded region. -/
theorem planarBrownianMotion_dyadic_log_occupation (x : ℂ) (N : ℕ) (D : ℝ)
    (hD : 32 * (2 * (1 / (2 * Real.pi)) *
      (1 + Real.log (1 / (1 / (2 * Real.pi))) + Real.log 4)) < D) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ᶠ k : ℕ in Filter.atTop, ∀ z : ℂ, ‖z‖ ≤ N →
      ν {t | ‖b t - z‖ < (2 : ℝ)⁻¹ ^ (k + 3)} ≤
        ENNReal.ofReal (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let c : ℝ := 1 / (2 * Real.pi)
  let B : ℝ := 64 * ((4 * N + 1 : ℕ) : ℝ) ^ 2
  let G : ℕ → Finset ℂ := fun k => squareGrid N (2 ^ (k + 3 + 1))
  let r : ℕ → ℝ := fun k => 2 * (2 : ℝ)⁻¹ ^ (k + 3)
  let ε : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)).2
    linarith [Real.pi_gt_three]
  have hlog : 0 ≤ Real.log (1 / c) := Real.log_nonneg (one_le_div hc |>.2 hc1)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hDpos : 0 < D := by
    change 32 * (2 * c * (1 + Real.log (1 / c) + Real.log 4)) < D at hD
    nlinarith [mul_pos hc (show 0 < 1 + Real.log (1 / c) + Real.log 4 by positivity)]
  have ha (k : ℕ) : (2 / Real.pi) * (2 * r k) ^ 2 = c * (1 / 4 : ℝ) ^ k :=
    dyadic_log_kernel_parameter k
  have ha1 (k : ℕ) : (2 / Real.pi) * (2 * r k) ^ 2 ≤ 1 := by
    rw [ha]
    calc
      _ ≤ c * 1 := by gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
      _ ≤ 1 := by simpa using hc1
  have hsum := tsum_log_kernel_grid_tail_lt_top G B c D (by dsimp [B]; positivity) hc hc1 hD
    (fun k => squareGrid_shifted_card_le_geometric N k)
  have hsum' : (∑' k, ((G k).card : ℝ≥0∞) *
      (((Fintype.card (Equiv.Perm (Fin (k + 1))) : ℝ≥0∞) *
        ENNReal.ofReal (2 * (((2 / Real.pi) * (2 * r k) ^ 2) *
          (1 + Real.log (1 / ((2 / Real.pi) * (2 * r k) ^ 2))))) ^ k) /
            ε k ^ (k + 1))) ≠ ∞ := by
    simp_rw [ha]
    exact hsum.ne
  have hevent := planarBrownianMotion_occupation_eventually_lt_of_log_kernel_summable x G
    (fun k => k) r ε (fun k => by dsimp [r]; positivity) ha1
    (fun k => ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
    (fun _ => ENNReal.ofReal_ne_top) hsum'
  filter_upwards [hevent] with b hb
  apply hb.mono
  intro k hk z hz
  apply occupation_le_of_squareGrid ν b N (k + 3) (ε k) _ z hz
  intro w hw
  exact (hk w hw).le

/-- Fine dyadic occupation bounds hold simultaneously at every centre. -/
theorem planarBrownianMotion_dyadic_log_occupation_global (x : ℂ) (D : ℝ)
    (hD : 32 * (2 * (1 / (2 * Real.pi)) *
      (1 + Real.log (1 / (1 / (2 * Real.pi))) + Real.log 4)) < D) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ᶠ k : ℕ in Filter.atTop, ∀ z : ℂ,
      ν {t | ‖b t - z‖ < (2 : ℝ)⁻¹ ^ (k + 3)} ≤
        ENNReal.ofReal (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hN : ∀ N : ℕ, ∀ᵐ b ∂(planarBrownianMotion x), ∀ᶠ k : ℕ in Filter.atTop,
      ∀ z : ℂ, ‖z‖ ≤ N → ν {t | ‖b t - z‖ < (2 : ℝ)⁻¹ ^ (k + 3)} ≤
        ENNReal.ofReal (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) :=
    fun N => planarBrownianMotion_dyadic_log_occupation x N D hD
  have hs : ∀ᵐ y ∂ν, y ≤ 1 := by
    dsimp [ν]
    apply (ae_map_iff continuous_real_toNNReal.measurable.aemeasurable
      (measurableSet_le measurable_id measurable_const)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact Real.toNNReal_le_iff_le_coe.mpr (by simpa using hy.2)
  filter_upwards [ae_all_iff.mpr hN] with b hb
  obtain ⟨N, hN⟩ := continuousPath_bounded_unit_time b
  filter_upwards [hb (N + 2)] with k hk z
  by_cases hz : ‖z‖ ≤ (N + 2 : ℕ)
  · exact hk z hz
  · have hδ : (2 : ℝ)⁻¹ ^ (k + 3) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hnil : ν {t | ‖b t - z‖ < (2 : ℝ)⁻¹ ^ (k + 3)} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hs] with t ht
      have htri := norm_add_le (z - b t) (b t)
      have hnorm : ‖z‖ ≤ ‖z - b t‖ + ‖b t‖ := by simpa using htri
      have heq : ‖z - b t‖ = ‖b t - z‖ := norm_sub_rev _ _
      push_cast at hz
      rw [heq] at hnorm
      linarith [hN t ht]
    rw [hnil]
    exact zero_le

/-- A dyadic logarithmic occupation bound extends to all sufficiently small radii. -/
theorem occupation_log_bound_of_dyadic (ν : Measure ℝ≥0) (b : ContinuousPath ℂ)
    (D : ℝ) (hD : 0 < D) (k₀ : ℕ)
    (h : ∀ k ≥ k₀, ∀ z : ℂ,
      ν {t | ‖b t - z‖ < (2 : ℝ)⁻¹ ^ (k + 3)} ≤
        ENNReal.ofReal (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k)) :
    ∀ (z : ℂ) (r : ℝ), 0 < r → r < (2 : ℝ)⁻¹ ^ (k₀ + 3) →
      ν {t | ‖b t - z‖ < r} ≤
        ENNReal.ofReal ((256 * D / (Real.log 2) ^ 2) * r ^ 2 * (Real.log (1 / r)) ^ 2) := by
  intro z r hr hrsmall
  have hr1 : r ≤ 1 := le_trans hrsmall.le (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hj : k₀ + 3 ≤ j := by
    by_contra hn
    have hn' : j + 1 ≤ k₀ + 3 := by omega
    have hp : (2 : ℝ)⁻¹ ^ (k₀ + 3) ≤ (2 : ℝ)⁻¹ ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn'
    linarith
  let k := j - 3
  have hjk : j = k + 3 := by dsimp [k]; omega
  have hk : k₀ ≤ k := by omega
  have hδ : 0 < (2 : ℝ)⁻¹ ^ (k + 3) := by positivity
  have hδr : (2 : ℝ)⁻¹ ^ (k + 3) ≤ 2 * r := by
    rw [hjk, pow_succ] at hj1
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (k + 1 : ℝ) * Real.log 2 ≤ Real.log (1 / r) := by
    have hh := Real.log_le_log hr hj2
    rw [hjk, Real.log_pow, Real.log_inv] at hh
    rw [one_div, Real.log_inv]
    push_cast at hh
    nlinarith
  have hklog : (k + 1 : ℝ) ≤ Real.log (1 / r) / Real.log 2 :=
    (le_div_iff₀ hlog2).2 hlog
  have hsq : (k + 1 : ℝ) ^ 2 ≤ (Real.log (1 / r) / Real.log 2) ^ 2 := by
    have hkpos : (0 : ℝ) ≤ k + 1 := by positivity
    nlinarith
  have hpow : (1 / 4 : ℝ) ^ k = 64 * ((2 : ℝ)⁻¹ ^ (k + 3)) ^ 2 := by
    rw [pow_add]
    norm_num
    have hp : ((2 : ℝ)⁻¹ ^ k) ^ 2 = (1 / 4 : ℝ) ^ k := by
      rw [pow_two, ← mul_pow]
      norm_num
    nlinarith [hp]
  have hδsq : ((2 : ℝ)⁻¹ ^ (k + 3)) ^ 2 ≤ 4 * r ^ 2 := by nlinarith
  have hcomp : D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k ≤
      (256 * D / (Real.log 2) ^ 2) * r ^ 2 * (Real.log (1 / r)) ^ 2 := by
    rw [hpow]
    calc
      _ ≤ D * (Real.log (1 / r) / Real.log 2) ^ 2 * (64 * (4 * r ^ 2)) := by gcongr
      _ = _ := by field_simp; ring
  calc
    _ ≤ ν {t | ‖b t - z‖ < (2 : ℝ)⁻¹ ^ (k + 3)} := by
      apply measure_mono
      intro t ht
      change ‖b t - z‖ < (2 : ℝ)⁻¹ ^ (k + 3)
      rw [← hjk]
      exact lt_of_lt_of_le ht hj2
    _ ≤ ENNReal.ofReal (D * (k + 1 : ℝ) ^ 2 * (1 / 4 : ℝ) ^ k) := h k hk z
    _ ≤ _ := ENNReal.ofReal_le_ofReal hcomp

/-- Planar Brownian unit-time occupation has a uniform sharp logarithmic ball bound. -/
theorem planarBrownianMotion_uniform_ball_occupation_log (x : ℂ) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ (z : ℂ) (r : ℝ), 0 < r → r < r₀ →
        ν {t | ‖b t - z‖ < r} ≤ ENNReal.ofReal (C * r ^ 2 * (Real.log (1 / r)) ^ 2) := by
  let c : ℝ := 1 / (2 * Real.pi)
  let A : ℝ := 2 * c * (1 + Real.log (1 / c) + Real.log 4)
  let D : ℝ := 64 * A + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * Real.pi)).2
    linarith [Real.pi_gt_three]
  have hlog : 0 ≤ Real.log (1 / c) := Real.log_nonneg (one_le_div hc |>.2 hc1)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 32 * A < D := by dsimp [D]; linarith
  have hDpos : 0 < D := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [planarBrownianMotion_dyadic_log_occupation_global x D hD] with b hb
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp hb
  refine ⟨256 * D / (Real.log 2) ^ 2, by positivity, (2 : ℝ)⁻¹ ^ (k₀ + 3), by positivity, ?_⟩
  exact occupation_log_bound_of_dyadic _ b D hDpos k₀ hk₀

/-- The logarithmic occupation bound expressed in real time on the unit interval. -/
theorem planarBrownianMotion_uniform_ball_occupation_log_real_time (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 < C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ (z : ℂ) (r : ℝ), 0 < r → r < r₀ →
        volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ ‖b (Real.toNNReal t) - z‖ < r} ≤
          ENNReal.ofReal (C * r ^ 2 * (Real.log (1 / r)) ^ 2) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [planarBrownianMotion_uniform_ball_occupation_log x] with b hb
  obtain ⟨C, hC, r₀, hr₀, hbound⟩ := hb
  refine ⟨C, hC, r₀, hr₀, ?_⟩
  intro z r hr hrsmall
  have hm : MeasurableSet {t : ℝ≥0 | ‖b t - z‖ < r} := by
    apply isOpen_lt _ continuous_const |>.measurableSet
    fun_prop
  have heq : volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ ‖b (Real.toNNReal t) - z‖ < r} =
      ν {t | ‖b t - z‖ < r} := by
    dsimp [ν]
    rw [Measure.map_apply continuous_real_toNNReal.measurable hm,
      Measure.restrict_apply (continuous_real_toNNReal.measurable hm)]
    congr 1
    ext t
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    tauto
  rw [heq]
  exact hbound z r hr hrsmall

end HarmonicBalls
