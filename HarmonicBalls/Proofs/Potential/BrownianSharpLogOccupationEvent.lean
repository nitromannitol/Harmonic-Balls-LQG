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

end HarmonicBalls
