import Mathlib

/-! # Route (A), Palm identity: two measure-theoretic tools of the written proofs of r10

* `ae_tendsto_zero_of_sq_integral_le`: Chebyshev and Borel-Cantelli, as in the paragraph of r10
  `l:r9-circle-code` (r10 lines 1257-1392) that chooses, for each coded circle, a sequence `eps_j` along
  which the squared `L²` error is at most `2^(-4j)`; the errors then tend to zero almost surely
  (`∑_j P(|error| > 2^(-j)) < ∞`).
* `tendsto_integral_abs_sub_of_ae_tendsto`: the `L¹` convergence `E|X_eps - X| → 0` by the min-trick
  `E|X_eps - X| = E X_eps + E X - 2 E min(X_eps, X)`, as in the paragraph "First moments and the required
  `L¹` convergence" of `l:r9-marked` (r10 lines 2575-2790).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Chebyshev and Borel-Cantelli** (r10 `l:r9-circle-code`): if the second moments of `E j` are at most
`(1/16)^j = 2^(-4j)`, then `E j → 0` almost surely. -/
theorem ae_tendsto_zero_of_sq_integral_le {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ℕ → Ω → ℝ} (hint : ∀ j, Integrable (fun ω => E j ω ^ 2) P)
    (hsq : ∀ j, ∫ ω, E j ω ^ 2 ∂P ≤ (1 / 16 : ℝ) ^ j) :
    ∀ᵐ ω ∂P, Tendsto (fun j => E j ω) atTop (𝓝 0) := by
  set s : ℕ → Set Ω := fun j => {ω | (1 / 4 : ℝ) ^ j ≤ E j ω ^ 2}
  -- Chebyshev: `P(E_j² ≥ 4^(-j)) ≤ 4^(-j)`
  have hbound : ∀ j, (P (s j)).toReal ≤ (1 / 4 : ℝ) ^ j := by
    intro j
    have hpos : (0 : ℝ) < (1 / 4 : ℝ) ^ j := by positivity
    have hcheb := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg (E j ω))
      (hint j) ((1 / 4 : ℝ) ^ j)
    have h2 : (1 / 16 : ℝ) ^ j = (1 / 4 : ℝ) ^ j * (1 / 4 : ℝ) ^ j := by
      rw [← mul_pow]; norm_num
    have h1 : (1 / 4 : ℝ) ^ j * (P (s j)).toReal ≤ (1 / 4 : ℝ) ^ j * (1 / 4 : ℝ) ^ j := by
      rw [← h2]; exact le_trans hcheb (hsq j)
    exact le_of_mul_le_mul_left h1 hpos
  -- Borel-Cantelli: the events have summable probabilities
  have hsum : (∑' j, P (s j)) ≠ ⊤ := by
    have hle : ∀ j, P (s j) ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ j) := fun j =>
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P _) (pow_nonneg (by norm_num) j)).2 (hbound j)
    have hgeom : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hfin : ∑' j, ENNReal.ofReal ((1 / 4 : ℝ) ^ j) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => pow_nonneg (by norm_num) j) hgeom]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum hle)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  have hsmall : ∀ᶠ j in atTop, ‖E j ω‖ ≤ (1 / 2 : ℝ) ^ j := by
    filter_upwards [hω] with j hj
    have hj' : ¬ ((1 / 4 : ℝ) ^ j ≤ E j ω ^ 2) := hj
    have hlt : E j ω ^ 2 < (1 / 4 : ℝ) ^ j := not_le.1 hj'
    have h4 : (1 / 4 : ℝ) ^ j = (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j := by
      rw [← mul_pow]; norm_num
    have hsq2 : ((1 / 2 : ℝ) ^ j) ^ 2 = (1 / 4 : ℝ) ^ j := by
      rw [h4]; ring
    rw [Real.norm_eq_abs]
    exact (abs_lt_of_sq_lt_sq (by rw [hsq2]; exact hlt) (pow_nonneg (by norm_num) j)).le
  exact squeeze_zero_norm' hsmall
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- **L¹ convergence by the min-trick** (r10 `l:r9-marked`, "First moments and the required `L¹`
convergence"): if `X n → Y` almost surely, the `X n` and `Y` are nonnegative and integrable, and
`E X n = E Y` for all large `n`, then `E|X n - Y| → 0`. -/
theorem tendsto_integral_abs_sub_of_ae_tendsto {P : Measure Ω} {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, Integrable (X n) P) (hY : Integrable Y P)
    (hX0 : ∀ n, 0 ≤ᵐ[P] X n) (hY0 : 0 ≤ᵐ[P] Y)
    (hmean : ∀ᶠ n in atTop, ∫ ω, X n ω ∂P = ∫ ω, Y ω ∂P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => ∫ ω, |X n ω - Y ω| ∂P) atTop (𝓝 0) := by
  have habs : ∀ a b : ℝ, |a - b| = a + b - 2 * min a b := by
    intro a b
    rcases le_total a b with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring
  have hmi : ∀ n, Integrable (fun ω => min (X n ω) (Y ω)) P := fun n =>
    hY.mono' ((hX n).aemeasurable.min hY.aemeasurable).aestronglyMeasurable (by
      filter_upwards [hX0 n, hY0] with ω h1 h2
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min h1 h2)]
      exact min_le_right _ _)
  have hid : ∀ n, ∫ ω, |X n ω - Y ω| ∂P
      = ∫ ω, X n ω ∂P + ∫ ω, Y ω ∂P - 2 * ∫ ω, min (X n ω) (Y ω) ∂P := by
    intro n
    have e1 : (fun ω => |X n ω - Y ω|) = fun ω => (X n ω + Y ω) - 2 * min (X n ω) (Y ω) := by
      funext ω; exact habs _ _
    have hs : Integrable (fun ω => X n ω + Y ω) P := (hX n).add hY
    rw [e1, integral_sub hs ((hmi n).const_mul 2), integral_add (hX n) hY, integral_const_mul]
  have hDCT : Tendsto (fun n => ∫ ω, min (X n ω) (Y ω) ∂P) atTop (𝓝 (∫ ω, Y ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => Y ω)
      (fun n => (hmi n).aestronglyMeasurable) hY ?_ ?_
    · intro n
      filter_upwards [hX0 n, hY0] with ω h1 h2
      show ‖min (X n ω) (Y ω)‖ ≤ Y ω
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min h1 h2)]
      exact min_le_right _ _
    · filter_upwards [hconv] with ω hω
      have h := hω.min (tendsto_const_nhds : Tendsto (fun _ : ℕ => Y ω) atTop (𝓝 (Y ω)))
      rwa [min_self] at h
  have hlim : Tendsto (fun n => ∫ ω, Y ω ∂P + ∫ ω, Y ω ∂P - 2 * ∫ ω, min (X n ω) (Y ω) ∂P) atTop
      (𝓝 (∫ ω, Y ω ∂P + ∫ ω, Y ω ∂P - 2 * ∫ ω, Y ω ∂P)) :=
    (tendsto_const_nhds.add tendsto_const_nhds).sub (hDCT.const_mul 2)
  have hzero : ∫ ω, Y ω ∂P + ∫ ω, Y ω ∂P - 2 * ∫ ω, Y ω ∂P = 0 := by ring
  rw [hzero] at hlim
  refine Tendsto.congr' ?_ hlim
  filter_upwards [hmean] with n hn
  rw [hid n, hn]

end HarmonicBalls

end
