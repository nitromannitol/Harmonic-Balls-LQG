import HarmonicBalls.Proofs.Potential.BrownianShiftedDyadicPairCount
import HarmonicBalls.Proofs.Sec6.BrownianScaling

/-! # Brownian pair counts on finite horizons

The shifted dyadic close-pair bound holds simultaneously on all finite horizons.
-/

open MeasureTheory Set
open scoped NNReal
open HarmonicBalls.Section6

namespace HarmonicBalls

/-- Indices of shifted dyadic times in a finite interval. -/
noncomputable def shiftedDyadicIndicesUntil (T s : ℝ) (k : ℕ) : Finset ℤ :=
  Finset.Icc ⌈(-s) / (1 / 4 : ℝ) ^ k⌉ ⌊(T - s) / (1 / 4 : ℝ) ^ k⌋

/-- Membership means that the corresponding physical grid time lies in the interval. -/
theorem mem_shiftedDyadicIndicesUntil (T s : ℝ) (k : ℕ) (i : ℤ) :
    i ∈ shiftedDyadicIndicesUntil T s k ↔
      s + (1 / 4 : ℝ) ^ k * (i : ℝ) ∈ Icc (0 : ℝ) T := by
  have hδ : 0 < (1 / 4 : ℝ) ^ k := by positivity
  simp only [shiftedDyadicIndicesUntil, Finset.mem_Icc, Int.ceil_le, Int.le_floor, mem_Icc]
  rw [div_le_iff₀ hδ, le_div_iff₀ hδ]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

/-- A close-pair count is monotone in the sample set. -/
theorem sampledClosePairCount_mono {ι : Type*} [DecidableEq ι]
    (b : ℝ → ℂ) (S U : Finset ι) (t : ι → ℝ) (r : ℝ) (h : S ⊆ U) :
    sampledClosePairCount b S t r ≤ sampledClosePairCount b U t r := by
  classical
  rw [sampledClosePairCount_eq_card, sampledClosePairCount_eq_card]
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.product_subset_product h h)

/-- Every nonnegative finite horizon admits the original shifted-grid pair bound. -/
theorem planarBrownianMotion_shifted_dyadic_close_pairs_all_horizons (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ,
        (sampledClosePairCount (fun t => b (Real.toNNReal t))
          (shiftedDyadicIndicesUntil T s k)
          (fun i => s + (1 / 4 : ℝ) ^ k * (i : ℝ)) ((1 / 2 : ℝ) ^ k) : ℝ) ≤
            C * (4 : ℝ) ^ k * (k : ℝ) ^ 3 := by
  have ha : ∀ n : ℕ, ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ,
        (sampledClosePairCount
          (fun t => scaledCenteredPlanarPath x ((4 : ℝ≥0) ^ n) b (Real.toNNReal t))
          (shiftedDyadicIndices s k)
          (fun i => s + (1 / 4 : ℝ) ^ k * (i : ℝ)) ((1 / 2 : ℝ) ^ k) : ℝ) ≤
            C * (4 : ℝ) ^ k * (k : ℝ) ^ 3 := by
    intro n
    have hm := planarBrownianMotion_shifted_dyadic_close_pairs 0
    rw [← planarBrownianMotion_map_scaledCenteredPlanarPath x (c := (4 : ℝ≥0) ^ n)
      (by positivity)] at hm
    exact ae_of_ae_map (continuous_scaledCenteredPlanarPath x _).measurable.aemeasurable hm
  filter_upwards [ae_all_iff.mpr ha] with b hb T hT
  obtain ⟨n, hn⟩ := exists_nat_gt T
  have hn4 : T ≤ (4 : ℝ) ^ n := by
    have hpow : ∀ m : ℕ, (m : ℝ) ≤ (4 : ℝ) ^ m := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
        rw [pow_succ, Nat.cast_succ]
        have hp : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
        nlinarith
    linarith [hpow n]
  obtain ⟨C, hC, hbound⟩ := hb n
  refine ⟨C * 4 ^ n * (n + 1 : ℝ) ^ 3, by positivity, ?_⟩
  intro k hk s
  let S := shiftedDyadicIndicesUntil T s k
  let s' := s / (4 : ℝ) ^ n
  let t : ℤ → ℝ := fun i => s + (1 / 4 : ℝ) ^ k * (i : ℝ)
  let t' : ℤ → ℝ := fun i => s' + (1 / 4 : ℝ) ^ (k + n) * (i : ℝ)
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hp4 : (1 / 4 : ℝ) ^ (k + n) = (1 / 4 : ℝ) ^ k / 4 ^ n := by
    simp only [pow_add, div_eq_mul_inv, one_mul, inv_pow]
  have hp2 : (1 / 2 : ℝ) ^ (k + n) = (1 / 2 : ℝ) ^ k / 2 ^ n := by
    simp only [pow_add, div_eq_mul_inv, one_mul, inv_pow]
  have htime : ∀ i, t' i = t i / 4 ^ n := by
    intro i; dsimp [t', t, s']; rw [hp4]; ring
  have hsub : S ⊆ shiftedDyadicIndices s' (k + n) := by
    intro i hi
    have hi := (mem_shiftedDyadicIndicesUntil T s k i).mp hi
    apply (mem_shiftedDyadicIndices s' (k + n) i).mpr
    change t' i ∈ Icc (0 : ℝ) 1
    rw [htime]
    exact ⟨div_nonneg hi.1 h4.le, (div_le_one h4).2 (hi.2.trans hn4)⟩
  have hsqrt : Real.sqrt ((4 : ℝ) ^ n) = (2 : ℝ) ^ n := by
    rw [show (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 by
      calc
        (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by norm_num
        _ = ((2 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
    exact Real.sqrt_sq (by positivity)
  have hpath : ∀ i, scaledCenteredPlanarPath x ((4 : ℝ≥0) ^ n) b (Real.toNNReal (t' i)) =
      ((2 : ℝ) ^ n)⁻¹ • (b (Real.toNNReal (t i)) - x) := by
    intro i
    rw [htime]
    simp only [scaledCenteredPlanarPath, ContinuousMap.coe_mk, NNReal.coe_pow, NNReal.coe_ofNat, hsqrt]
    have ht : (4 : ℝ≥0) ^ n * Real.toNNReal (t i / 4 ^ n) = Real.toNNReal (t i) := by
      have hf : Real.toNNReal ((4 : ℝ) ^ n) = (4 : ℝ≥0) ^ n := by
        simpa only [NNReal.coe_pow, NNReal.coe_ofNat] using
          (show Real.toNNReal (((4 : ℝ≥0) ^ n : ℝ≥0) : ℝ) = (4 : ℝ≥0) ^ n from Real.toNNReal_coe)
      rw [← hf, ← Real.toNNReal_mul h4.le]
      congr 1
      field_simp
    rw [ht]
  have hdist : ∀ i j, ‖scaledCenteredPlanarPath x ((4 : ℝ≥0) ^ n) b
      (Real.toNNReal (t' j)) - scaledCenteredPlanarPath x ((4 : ℝ≥0) ^ n) b
      (Real.toNNReal (t' i))‖ = ‖b (Real.toNNReal (t j)) - b (Real.toNNReal (t i))‖ / 2 ^ n := by
    intro i j
    rw [hpath, hpath, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h2)]
    rw [show b (Real.toNNReal (t j)) - x - (b (Real.toNNReal (t i)) - x) =
      b (Real.toNNReal (t j)) - b (Real.toNNReal (t i)) by abel]
    ring
  have hcount : sampledClosePairCount (fun u => b (Real.toNNReal u)) S t ((1 / 2 : ℝ) ^ k) =
      sampledClosePairCount (fun u => scaledCenteredPlanarPath x ((4 : ℝ≥0) ^ n) b
        (Real.toNNReal u)) S t' ((1 / 2 : ℝ) ^ (k + n)) := by
    rw [sampledClosePairCount_eq_card, sampledClosePairCount_eq_card]
    congr 1
    apply Finset.filter_congr
    intro p _
    rw [hdist, hp2, div_le_div_iff_of_pos_right h2]
  have hm := sampledClosePairCount_mono
    (fun u => scaledCenteredPlanarPath x ((4 : ℝ≥0) ^ n) b (Real.toNNReal u))
    S (shiftedDyadicIndices s' (k + n)) t' ((1 / 2 : ℝ) ^ (k + n)) hsub
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkn : (k + n : ℝ) ≤ (n + 1 : ℝ) * k := by nlinarith
  calc
    _ = (sampledClosePairCount (fun u => scaledCenteredPlanarPath x ((4 : ℝ≥0) ^ n) b
        (Real.toNNReal u)) S t' ((1 / 2 : ℝ) ^ (k + n)) : ℝ) := by exact_mod_cast hcount
    _ ≤ _ := by exact_mod_cast hm
    _ ≤ C * (4 : ℝ) ^ (k + n) * ((k + n : ℕ) : ℝ) ^ 3 := hbound _ (by omega) s'
    _ ≤ C * 4 ^ n * (n + 1 : ℝ) ^ 3 * 4 ^ k * (k : ℝ) ^ 3 := by
      rw [pow_add, Nat.cast_add]
      have hp : ((k : ℝ) + n) ^ 3 ≤ ((n + 1 : ℝ) * k) ^ 3 := by gcongr
      nlinarith [mul_nonneg (mul_nonneg hC.le (show 0 ≤ (4 : ℝ) ^ k by positivity))
        (show 0 ≤ (4 : ℝ) ^ n by positivity) |>.trans (le_refl _)]

end HarmonicBalls
