import HarmonicBalls.Defs.LBM

/-!
# Weighted primitives of uniformly Cauchy primitives

Let `f k ≥ 0` be continuous on `ℝ`, with primitives `F_k(t) = ∫_0^t f_k` that are uniformly Cauchy
on `[0, T]` and bounded at `T`, and let `g` be continuous on `[0, T]`. Then the weighted primitives
`G_k(t) = ∫_0^t g f_k` are uniformly Cauchy on `[0, T]`.

Proof. For a partition `0 = a_0 ≤ … ≤ a_m = t` with `a_i = min t (i T / m)` and `g` oscillating by
less than `η` on pieces of length `T / m`, `G_k(t)` differs from the Riemann–Stieltjes sum
`∑ g(a_i) (F_k(a_{i+1}) - F_k(a_i))` by at most `η F_k(T)`, and two such sums for `j` and `k`
differ by at most `2 m sup |g| sup_{[0,T]} |F_j - F_k|`.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- **Weighted primitives of uniformly Cauchy primitives are uniformly Cauchy.** -/
theorem weightedPrimitive_uniformCauchy {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 T)) {f : ℕ → ℝ → ℝ} (hf : ∀ k, Continuous (f k))
    (hf0 : ∀ k s, 0 ≤ f k s)
    (hF : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k → ∀ t ∈ Icc (0 : ℝ) T,
      |(∫ s in (0 : ℝ)..t, f j s) - ∫ s in (0 : ℝ)..t, f k s| ≤ ε)
    (hB : ∃ B : ℝ, ∀ k, (∫ s in (0 : ℝ)..T, f k s) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k → ∀ t ∈ Icc (0 : ℝ) T,
      |(∫ s in (0 : ℝ)..t, g s * f j s) - ∫ s in (0 : ℝ)..t, g s * f k s| ≤ ε := by
  intro ε hε
  obtain ⟨B, hBk⟩ := hB
  have hB0 : 0 ≤ B := (intervalIntegral.integral_nonneg hT fun s _ => hf0 0 s).trans (hBk 0)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hg
  set η : ℝ := ε / (4 * (B + 1)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.1 huc η hηpos
  obtain ⟨m, hm⟩ := exists_nat_gt (T / δ)
  have hm0 : 0 < (m : ℝ) := lt_of_le_of_lt (div_nonneg hT hδ.le) hm
  have hmesh : T / m < δ := by
    rw [div_lt_iff₀ hm0]
    rw [div_lt_iff₀ hδ] at hm
    linarith
  set ε' : ℝ := ε / (4 * ((m : ℝ) + 1) * (M + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨N, hN⟩ := hF ε' hε'pos
  refine ⟨N, fun j hj k hk t ht => ?_⟩
  set c : ℕ → ℝ := fun i => i * T / m with hc
  set a : ℕ → ℝ := fun i => min t (c i) with ha
  have ha0 : a 0 = 0 := by simp [ha, hc, ht.1]
  have ham : a m = t := by
    simp only [ha, hc]
    rw [mul_div_cancel_left₀ _ hm0.ne']
    exact min_eq_left ht.2
  have hc_mono : Monotone c := fun i i' hii' => by
    simp only [hc]
    gcongr
  have ha_mono : ∀ i, a i ≤ a (i + 1) := fun i => min_le_min le_rfl (hc_mono (Nat.le_succ i))
  have ha_mem : ∀ i, a i ∈ Icc (0 : ℝ) T := fun i =>
    ⟨le_min ht.1 (by simp only [hc]; positivity), (min_le_left _ _).trans ht.2⟩
  have ha_step : ∀ i, a (i + 1) - a i ≤ T / m := by
    intro i
    have h1 := abs_min_sub_min_le_max t (c (i + 1)) t (c i)
    simp only [sub_self, abs_zero] at h1
    have h2 : c (i + 1) - c i = T / m := by simp only [hc]; push_cast; ring
    have h3 : |c (i + 1) - c i| = T / m := by rw [h2, abs_of_nonneg (div_nonneg hT hm0.le)]
    have h4 := le_abs_self (a (i + 1) - a i)
    rw [max_eq_right (abs_nonneg _), h3] at h1
    exact h4.trans h1
  have hint : ∀ (q : ℕ → ℝ → ℝ), (∀ k, Continuous (q k)) → ∀ k (u v : ℝ),
      IntervalIntegrable (q k) volume u v := fun q hq k u v => (hq k).intervalIntegrable u v
  have hgf : ∀ k, ContinuousOn (fun s => g s * f k s) (Icc 0 T) :=
    fun k => hg.mul (hf k).continuousOn
  -- the piece estimate
  have hpiece : ∀ k i, |(∫ s in (a i)..(a (i + 1)), g s * f k s) -
      g (a i) * ∫ s in (a i)..(a (i + 1)), f k s| ≤ η * ∫ s in (a i)..(a (i + 1)), f k s := by
    intro k i
    have hsub : Icc (a i) (a (i + 1)) ⊆ Icc 0 T :=
      Icc_subset_Icc (ha_mem i).1 (ha_mem (i + 1)).2
    have hi1 : IntervalIntegrable (fun s => g s * f k s) volume (a i) (a (i + 1)) :=
      ((hgf k).mono hsub).intervalIntegrable_of_Icc (ha_mono i)
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hi1
      ((hint f hf k _ _).const_mul _)]
    refine (intervalIntegral.abs_integral_le_integral_abs (ha_mono i)).trans ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (ha_mono i) ?_ ((hint f hf k _ _).const_mul _) ?_
    · exact ((hi1.sub ((hint f hf k _ _).const_mul _)).abs)
    · intro s hs
      rw [← sub_mul, abs_mul, abs_of_nonneg (hf0 k s)]
      refine mul_le_mul_of_nonneg_right ?_ (hf0 k s)
      have hd : dist s (a i) < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs.1)]
        linarith [hs.2, ha_step i]
      have := hδg s (hsub hs) (a i) (ha_mem i) hd
      rw [Real.dist_eq] at this
      exact this.le
  -- the Riemann-Stieltjes sums
  set S : ℕ → ℝ := fun k => ∑ i ∈ Finset.range m,
    g (a i) * ((∫ s in (0 : ℝ)..(a (i + 1)), f k s) - ∫ s in (0 : ℝ)..(a i), f k s) with hS
  have hsplit : ∀ (q : ℝ → ℝ), (∀ u v : ℝ, IntervalIntegrable q volume u v) →
      (∫ s in (0 : ℝ)..t, q s) = ∑ i ∈ Finset.range m, ∫ s in (a i)..(a (i + 1)), q s := by
    intro q hq
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun i _ => hq _ _), ha0, ham]
  have hdiff : ∀ k i, (∫ s in (0 : ℝ)..(a (i + 1)), f k s) - ∫ s in (0 : ℝ)..(a i), f k s =
      ∫ s in (a i)..(a (i + 1)), f k s := fun k i =>
    intervalIntegral.integral_interval_sub_left (hint f hf k _ _) (hint f hf k _ _)
  have hGS : ∀ k, |(∫ s in (0 : ℝ)..t, g s * f k s) - S k| ≤ η * B := by
    intro k
    have hgfi : ∀ u v : ℝ, u ∈ Icc (0 : ℝ) T → v ∈ Icc (0 : ℝ) T →
        IntervalIntegrable (fun s => g s * f k s) volume u v := fun u v hu hv =>
      ((hgf k).mono (uIcc_subset_Icc hu hv)).intervalIntegrable
    have hsum : (∫ s in (0 : ℝ)..t, g s * f k s) =
        ∑ i ∈ Finset.range m, ∫ s in (a i)..(a (i + 1)), g s * f k s := by
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun i _ => hgfi _ _ (ha_mem i) (ha_mem (i + 1))), ha0, ham]
    rw [hsum, hS, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range m, |(∫ s in (a i)..(a (i + 1)), g s * f k s) -
          g (a i) * ((∫ s in (0 : ℝ)..(a (i + 1)), f k s) - ∫ s in (0 : ℝ)..(a i), f k s)|
        ≤ ∑ i ∈ Finset.range m, η * ∫ s in (a i)..(a (i + 1)), f k s := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [hdiff k i]
          exact hpiece k i
      _ = η * ∫ s in (0 : ℝ)..t, f k s := by
          rw [← Finset.mul_sum, hsplit (f k) (hint f hf k)]
      _ ≤ η * B := by
          refine mul_le_mul_of_nonneg_left ?_ hηpos.le
          refine le_trans ?_ (hBk k)
          exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
            (Eventually.of_forall fun s => hf0 k s) (hint f hf k _ _)
  have hSS : |S j - S k| ≤ 2 * m * M * ε' := by
    rw [hS, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range m,
          |g (a i) * ((∫ s in (0 : ℝ)..(a (i + 1)), f j s) - ∫ s in (0 : ℝ)..(a i), f j s) -
            g (a i) * ((∫ s in (0 : ℝ)..(a (i + 1)), f k s) - ∫ s in (0 : ℝ)..(a i), f k s)|
        ≤ ∑ _i ∈ Finset.range m, M * (2 * ε') := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← mul_sub, abs_mul]
          refine mul_le_mul (hM _ (ha_mem i)) ?_ (abs_nonneg _) hM0
          have h1 := hN j hj k hk (a (i + 1)) (ha_mem (i + 1))
          have h2 := hN j hj k hk (a i) (ha_mem i)
          rw [show (∫ s in (0 : ℝ)..(a (i + 1)), f j s) - (∫ s in (0 : ℝ)..(a i), f j s) -
              ((∫ s in (0 : ℝ)..(a (i + 1)), f k s) - ∫ s in (0 : ℝ)..(a i), f k s) =
              ((∫ s in (0 : ℝ)..(a (i + 1)), f j s) - ∫ s in (0 : ℝ)..(a (i + 1)), f k s) -
              ((∫ s in (0 : ℝ)..(a i), f j s) - ∫ s in (0 : ℝ)..(a i), f k s) by ring]
          refine (abs_sub _ _).trans ?_
          linarith
      _ = 2 * m * M * ε' := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hfin : 2 * η * B + 2 * m * M * ε' ≤ ε := by
    have h1 : 2 * η * B ≤ ε / 2 := by
      rw [hη]
      have : B / (B + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
      calc 2 * (ε / (4 * (B + 1))) * B = ε / 2 * (B / (B + 1)) := by field_simp; ring
        _ ≤ ε / 2 * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have h2 : 2 * m * M * ε' ≤ ε / 2 := by
      rw [hε']
      have hmM : (m : ℝ) * M / (((m : ℝ) + 1) * (M + 1)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      calc 2 * m * M * (ε / (4 * ((m : ℝ) + 1) * (M + 1)))
          = ε / 2 * ((m : ℝ) * M / (((m : ℝ) + 1) * (M + 1))) := by field_simp; ring
        _ ≤ ε / 2 * 1 := by gcongr
        _ = ε / 2 := mul_one _
    linarith
  calc |(∫ s in (0 : ℝ)..t, g s * f j s) - ∫ s in (0 : ℝ)..t, g s * f k s|
      = |((∫ s in (0 : ℝ)..t, g s * f j s) - S j) - ((∫ s in (0 : ℝ)..t, g s * f k s) - S k) +
          (S j - S k)| := by ring_nf
    _ ≤ |(∫ s in (0 : ℝ)..t, g s * f j s) - S j| + |(∫ s in (0 : ℝ)..t, g s * f k s) - S k| +
          |S j - S k| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ η * B + η * B + 2 * m * M * ε' := by gcongr <;> first | exact hGS j | exact hGS k
    _ = 2 * η * B + 2 * m * M * ε' := by ring
    _ ≤ ε := hfin

end HarmonicBalls
