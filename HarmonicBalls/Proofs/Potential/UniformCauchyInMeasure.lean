import HarmonicBalls.Defs.LBM

/-!
# Limits of sequences that are Cauchy in measure uniformly on bounded time sets

Let `A k : X → ℝ≥0 → ℝ` be a sequence of time-indexed functionals on a measure space `(X, Q)`.
Suppose it is Cauchy in measure uniformly on bounded time sets: for every `T`, `η > 0` and
`θ > 0` there is `N` with `Q {b | ∃ t ≤ T, η ≤ |A j b t - A k b t|} ≤ θ` for `j, k ≥ N`. Then
there is a limit `F` with `Q {b | ∃ t ≤ T, η ≤ |A k b t - F b t|} → 0` for every `T` and `η > 0`.
This is the form of convergence of the LQG clock (`IsLQGClock`).

The proof chooses indices `n m` such that the sets
`S m = {b | ∃ t ≤ m, 2^{-m} ≤ |A (n (m+1)) b t - A (n m) b t|}` have measure at most `2^{-m}`.
Off `⋃_{i ≥ m} S i` the sequence `A (n i) b t` is Cauchy at every `t ≤ m`, with tail bound
`2 · 2^{-m}`, and the limit `F b t` is its pointwise limit. No measurability is used: all sets are
measured by the outer measure `Q`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-- **Limits of sequences Cauchy in measure uniformly on bounded time sets.** -/
theorem exists_tendsto_of_uniformCauchyInMeasure {X : Type*} [MeasurableSpace X] (Q : Measure X)
    (A : ℕ → X → ℝ≥0 → ℝ)
    (h : ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ θ : ℝ, 0 < θ → ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k →
      Q {b | ∃ t ≤ T, η ≤ |A j b t - A k b t|} ≤ ENNReal.ofReal θ) :
    ∃ F : X → ℝ≥0 → ℝ, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      Tendsto (fun k => Q {b | ∃ t ≤ T, η ≤ |A k b t - F b t|}) atTop (𝓝 0) := by
  choose N hN using h
  set e : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ m with he_def
  have he : ∀ m, 0 < e m := fun m => by positivity
  have he_add : ∀ m i, e (m + i) = e m * (1 / 2) ^ i := fun m i => by simp only [he_def]; ring
  set N' : ℕ → ℕ := fun m => N (m : ℝ≥0) (e m) (he m) (e m) (he m) with hN'
  set n : ℕ → ℕ := fun m => (Finset.range (m + 1)).sup N' + m with hn_def
  have hn_ge : ∀ i m, i ≤ m → N' i ≤ n m := fun i m him =>
    le_trans (Finset.le_sup (f := N') (Finset.mem_range.2 (Nat.lt_succ_of_le him)))
      (Nat.le_add_right _ _)
  have hn_self : ∀ m, m ≤ n m := fun m => Nat.le_add_left _ _
  set S : ℕ → Set X := fun m =>
    {b | ∃ t ≤ (m : ℝ≥0), e m ≤ |A (n (m + 1)) b t - A (n m) b t|} with hS_def
  have hS : ∀ m, Q (S m) ≤ ENNReal.ofReal (e m) := fun m =>
    hN _ _ _ _ _ (n (m + 1)) (hn_ge m (m + 1) (Nat.le_succ m)) (n m) (hn_ge m m le_rfl)
  -- off the tail union, the subsequence is Cauchy with a geometric tail bound
  have htail : ∀ (m : ℕ) (b : X) (t : ℝ≥0), t ≤ (m : ℝ≥0) → b ∉ ⋃ i, S (m + i) →
      ∃ L : ℝ, Tendsto (fun i => A (n i) b t) atTop (𝓝 L) ∧ |A (n m) b t - L| ≤ 2 * e m := by
    intro m b t ht hb
    simp only [Set.mem_iUnion, not_exists] at hb
    have hstep : ∀ i, dist (A (n (m + i)) b t) (A (n (m + i + 1)) b t) ≤ e m * (1 / 2) ^ i := by
      intro i
      have hbi := hb i
      simp only [hS_def, Set.mem_ofPred_eq, not_exists, not_and, not_le] at hbi
      have hti : t ≤ ((m + i : ℕ) : ℝ≥0) := ht.trans (by exact_mod_cast Nat.le_add_right m i)
      have := hbi t hti
      rw [dist_comm, Real.dist_eq, ← he_add]
      exact this.le
    have hcs : CauchySeq fun i => A (n (m + i)) b t :=
      cauchySeq_of_le_geometric (1 / 2) (e m) (by norm_num) hstep
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
    refine ⟨L, (tendsto_add_atTop_iff_nat m).1 (hL.congr fun i => by rw [add_comm]), ?_⟩
    have hd := dist_le_of_le_geometric_of_tendsto (1 / 2) (e m) (by norm_num) hstep hL 0
    rw [Real.dist_eq] at hd
    have hd' : |A (n m) b t - L| ≤ e m / (1 - 1 / 2) := by simpa using hd
    refine hd'.trans_eq ?_
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, div_inv_eq_mul, mul_comm]
  refine ⟨fun b t => limUnder atTop (fun i => A (n i) b t), fun T η hη => ?_⟩
  have hlim : ∀ (m : ℕ) (b : X) (t : ℝ≥0), t ≤ (m : ℝ≥0) → b ∉ ⋃ i, S (m + i) →
      |A (n m) b t - limUnder atTop (fun i => A (n i) b t)| ≤ 2 * e m := by
    intro m b t ht hb
    obtain ⟨L, hL, hbd⟩ := htail m b t ht hb
    rwa [hL.limUnder_eq]
  -- measure of the tail union
  have hpow : ∀ i : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ i) = (2⁻¹ : ℝ≥0∞) ^ i := fun i => by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos,
      ENNReal.ofReal_ofNat]
  have hunion : ∀ m : ℕ, Q (⋃ i, S (m + i)) ≤ ENNReal.ofReal (2 * e m) := by
    intro m
    calc Q (⋃ i, S (m + i)) ≤ ∑' i, Q (S (m + i)) := measure_iUnion_le _
      _ ≤ ∑' i, ENNReal.ofReal (e m) * (2⁻¹ : ℝ≥0∞) ^ i := by
          refine ENNReal.tsum_le_tsum fun i => (hS (m + i)).trans_eq ?_
          rw [he_add, ENNReal.ofReal_mul (he m).le, hpow i]
      _ = ENNReal.ofReal (2 * e m) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
            ENNReal.ofReal_mul (by norm_num), mul_comm]
          simp
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  obtain ⟨δ, hδ0, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
  have hδ : (0 : ℝ) < δ := by exact_mod_cast hδ0
  set θ : ℝ := (δ : ℝ) / 2 with hθ
  have hθ0 : 0 < θ := by positivity
  set K : ℕ := N T (η / 2) (by positivity) θ hθ0 with hK
  -- choose `m` with `T ≤ m`, `2 e m < η / 2`, `2 e m ≤ θ` and `K ≤ n m`
  have hev : ∀ᶠ m : ℕ in atTop, 2 * e m < η / 2 ∧ 2 * e m ≤ θ := by
    have h0 : Tendsto (fun m => 2 * e m) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
      rw [mul_zero] at h
      exact h
    exact (h0.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 2))).and
      (h0.eventually (ge_mem_nhds hθ0))
  obtain ⟨m, hm⟩ := (hev.and ((eventually_ge_atTop (⌈(T : ℝ)⌉₊)).and
    (eventually_ge_atTop K))).exists
  obtain ⟨⟨hm1, hm2⟩, hmT, hmK⟩ := hm
  have hTm : T ≤ (m : ℝ≥0) := by
    have : (T : ℝ) ≤ m := (Nat.le_ceil _).trans (by exact_mod_cast hmT)
    exact_mod_cast this
  refine ⟨K, fun k hk => ?_⟩
  have hsub : {b | ∃ t ≤ T, η ≤ |A k b t - limUnder atTop (fun i => A (n i) b t)|} ⊆
      {b | ∃ t ≤ T, η / 2 ≤ |A k b t - A (n m) b t|} ∪ ⋃ i, S (m + i) := by
    intro b hb
    by_cases hbS : b ∈ ⋃ i, S (m + i)
    · exact Or.inr hbS
    · left
      obtain ⟨t, htT, hηt⟩ := hb
      refine ⟨t, htT, ?_⟩
      have hb2 := hlim m b t (htT.trans hTm) hbS
      have htri : |A k b t - limUnder atTop (fun i => A (n i) b t)| ≤
          |A k b t - A (n m) b t| + |A (n m) b t - limUnder atTop (fun i => A (n i) b t)| :=
        abs_sub_le _ _ _
      linarith
  calc Q {b | ∃ t ≤ T, η ≤ |A k b t - limUnder atTop (fun i => A (n i) b t)|}
      ≤ Q ({b | ∃ t ≤ T, η / 2 ≤ |A k b t - A (n m) b t|} ∪ ⋃ i, S (m + i)) := measure_mono hsub
    _ ≤ Q {b | ∃ t ≤ T, η / 2 ≤ |A k b t - A (n m) b t|} + Q (⋃ i, S (m + i)) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal θ + ENNReal.ofReal θ := by
        refine add_le_add (hN T (η / 2) (by positivity) θ hθ0 k hk (n m) (hmK.trans (hn_self m))) ?_
        exact (hunion m).trans (ENNReal.ofReal_le_ofReal hm2)
    _ = (δ : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_add hθ0.le hθ0.le, hθ, add_halves, ENNReal.ofReal_coe_nnreal]
    _ ≤ ε := hδε.le

end HarmonicBalls
