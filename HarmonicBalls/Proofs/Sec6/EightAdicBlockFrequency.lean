import HarmonicBalls.Proofs.Sec6.DyadicVeryGoodPrevalence

/-! # Passing a dyadic block count to inverse powers of eight

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter

/-- A dyadic block count bounds the count on every third index. At most
`2 * K` good indices in the larger block can lie outside that subsequence. -/
theorem every_third_block_count (P : ℕ → Prop) (K : ℕ) :
    ({n : ℕ | n ∈ Icc (3*K+1) (6*K) ∧ P n}.ncard) ≤
      ({n : ℕ | n ∈ Icc (K+1) (2*K) ∧ P (3*n)}.ncard) + 2*K := by
  classical
  let A := (Finset.Icc (K+1) (2*K)).filter fun n => P (3*n)
  let B := (Finset.Icc (3*K+1) (6*K)).filter P
  let T := Finset.Icc (3*K+1) (6*K)
  let S := (Finset.Icc (K+1) (2*K)).image (fun n => 3*n)
  have hS : S ⊆ T := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    change 3 * j ∈ Finset.Icc (3*K+1) (6*K)
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have hA : A.card = (B ∩ S).card := by
    have heq : A.image (fun n => 3*n) = B ∩ S := by
      ext n
      simp only [A, B, S, Finset.mem_image, Finset.mem_filter, Finset.mem_inter,
        Finset.mem_Icc]
      constructor
      · rintro ⟨j, ⟨⟨hj₁, hj₂⟩, hp⟩, rfl⟩
        exact ⟨⟨⟨by omega, by omega⟩, hp⟩, ⟨j, ⟨hj₁, hj₂⟩, rfl⟩⟩
      · rintro ⟨⟨_, hp⟩, j, hj, rfl⟩
        exact ⟨j, ⟨hj, hp⟩, rfl⟩
    rw [← heq, Finset.card_image_iff.mpr]
    intro x _ y _ hxy
    change 3*x = 3*y at hxy
    omega
  have hSsize : S.card = K := by
    dsimp [S]
    rw [Finset.card_image_iff.mpr (by intro x _ y _ hxy; change 3*x = 3*y at hxy; omega), Nat.card_Icc]
    omega
  have hTsize : T.card = 3*K := by
    dsimp [T]
    rw [Nat.card_Icc]
    omega
  have hdiff : (T \ S).card = 2*K := by
    have h := Finset.card_sdiff_add_card_eq_card hS
    omega
  have hsub : B \ S ⊆ T \ S := by
    intro n hn
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp (Finset.mem_sdiff.mp hn).1).1,
      (Finset.mem_sdiff.mp hn).2⟩
  have h := Finset.card_sdiff_add_card_inter B S
  have hbound := Finset.card_le_card hsub
  have hcard : B.card ≤ A.card + 2*K := by omega
  simpa only [A, B, ← Set.ncard_coe_finset, Finset.coe_filter, Finset.mem_Icc, Set.mem_Icc,
    Set.ofPred_mem_eq] using hcard

/-- A high-density dyadic comparable-scale count gives an eight-adic
block count, with three times the dyadic failure fraction. -/
theorem eightAdic_comparable_block_count_of_dyadic
    (μ : Measure ℂ) (β : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (K : ℕ)
    (hcount : (1 - ζ) * ((3*K : ℕ) : ℝ) ≤
      veryGoodComparableScaleCount μ β z N₀ a b C₁m C₁p C₂m C₂p C₃ m (3*K)) :
    (1 - 3*ζ) * (K : ℝ) ≤
      ({n : ℕ | n ∈ Icc (K+1) (2*K) ∧
        IsVeryGoodAnnulus μ β ((8 : ℝ)⁻¹ ^ n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
        AnnulusBallComparison μ (3*n) z m}.ncard : ℝ) := by
  have h := every_third_block_count (fun n =>
    IsVeryGoodAnnulus μ β (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison μ n z m) K
  have h' : (veryGoodComparableScaleCount μ β z N₀ a b C₁m C₁p C₂m C₂p C₃ m (3*K) : ℝ) ≤
      ({n : ℕ | n ∈ Icc (K+1) (2*K) ∧
        IsVeryGoodAnnulus μ β ((8 : ℝ)⁻¹ ^ n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
        AnnulusBallComparison μ (3*n) z m}.ncard : ℝ) + 2*(K : ℝ) := by
    have hc : (({n : ℕ | n ∈ Icc (3*K+1) (6*K) ∧
        IsVeryGoodAnnulus μ β (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
        AnnulusBallComparison μ n z m}.ncard : ℕ) : ℝ) ≤
        (({n : ℕ | n ∈ Icc (K+1) (2*K) ∧
        IsVeryGoodAnnulus μ β (dyadicScale (3*n)) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
        AnnulusBallComparison μ (3*n) z m}.ncard : ℕ) : ℝ) + 2*(K : ℝ) := by
      exact_mod_cast h
    simpa only [veryGoodComparableScaleCount, inverse_eight_pow_eq_dyadicScale,
      show 2 * (3*K) = 6*K by omega] using hc
  push_cast at hcount
  nlinarith

/-- The eight-adic block estimate holds eventually whenever the dyadic
comparable-scale estimate holds eventually. -/
theorem eventually_eightAdic_comparable_block_count_of_dyadic
    (μ : Measure ℂ) (β : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hcount : ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
      veryGoodComparableScaleCount μ β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K) :
    ∀ᶠ K : ℕ in atTop, (1 - 3*ζ) * (K : ℝ) ≤
      ({n : ℕ | n ∈ Icc (K+1) (2*K) ∧
        IsVeryGoodAnnulus μ β ((8 : ℝ)⁻¹ ^ n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
        AnnulusBallComparison μ (3*n) z m}.ncard : ℝ) := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hcount
  filter_upwards [eventually_ge_atTop K₀] with K hK
  exact eightAdic_comparable_block_count_of_dyadic μ β z N₀
    a b C₁m C₁p C₂m C₂p C₃ m ζ K (hK₀ (3*K) (by omega))

end HarmonicBalls.Section6
