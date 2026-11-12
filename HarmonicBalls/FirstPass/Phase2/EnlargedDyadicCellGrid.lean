import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Clipped enlarged dyadic cells are grid rectangles

Let `S₂ = closedDyadicSquare n₀ j₂ k₂ = [j₂ 2^{-n₀}, (j₂ + 1) 2^{-n₀}] × [k₂ 2^{-n₀}, (k₂ + 1) 2^{-n₀}]` and let
`closedDyadicSquare N j k ⊆ S₂` be a dyadic cell of level `N` (so `n₀ ≤ N`). The enlargement
`Ŝ = enlargedDyadicCell N j k` (same centre, side `2^{-N} + 2^{-N-2}`) is the closed square
`[(8j - 1) u, (8j + 9) u] × [(8k - 1) u, (8k + 9) u]` with `u = 2^{-N-3}`, and `Ŝ ∩ S₂` is a closed rectangle on the
grid of mesh `u = 2^{-n₀} / 2^m`, `m = N + 3 - n₀`, made of at most `10 × 10` closed dyadic subsquares of `S₂` of
level `m` (proof of Lemma 11.10, paper lines 3010-3016: the clipped cells are tiled by boundedly many small squares).
-/

open Set

namespace HarmonicBalls

/-- The intersection of two products `s ×ℂ t` is the product of the intersections. -/
theorem reProdIm_inter_reProdIm (s₁ t₁ s₂ t₂ : Set ℝ) :
    (s₁ ×ℂ t₁) ∩ (s₂ ×ℂ t₂) = (s₁ ∩ s₂) ×ℂ (t₁ ∩ t₂) := by
  ext z
  simp only [mem_inter_iff, Complex.mem_reProdIm]
  tauto

/-- One-dimensional clipping on a grid of mesh `u > 0`: if `a = c u`, `c ≤ lo + 1` and `lo + 9 ≤ c + T`, then
`[lo u, (lo + 10) u] ∩ [a, a + T u] = [a + i₀ u, a + (i₀ + K + 1) u]` with `K ≤ 9` and `i₀ + K < T`. -/
theorem Icc_inter_Icc_eq_grid {u a : ℝ} (hu : 0 < u) {lo c : ℤ} {T : ℕ} (ha : a = c * u) (hc : c ≤ lo + 1)
    (hT : lo + 9 ≤ c + T) :
    ∃ i₀ K : ℕ, K ≤ 9 ∧ i₀ + K < T ∧
      Icc ((lo : ℝ) * u) (((lo : ℝ) + 10) * u) ∩ Icc a (a + (T : ℝ) * u) =
        Icc (a + (i₀ : ℝ) * u) (a + ((i₀ : ℝ) + K + 1) * u) := by
  have h0 : (0 : ℤ) ≤ max lo c - c := by omega
  have h1 : (0 : ℤ) ≤ min (lo + 10) (c + T) - max lo c - 1 := by omega
  refine ⟨(max lo c - c).toNat, (min (lo + 10) (c + T) - max lo c - 1).toNat, by omega, by omega, ?_⟩
  have hi : (((max lo c - c).toNat : ℕ) : ℝ) = ((max lo c - c : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  have hK : (((min (lo + 10) (c + T) - max lo c - 1).toNat : ℕ) : ℝ) =
      ((min (lo + 10) (c + T) - max lo c - 1 : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
  rw [Icc_inter_Icc, hi, hK]
  subst ha
  push_cast
  congr 1
  · rw [← max_mul_of_nonneg _ _ hu.le]
    ring
  · have e : (c : ℝ) * u + (T : ℝ) * u = ((c : ℝ) + T) * u := by ring
    rw [e, ← min_mul_of_nonneg _ _ hu.le]
    ring

/-- The enlarged dyadic cell `enlargedDyadicCell N j k` is the closed square
`[(8j - 1) u, (8j + 9) u] × [(8k - 1) u, (8k + 9) u]`, `u = 2^{-N-3}`. -/
theorem enlargedDyadicCell_eq_reProdIm (N j k : ℤ) :
    enlargedDyadicCell N j k =
      Icc (((8 * j - 1 : ℤ) : ℝ) * (2 : ℝ) ^ (-N - 3)) ((((8 * j - 1 : ℤ) : ℝ) + 10) * (2 : ℝ) ^ (-N - 3)) ×ℂ
        Icc (((8 * k - 1 : ℤ) : ℝ) * (2 : ℝ) ^ (-N - 3)) ((((8 * k - 1 : ℤ) : ℝ) + 10) * (2 : ℝ) ^ (-N - 3)) := by
  have h8 : (2 : ℝ) ^ (-N) = 8 * (2 : ℝ) ^ (-N - 3) := by
    have e : (2 : ℝ) ^ (-N) = (2 : ℝ) ^ ((3 : ℤ) + (-N - 3)) := by congr 1; ring
    rw [e, zpow_add₀ two_ne_zero]
    norm_num
  have h2 : (2 : ℝ) ^ (-N - 2) = 2 * (2 : ℝ) ^ (-N - 3) := by
    have e : (2 : ℝ) ^ (-N - 2) = (2 : ℝ) ^ ((1 : ℤ) + (-N - 3)) := by congr 1; ring
    rw [e, zpow_add₀ two_ne_zero]
    norm_num
  ext z
  simp only [enlargedDyadicCell, Set.mem_ofPred_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le, h8, h2]
  push_cast
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **Clipped enlarged dyadic cells are grid rectangles.** If the dyadic cell `closedDyadicSquare N j k` lies in
`S₂ = closedDyadicSquare n₀ j₂ k₂`, then `enlargedDyadicCell N j k ∩ S₂` is the closed rectangle
`[a + i₀ h, a + (i₀ + K + 1) h] × [b + j₀ h, b + (j₀ + L + 1) h]` on the grid of mesh `h = 2^{-n₀} / 2^m` of
`S₂ = [a, a + 2^{-n₀}] × [b, b + 2^{-n₀}]`, `m = N + 3 - n₀`, with `K, L ≤ 9` and `i₀ + K, j₀ + L < 2^m`: a union of at
most `10 × 10` closed dyadic subsquares of `S₂` of level `m`. -/
theorem enlargedDyadicCell_inter_closedDyadicSquare_eq_gridRectangle {n₀ j₂ k₂ j k : ℤ} {N : ℕ}
    (hsub : closedDyadicSquare (N : ℤ) j k ⊆ closedDyadicSquare n₀ j₂ k₂) :
    ∃ i₀ j₀ K L : ℕ, K ≤ 9 ∧ L ≤ 9 ∧ i₀ + K < 2 ^ ((N : ℤ) + 3 - n₀).toNat ∧
      j₀ + L < 2 ^ ((N : ℤ) + 3 - n₀).toNat ∧
      enlargedDyadicCell (N : ℤ) j k ∩ closedDyadicSquare n₀ j₂ k₂ =
        Icc ((j₂ : ℝ) * 2 ^ (-n₀) + (i₀ : ℝ) * (2 ^ (-n₀) / 2 ^ ((N : ℤ) + 3 - n₀).toNat))
            ((j₂ : ℝ) * 2 ^ (-n₀) + ((i₀ : ℝ) + K + 1) * (2 ^ (-n₀) / 2 ^ ((N : ℤ) + 3 - n₀).toNat)) ×ℂ
          Icc ((k₂ : ℝ) * 2 ^ (-n₀) + (j₀ : ℝ) * (2 ^ (-n₀) / 2 ^ ((N : ℤ) + 3 - n₀).toNat))
            ((k₂ : ℝ) * 2 ^ (-n₀) + ((j₀ : ℝ) + L + 1) * (2 ^ (-n₀) / 2 ^ ((N : ℤ) + 3 - n₀).toNat)) := by
  set m := ((N : ℤ) + 3 - n₀).toNat with hm_def
  set u : ℝ := (2 : ℝ) ^ (-(N : ℤ) - 3) with hu_def
  have hu : 0 < u := zpow_pos two_pos _
  have h8 : (2 : ℝ) ^ (-(N : ℤ)) = 8 * u := by
    have e : (2 : ℝ) ^ (-(N : ℤ)) = (2 : ℝ) ^ ((3 : ℤ) + (-(N : ℤ) - 3)) := by congr 1; ring
    rw [e, zpow_add₀ two_ne_zero, hu_def]
    norm_num
  -- the two corners of the cell lie in `S₂`
  have hlo := hsub (show (⟨(j : ℝ) * 2 ^ (-(N : ℤ)), (k : ℝ) * 2 ^ (-(N : ℤ))⟩ : ℂ) ∈ closedDyadicSquare N j k by
    simp only [closedDyadicSquare, Complex.mem_reProdIm, Set.mem_Icc, h8]
    exact ⟨⟨le_rfl, by linarith⟩, le_rfl, by linarith⟩)
  have hhi := hsub
    (show (⟨((j : ℝ) + 1) * 2 ^ (-(N : ℤ)), ((k : ℝ) + 1) * 2 ^ (-(N : ℤ))⟩ : ℂ) ∈ closedDyadicSquare N j k by
      simp only [closedDyadicSquare, Complex.mem_reProdIm, Set.mem_Icc, h8]
      exact ⟨⟨by linarith, le_rfl⟩, by linarith, le_rfl⟩)
  simp only [closedDyadicSquare, Complex.mem_reProdIm, Set.mem_Icc, h8] at hlo hhi
  obtain ⟨⟨hA1, -⟩, hA3, -⟩ := hlo
  obtain ⟨⟨-, hB2⟩, -, hB4⟩ := hhi
  -- hence `n₀ ≤ N`
  have hN : n₀ ≤ (N : ℤ) := by
    have h : (2 : ℝ) ^ (-(N : ℤ)) ≤ 2 ^ (-n₀) := by rw [h8]; linarith
    have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h
    omega
  have hm : (m : ℤ) = N + 3 - n₀ := Int.toNat_of_nonneg (by omega)
  have hs : (2 : ℝ) ^ (-n₀) = 2 ^ m * u := by
    rw [hu_def, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
    congr 1
    omega
  have hsu : (2 : ℝ) ^ (-n₀) / 2 ^ m = u := by
    rw [hs]
    field_simp
  rw [hs] at hA1 hA3 hB2 hB4
  -- grid inequalities
  have hc1 : j₂ * 2 ^ m ≤ 8 * j - 1 + 1 := by
    have : ((j₂ * 2 ^ m : ℤ) : ℝ) * u ≤ ((8 * j : ℤ) : ℝ) * u := by push_cast; linarith
    have := le_of_mul_le_mul_right this hu
    have : j₂ * 2 ^ m ≤ 8 * j := by exact_mod_cast this
    linarith
  have hT1 : 8 * j - 1 + 9 ≤ j₂ * 2 ^ m + ((2 ^ m : ℕ) : ℤ) := by
    have : ((8 * j + 8 : ℤ) : ℝ) * u ≤ ((j₂ * 2 ^ m + 2 ^ m : ℤ) : ℝ) * u := by push_cast; linarith
    have := le_of_mul_le_mul_right this hu
    have : 8 * j + 8 ≤ j₂ * 2 ^ m + 2 ^ m := by exact_mod_cast this
    push_cast
    linarith
  have hc2 : k₂ * 2 ^ m ≤ 8 * k - 1 + 1 := by
    have : ((k₂ * 2 ^ m : ℤ) : ℝ) * u ≤ ((8 * k : ℤ) : ℝ) * u := by push_cast; linarith
    have := le_of_mul_le_mul_right this hu
    have : k₂ * 2 ^ m ≤ 8 * k := by exact_mod_cast this
    linarith
  have hT2 : 8 * k - 1 + 9 ≤ k₂ * 2 ^ m + ((2 ^ m : ℕ) : ℤ) := by
    have : ((8 * k + 8 : ℤ) : ℝ) * u ≤ ((k₂ * 2 ^ m + 2 ^ m : ℤ) : ℝ) * u := by push_cast; linarith
    have := le_of_mul_le_mul_right this hu
    have : 8 * k + 8 ≤ k₂ * 2 ^ m + 2 ^ m := by exact_mod_cast this
    push_cast
    linarith
  have ha1 : (j₂ : ℝ) * 2 ^ (-n₀) = ((j₂ * 2 ^ m : ℤ) : ℝ) * u := by push_cast; rw [hs]; ring
  have ha2 : (k₂ : ℝ) * 2 ^ (-n₀) = ((k₂ * 2 ^ m : ℤ) : ℝ) * u := by push_cast; rw [hs]; ring
  obtain ⟨i₀, K, hK, hiK, hre⟩ := Icc_inter_Icc_eq_grid hu ha1 hc1 hT1
  obtain ⟨j₀, L, hL, hjL, him⟩ := Icc_inter_Icc_eq_grid hu ha2 hc2 hT2
  refine ⟨i₀, j₀, K, L, hK, hL, hiK, hjL, ?_⟩
  have hS2 : closedDyadicSquare n₀ j₂ k₂ =
      Icc ((j₂ : ℝ) * 2 ^ (-n₀)) ((j₂ : ℝ) * 2 ^ (-n₀) + ((2 ^ m : ℕ) : ℝ) * u) ×ℂ
        Icc ((k₂ : ℝ) * 2 ^ (-n₀)) ((k₂ : ℝ) * 2 ^ (-n₀) + ((2 ^ m : ℕ) : ℝ) * u) := by
    simp only [closedDyadicSquare]
    push_cast
    rw [hs]
    congr 2 <;> ring
  rw [hsu, enlargedDyadicCell_eq_reProdIm, hS2, reProdIm_inter_reProdIm, ← hu_def, hre, him]

end HarmonicBalls
