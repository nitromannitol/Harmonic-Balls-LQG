import HarmonicBalls.Proofs.Sec6.LowMass
import HarmonicBalls.Proofs.Sec6.PrevalenceGridCard

/-! # Quantitative lattice covers of the unit disc -/

namespace HarmonicBalls.Section6

open Metric Set

/-- A mesh-`δ` lattice supplies a finite cover of the unit disc by balls of
radius `2δ`, with at most `(7/δ)²` centres. -/
theorem exists_unitDisc_lattice_cover {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ T : Finset ℂ, (T.card : ℝ) ≤ (7 / δ) ^ 2 ∧
      ∀ z ∈ ball (0 : ℂ) 1, ∃ x ∈ T, z ∈ ball x (2 * δ) := by
  classical
  let M : ℤ := ⌈2 / δ⌉
  let S : Set ℤ := Icc (-M) M
  let f : ℤ × ℤ → ℂ := fun p => (δ : ℂ) * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
  have hM : 0 ≤ M := by
    have h : (0 : ℝ) ≤ (M : ℝ) := (div_nonneg (by norm_num) hδ.le).trans (Int.le_ceil _)
    exact_mod_cast h
  have hf : S.Finite := Set.finite_Icc _ _
  let T : Finset ℂ := ((hf.prod hf).image f).toFinset
  have hc : (S.ncard : ℝ) = 2 * (M : ℝ) + 1 := by
    have hcard := Int.card_Icc_of_le (a := -M) (b := M) (by omega)
    have hcast : ((Finset.Icc (-M) M).card : ℝ) = ((M + 1 - -M : ℤ) : ℝ) := by
      exact_mod_cast hcard
    have hcast' : (S.ncard : ℝ) = (M : ℝ) + 1 + (M : ℝ) := by
      simpa [S, ← Set.ncard_coe_finset, Int.cast_add, Int.cast_sub] using hcast
    linarith
  have hn : (T.card : ℝ) ≤ (2 * (M : ℝ) + 1) ^ 2 := by
    have hi : (f '' (S ×ˢ S)).ncard ≤ (S ×ˢ S).ncard := Set.ncard_image_le (hf.prod hf)
    have hi' : ((f '' (S ×ˢ S)).ncard : ℝ) ≤ ((S ×ˢ S).ncard : ℝ) := by exact_mod_cast hi
    rw [Set.ncard_eq_toFinset_card _ ((hf.prod hf).image f)] at hi'
    simpa [T, Set.ncard_prod, Nat.cast_mul, hc, pow_two] using hi'
  have hceil : (M : ℝ) < 2 / δ + 1 := Int.ceil_lt_add_one _
  have hinv : 1 ≤ 1 / δ := (le_div_iff₀ hδ).2 (by simpa using hδ1)
  have hbound : 2 * (M : ℝ) + 1 ≤ 7 / δ := by
    have hthree : 3 ≤ 3 / δ := by
      calc
        3 ≤ 3 * (1 / δ) := by linarith
        _ = 3 / δ := by ring
    have hid : 7 / δ = 2 * (2 / δ) + 3 / δ := by ring
    linarith
  have hnonneg : 0 ≤ 2 * (M : ℝ) + 1 := by exact_mod_cast (by omega : 0 ≤ 2 * M + 1)
  refine ⟨T, hn.trans (pow_le_pow_left₀ hnonneg hbound 2), ?_⟩
  intro z hz
  obtain ⟨j, k, hnear⟩ := exists_lattice_near z hδ
  let w : ℂ := f (j, k)
  have hw : ‖w‖ ≤ 2 := by
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have htriangle : ‖w‖ ≤ ‖z - w‖ + ‖z‖ := by
      calc
        ‖w‖ = ‖-(z - w) + z‖ := by congr 1; abel
        _ ≤ ‖-(z - w)‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z - w‖ + ‖z‖ := by rw [norm_neg]
    have hn' : ‖z - w‖ ≤ δ := hnear
    linarith
  have hj : |δ * (j : ℝ)| ≤ 2 := by
    have h := (Complex.abs_re_le_norm w).trans hw
    simpa [w, f] using h
  have hk : |δ * (k : ℝ)| ≤ 2 := by
    have h := (Complex.abs_im_le_norm w).trans hw
    simpa [w, f] using h
  have hc' : 2 / δ ≤ (M : ℝ) := Int.le_ceil _
  have hj' : |(j : ℝ)| ≤ (M : ℝ) := by
    rw [abs_mul, abs_of_pos hδ] at hj
    exact ((le_div_iff₀ hδ).2 (by nlinarith)).trans hc'
  have hk' : |(k : ℝ)| ≤ (M : ℝ) := by
    rw [abs_mul, abs_of_pos hδ] at hk
    exact ((le_div_iff₀ hδ).2 (by nlinarith)).trans hc'
  have hjS : j ∈ S := by
    have h := abs_le.mp hj'
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have hkS : k ∈ S := by
    have h := abs_le.mp hk'
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  refine ⟨w, ?_, ?_⟩
  · change w ∈ ((hf.prod hf).image f).toFinset
    simp only [Set.Finite.mem_toFinset]
    exact ⟨(j, k), ⟨hjS, hkS⟩, rfl⟩
  · rw [mem_ball, dist_eq_norm]
    change ‖z - w‖ < 2 * δ
    have hn' : ‖z - w‖ ≤ δ := hnear
    linarith

end HarmonicBalls.Section6
