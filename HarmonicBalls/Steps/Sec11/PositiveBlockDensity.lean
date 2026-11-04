import HarmonicBalls.Steps.Sec11.InternalPinchScales
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Positive block density and small pinch scales -/

namespace HarmonicBalls

open Set Filter
open scoped Topology

/-- A positive eventual block-density bound forces occurrences at arbitrarily
large indices. -/
theorem frequently_of_positive_block_density {p : ℕ → Prop} {q : ℝ}
    (hq : 0 < q)
    (hfreq : ∀ᶠ N : ℕ in atTop, q * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ p n}.ncard : ℝ)) :
    ∃ᶠ n in atTop, p n := by
  classical
  obtain ⟨K, hK⟩ := eventually_atTop.mp hfreq
  apply frequently_atTop.mpr
  intro b
  let N := max K (max b 1)
  have hKN : K ≤ N := le_max_left _ _
  have hbN : b ≤ N := (le_max_left b 1).trans (le_max_right K _)
  have hN : 0 < N := lt_of_lt_of_le (by norm_num : 0 < 1)
    ((le_max_right b 1).trans (le_max_right K _))
  have hbound := hK N hKN
  have hnonempty : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ p n}.Nonempty := by
    by_contra hne
    have heq : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ p n} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    rw [heq, Set.ncard_empty] at hbound
    have : 0 < q * (N : ℝ) := mul_pos hq (by exact_mod_cast hN)
    norm_num at hbound
    linarith
  obtain ⟨n, hn⟩ := hnonempty
  exact ⟨n, le_trans hbN (le_trans (Nat.le_succ N) hn.1), hn.2.2⟩

/-- Positive block density yields pinch scales below every positive radius. -/
theorem exists_small_dyadic_scale_of_positive_block_density
    {p : ℕ → Prop} {q : ℝ} (hq : 0 < q)
    (hfreq : ∀ᶠ N : ℕ in atTop, q * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ p n}.ncard : ℝ)) :
    ∀ r : ℝ, 0 < r → ∃ n : ℕ, (2 : ℝ)⁻¹ ^ n < r ∧ p n := by
  intro r hr
  have hlim : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ n : ℕ in atTop, ((2 : ℝ)⁻¹) ^ n < r :=
    hlim.eventually (Iio_mem_nhds hr)
  exact (hsmall.and_frequently (frequently_of_positive_block_density hq hfreq)).exists

#print axioms frequently_of_positive_block_density
#print axioms exists_small_dyadic_scale_of_positive_block_density

end HarmonicBalls
