import HarmonicBalls.Defs.LBM
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Almost-sure locally uniform clock approximation

A deterministic subsequence of the dyadic clock approximations converges almost
surely uniformly on every bounded time interval.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-- Dyadic clock approximations admit a deterministic subsequence converging
almost surely uniformly on every bounded time interval. -/
theorem IsLQGClock.exists_seq_locally_uniform_clockApprox
    {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hclock : IsLQGClock planarBrownianMotion γ hε x F) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ᵐ b ∂(planarBrownianMotion x), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ n in atTop, ∀ t ≤ T,
          |lqgClockApprox γ hε (dyadicScale (s n)) b t - F b t| < η := by
  classical
  let bad (n k : ℕ) : Set (ContinuousPath ℂ) :=
    {b | ∃ t ≤ (n : ℝ≥0), (2⁻¹ : ℝ) ^ n ≤
      |lqgClockApprox γ hε (dyadicScale k) b t - F b t|}
  have hchoice (n : ℕ) : ∃ N, ∀ k ≥ N,
      planarBrownianMotion x (bad n k) ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
    have hc := hclock (n : ℝ≥0) ((2⁻¹ : ℝ) ^ n) (by positivity)
    rw [ENNReal.tendsto_atTop_zero] at hc
    exact hc ((2⁻¹ : ℝ≥0∞) ^ n) (ENNReal.pow_pos (by simp) _)
  let N : ℕ → ℕ := fun n => Classical.choose (hchoice n)
  have hN (n k : ℕ) (h : N n ≤ k) :
      planarBrownianMotion x (bad n k) ≤ (2⁻¹ : ℝ≥0∞) ^ n :=
    Classical.choose_spec (hchoice n) k h
  let s : ℕ → ℕ := Nat.rec (N 0) (fun n v => max (N (n + 1)) (v + 1))
  have hsN (n : ℕ) : N n ≤ s n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_left _ _
  have hs : StrictMono s := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hsum : (∑' n, planarBrownianMotion x (bad n (s n))) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum (fun n => hN n (s n) (hsN n)))
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using ENNReal.ofNat_ne_top
  have hae : ∀ᵐ b ∂(planarBrownianMotion x), ¬ ∃ᶠ n in atTop, b ∈ bad n (s n) := by
    rw [ae_iff]
    simpa only [not_not] using (measure_setOfPred_frequently_eq_zero (p := fun n b => b ∈ bad n (s n)) hsum)
  refine ⟨s, hs, ?_⟩
  filter_upwards [hae] with b hb
  have hb' : ∀ᶠ n in atTop, b ∉ bad n (s n) := not_frequently.mp hb
  intro T η hη
  obtain ⟨M, hM⟩ := exists_nat_ge (T : ℝ)
  have hpow : ∀ᶠ n : ℕ in atTop, (2⁻¹ : ℝ) ^ n < η :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually (Iio_mem_nhds hη)
  filter_upwards [hb', hpow, eventually_ge_atTop M] with n hn hsmall hnM t ht
  have hT : T ≤ (n : ℝ≥0) := by
    exact_mod_cast hM.trans (Nat.cast_le.mpr hnM)
  have hnot : ¬ (2⁻¹ : ℝ) ^ n ≤
      |lqgClockApprox γ hε (dyadicScale (s n)) b t - F b t| := by
    intro h
    exact hn ⟨t, ht.trans hT, h⟩
  exact (lt_of_not_ge hnot).trans hsmall

end HarmonicBalls
