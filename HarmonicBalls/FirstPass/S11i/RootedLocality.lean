import HarmonicBalls.FirstPass.S11i.RootedFrequencyShift

/-!
# Locality of the rooted window frequency (write-up Step 11.4)

For `R ≥ 0` and an event `F` of the pairings on the ball `B_R(0)` modulo constants, the event
`E = ballRestrictPairing R ⁻¹' F` depends only on the canonical field restricted to `B_R(0)`.
The dilation `dilateTest n` shrinks supports by `2⁻ⁿ` (`DilationMixing.lean:23`): the test function `κₙ i`
for `i` supported in `B_R(0)` is supported in `B_{R/2ⁿ}(0)`. Hence two distributions `T`, `T'` that agree on test
functions supported in `B_b(0)` give the same dilated canonical pairings on `B_R(0)` as soon as `R / 2ⁿ < b`, and the
window frequencies of `E` at `T` and `T'` coincide for every `N` with `R / 2^(N+1) < b`. Only deterministic algebra
(`iterate_dilOp`, `MixingCanonical.lean:123`; `canonFieldOf`, `RootedFrequencyShift.lean:29`).

This is the locality used in Step 11 of the write-up to pass from a
distribution agreeing with `h^γ + u` on `B_b(0)` to the local event; it is not a probability statement.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- The restriction of a canonical pairing on the whole plane to the test functions supported in `B_R(0)`. -/
def ballRestrictPairing (R : ℝ) (L : ModConstTestPairings (Set.univ : Set ℂ)) :
    ModConstTestPairings (ball (0 : ℂ) R) :=
  fun i => L ⟨i.1, ⟨i.2.1.1, i.2.1.2.1, subset_univ _⟩, i.2.2⟩

/-- Dilation shrinks supports: if `tsupport k ⊆ B_R(0)` then `tsupport (κₙ k) ⊆ closedBall 0 (R / 2ⁿ)`, where
`κₙ k (y) = 4ⁿ k (2ⁿ • y)` (`dilateTest`, `DilationMixing.lean:23`). -/
theorem tsupport_dilateTest_subset {R : ℝ} {k : ℂ → ℝ} (hk : tsupport k ⊆ ball (0 : ℂ) R) (n : ℕ) :
    tsupport (dilateTest n k) ⊆ closedBall (0 : ℂ) (R / 2 ^ n) := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  have hy' : k (((2 : ℝ) ^ n) • y) ≠ 0 := by
    intro h
    apply Function.mem_support.mp hy
    show (4 : ℝ) ^ n * k (((2 : ℝ) ^ n) • y) = 0
    rw [h, mul_zero]
  have hmem : ((2 : ℝ) ^ n) • y ∈ ball (0 : ℂ) R :=
    hk (subset_tsupport _ (Function.mem_support.mpr hy'))
  have hn : ‖((2 : ℝ) ^ n)‖ = (2 : ℝ) ^ n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [mem_ball_zero_iff, norm_smul, hn] at hmem
  rw [mem_closedBall_zero_iff, le_div_iff₀ (by positivity), mul_comm]
  exact hmem.le

/-- Locality of the dilated canonical pairings. If `T` and `T'` agree on the test functions supported in `B_b(0)`,
then for `R / 2ⁿ < b` the `n`-th dilate of the canonical field of `T` and of `T'` agree on `B_R(0)`. -/
theorem ballRestrict_dilOp_iterate_eq (γ : ℝ) {T T' : (ℂ → ℝ) → ℝ} {b R : ℝ}
    (hT : ∀ φ : ℂ → ℝ, IsTestFunction (ball (0 : ℂ) b) φ → ∫ x, φ x = 0 → T φ = T' φ) (n : ℕ)
    (hnb : R / 2 ^ n < b) :
    ballRestrictPairing R (dilOp^[n] (canonFieldOf γ T)) =
      ballRestrictPairing R (dilOp^[n] (canonFieldOf γ T')) := by
  funext i
  have hu : IsTestFunction (Set.univ : Set ℂ) i.1 := ⟨i.2.1.1, i.2.1.2.1, subset_univ _⟩
  have hd := isTestFunction_dilateTest hu n
  have hsupp : IsTestFunction (ball (0 : ℂ) b) (dilateTest n i.1) :=
    ⟨hd.1, hd.2.1, (tsupport_dilateTest_subset i.2.1.2.2 n).trans (closedBall_subset_ball hnb)⟩
  have key := hT _ hsupp ((integral_dilateTest n i.1).trans i.2.2)
  simp only [ballRestrictPairing, iterate_dilOp, canonFieldOf, fieldPairing]
  rw [key]

/-- Step 11.4 (locality of the window frequency). For `R ≥ 0`, an event `F` on `B_R(0)` modulo constants, and
distributions `T`, `T'` agreeing on the test functions supported in `B_b(0)`, the window frequencies of
`E = ballRestrictPairing R ⁻¹' F` at `T` and `T'` coincide for every `N` with `R / 2^(N+1) < b`
(all dilation indices `n ∈ [N+1, 2N]` satisfy `R / 2ⁿ ≤ R / 2^(N+1) < b`). -/
theorem windowFreqOf_ballRestrict_eq (γ : ℝ) {R b : ℝ} (hR : 0 ≤ R)
    (F : Set (ModConstTestPairings (ball (0 : ℂ) R)))
    {T T' : (ℂ → ℝ) → ℝ} (hT : ∀ φ : ℂ → ℝ, IsTestFunction (ball (0 : ℂ) b) φ → ∫ x, φ x = 0 → T φ = T' φ)
    (N : ℕ) (hN : R / 2 ^ (N + 1) < b) :
    windowFreqOf γ (ballRestrictPairing R ⁻¹' F) T N = windowFreqOf γ (ballRestrictPairing R ⁻¹' F) T' N := by
  unfold windowFreqOf
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have h2 : (2 : ℝ) ^ (N + 1) ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn.1
  have hnb : R / 2 ^ n < b :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left hR (by positivity) h2) hN
  have hr := ballRestrict_dilOp_iterate_eq γ hT n hnb
  by_cases hm : dilOp^[n] (canonFieldOf γ T) ∈ ballRestrictPairing R ⁻¹' F
  · have hm' : dilOp^[n] (canonFieldOf γ T') ∈ ballRestrictPairing R ⁻¹' F := by
      have h1 : ballRestrictPairing R (dilOp^[n] (canonFieldOf γ T)) ∈ F := hm
      show ballRestrictPairing R (dilOp^[n] (canonFieldOf γ T')) ∈ F
      rw [← hr]
      exact h1
    rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
  · have hm' : dilOp^[n] (canonFieldOf γ T') ∉ ballRestrictPairing R ⁻¹' F := by
      intro h
      apply hm
      have h1 : ballRestrictPairing R (dilOp^[n] (canonFieldOf γ T')) ∈ F := h
      show ballRestrictPairing R (dilOp^[n] (canonFieldOf γ T)) ∈ F
      rw [hr]
      exact h1
    rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm']

end HarmonicBalls
