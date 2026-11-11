import Mathlib

/-!
# Convergence on a countable family implies convergence on all tests

The good set of the
measure part is defined through the countable family `Ψ` of `exists_countable_compactSupport_approx`
(`CompactTestDensity.lean`). This file proves the analytic step: if locally finite measures `ν n` have masses on each
closed ball bounded uniformly in `n`, and the integrals against `Ψ` converge, then the integrals against every
compactly supported continuous test converge. The approximation error is controlled by the local mass, and the Cauchy
criterion finishes the argument.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric

/-- **Convergence on a countable determining family.** Let `ν n` be locally finite measures on `ℂ` whose masses on the
closed balls `closedBall 0 (R + 1)` are bounded in `n`, for each `R : ℕ`. Let `Ψ` be a family of compactly supported
continuous tests that approximates every continuous test vanishing outside a ball (on the next ball, by a member
vanishing outside it), and whose integrals converge. Then the integrals of every compactly supported continuous test
converge. -/
theorem exists_tendsto_integral_of_countable_approx {ν : ℕ → Measure ℂ}
    (hloc : ∀ n, IsLocallyFiniteMeasure (ν n))
    {Ψ : Set (ℂ → ℝ)} (hΨ : ∀ g ∈ Ψ, Continuous g ∧ HasCompactSupport g)
    (happ : ∀ ψ : ℂ → ℝ, Continuous ψ → ∀ R : ℕ, (∀ z : ℂ, (R : ℝ) < ‖z‖ → ψ z = 0) →
        ∀ ε : ℝ, 0 < ε → ∃ g ∈ Ψ, (∀ z : ℂ, (R : ℝ) + 1 < ‖z‖ → g z = 0) ∧
          ∀ z : ℂ, ‖z‖ ≤ (R : ℝ) + 1 → |g z - ψ z| < ε)
    (hbd : ∀ R : ℕ, ∃ C : ℝ, ∀ n, (ν n (closedBall (0 : ℂ) ((R : ℝ) + 1))).toReal ≤ C)
    (hconv : ∀ g ∈ Ψ, ∃ L : ℝ, Tendsto (fun n => ∫ z, g z ∂(ν n)) atTop (𝓝 L))
    (ψ : ℂ → ℝ) (hψ : Continuous ψ) (hcs : HasCompactSupport ψ) :
    ∃ L : ℝ, Tendsto (fun n => ∫ z, ψ z ∂(ν n)) atTop (𝓝 L) := by
  -- a natural radius outside which `ψ` vanishes
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).mp hcs.isCompact.isBounded
  obtain ⟨R, hRr⟩ := exists_nat_ge r
  have hψR : ∀ z : ℂ, (R : ℝ) < ‖z‖ → ψ z = 0 := by
    intro z hz
    by_contra hne
    have hmem : z ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hne)
    have h1 : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp (hr hmem)
    linarith
  obtain ⟨C, hC⟩ := hbd R
  have hcauchy : CauchySeq (fun n => ∫ z, ψ z ∂(ν n)) := by
    rw [Metric.cauchySeq_iff]
    intro η hη
    have hKpos : 0 < |C| + 1 := by have := abs_nonneg C; linarith
    have hKne : |C| + 1 ≠ 0 := hKpos.ne'
    have h4K : 0 < 4 * (|C| + 1) := by linarith
    have hεpos : 0 < η / (4 * (|C| + 1)) := div_pos hη h4K
    obtain ⟨g, hgΨ, hgout, hgclose⟩ := happ ψ hψ R hψR (η / (4 * (|C| + 1))) hεpos
    obtain ⟨L, hL⟩ := hconv g hgΨ
    -- the uniform error bound between `∫ ψ` and `∫ g` on every `ν n`
    have hbound : ∀ n, |(∫ z, ψ z ∂(ν n)) - ∫ z, g z ∂(ν n)| ≤ η / (4 * (|C| + 1)) * (|C| + 1) := by
      intro n
      have := hloc n
      have hgi : Integrable g (ν n) := (hΨ g hgΨ).1.integrable_of_hasCompactSupport (hΨ g hgΨ).2
      have hψi : Integrable ψ (ν n) := hψ.integrable_of_hasCompactSupport hcs
      have hdiff : (∫ z, ψ z ∂(ν n)) - ∫ z, g z ∂(ν n) = ∫ z, (ψ z - g z) ∂(ν n) :=
        (integral_sub hψi hgi).symm
      rw [hdiff]
      -- the integrand vanishes outside the closed ball of radius `R + 1`
      have hzero : ∀ z : ℂ, z ∉ closedBall (0 : ℂ) ((R : ℝ) + 1) → ψ z - g z = 0 := by
        intro z hz
        have hz' : (R : ℝ) + 1 < ‖z‖ := by
          rw [mem_closedBall_zero_iff, not_le] at hz
          exact hz
        rw [hψR z (by linarith), hgout z hz', sub_zero]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
      have hfin : ν n (closedBall (0 : ℂ) ((R : ℝ) + 1)) < ⊤ :=
        (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 1)).measure_lt_top
      have hnorm := norm_setIntegral_le_of_norm_le_const (μ := ν n) (f := fun z => ψ z - g z)
        (C := η / (4 * (|C| + 1))) hfin (fun z hz => by
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact (hgclose z (mem_closedBall_zero_iff.mp hz)).le)
      have hreal : Measure.real (ν n) (closedBall (0 : ℂ) ((R : ℝ) + 1)) ≤ |C| + 1 := by
        have h1 : (ν n (closedBall (0 : ℂ) ((R : ℝ) + 1))).toReal ≤ C := hC n
        have h2 : C ≤ |C| := le_abs_self C
        have h3 : Measure.real (ν n) (closedBall (0 : ℂ) ((R : ℝ) + 1)) =
            (ν n (closedBall (0 : ℂ) ((R : ℝ) + 1))).toReal := rfl
        linarith
      calc |∫ z in closedBall (0 : ℂ) ((R : ℝ) + 1), (ψ z - g z) ∂(ν n)|
          = ‖∫ z in closedBall (0 : ℂ) ((R : ℝ) + 1), (ψ z - g z) ∂(ν n)‖ := (Real.norm_eq_abs _).symm
        _ ≤ η / (4 * (|C| + 1)) * Measure.real (ν n) (closedBall (0 : ℂ) ((R : ℝ) + 1)) := hnorm
        _ ≤ η / (4 * (|C| + 1)) * (|C| + 1) := mul_le_mul_of_nonneg_left hreal hεpos.le
    -- the constant `η / (4 (|C| + 1)) * (|C| + 1)` equals `η / 4`
    have hK4 : η / (4 * (|C| + 1)) * (|C| + 1) = η / 4 := by
      rw [div_mul_eq_mul_div, mul_div_mul_right η 4 hKne]
    rw [hK4] at hbound
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hL.cauchySeq (η / 4) (div_pos hη (by norm_num))
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 := hbound m
    have h2 := hbound n
    have h3 := hN m hm n hn
    rw [Real.dist_eq] at h3
    have t1 := abs_sub_le (∫ z, ψ z ∂(ν m)) (∫ z, g z ∂(ν m)) (∫ z, ψ z ∂(ν n))
    have t2 := abs_sub_le (∫ z, g z ∂(ν m)) (∫ z, g z ∂(ν n)) (∫ z, ψ z ∂(ν n))
    rw [abs_sub_comm (∫ z, g z ∂(ν n)) (∫ z, ψ z ∂(ν n))] at t2
    have h2' : |(∫ z, ψ z ∂(ν n)) - ∫ z, g z ∂(ν n)| ≤ η / 4 := h2
    linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨L, hL⟩

end HarmonicBalls
