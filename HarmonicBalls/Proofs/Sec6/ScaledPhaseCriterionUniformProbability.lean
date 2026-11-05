import HarmonicBalls.Proofs.Sec6.ScaledPhaseCriterionProbability
import HarmonicBalls.Proofs.Sec8.PhaseCriterionTranslation
import HarmonicBalls.Proofs.Sec6.UniformPolynomialDyadicTail

/-! # Arbitrary-radius probability for the third criterion

The good-annulus count estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- The third criterion holds with uniformly high probability at every
positive radius, deterministic centre and prescribed phase sequence. The starting index is common to all
whole-plane realizations. -/
theorem exists_universal_phaseCriterionThree_probability_all_radii
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ (s : ℝ), 0 < s → ∀ (x : ℂ) (phase : ℕ → ℂ),
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N a b (1 / 32) phase} ≤ δ := by
  obtain ⟨a, ha, D, r₀, hD, hr₀, hscale⟩ :=
    exists_scaled_phase_criterionThree_one_scale_failure_bound hgrowth hγ hγ₂ h₀ hμ₀ hb
  obtain ⟨N₀, hN₀, htail⟩ :=
    exists_uniform_dyadic_polynomial_tail_bound (p₀ := 4) (C₀ := D) (r₀ := r₀)
      (by norm_num) hr₀ hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hCfield hcirc μ hgff hμ s hs x phase
  let F : ℕ → Set Ω := fun n => if 9 ≤ n then
    {ω | ∀ z ∈ annulus x (s / 2) s,
      z - phase n ∈ scaledLattice (dyadicScale n * s / 100) →
      (1 / 32 : ℝ) * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)} else univ
  have hF : ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < r₀ →
      P (F n)ᶜ ≤ ENNReal.ofReal (D * ((2 : ℝ)⁻¹ ^ n) ^ (4 : ℝ)) := by
    intro n hsmall
    by_cases hn : 9 ≤ n
    · simpa only [F, ite_eq_left hn, compl_ofPred, dyadicScale] using
        hscale Ω P hCfield hcirc μ hgff hμ s hs x (phase n) n hn (by simpa only [dyadicScale] using hsmall)
    · simp only [F, ite_eq_right hn, compl_univ, measure_empty, zero_le]
  calc
    P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N a b (1 / 32) phase} ≤
        P {ω | ∀ n : ℕ, N ≤ n → ω ∈ F n}ᶜ := by
      apply measure_mono
      intro ω hbad hgood
      apply hbad
      intro n hn
      have hn9 : 9 ≤ n := hN₀.trans (hN.trans hn)
      simpa only [F, ite_eq_left hn9, mem_ofPred_eq] using hgood n hn
    _ ≤ δ := htail N hN Ω P F hF

end HarmonicBalls.Section6
