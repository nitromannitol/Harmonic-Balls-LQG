import HarmonicBalls.Proofs.Sec6.PhaseGridApprox
import HarmonicBalls.Proofs.Sec6.CriterionThreeOffCenter

/-! # Uniform probability for arbitrary lattice phases -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- Whole-plane subrange prevalence gives a criterion-three probability bound
uniform in the center and in an arbitrary sequence of lattice phases. The
starting index does not depend on either the center or the phases. -/
theorem exists_phase_uniform_unit_criterionThree_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (x : ℂ) (phase : ℕ → ℂ),
      P {ω | ¬ ∀ n : ℕ, N ≤ n → ∀ z ∈ annulus x (1 / 2) 1,
        z - phase n ∈ scaledLattice (dyadicScale n / 100) →
        c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * 1) (Real.sqrt (dyadicScale n) * 1) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = 1 * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)} ≤ δ := by
  obtain ⟨N₀, hN₀, hbound⟩ := exists_uniform_dyadic_failure_tail_bound P hprev hδ
  refine ⟨N₀, hN₀, fun N hN x phase => ?_⟩
  have hpos (n : ℕ) : 0 < dyadicScale n / 100 := by
    unfold dyadicScale
    positivity
  choose y hy hxy using fun n : ℕ => exists_phase_scaledLattice_dist_lt x (phase n) (hpos n)
  let F : ℕ → Set Ω := fun n => {ω | ∀ z ∈ prevalenceGrid (dyadicScale n),
    c * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
        (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus ((μ ω).map (fun w : ℂ => w + -(y n))) r z a b}.ncard : ℝ)}
  have hF : ∀ n, P (F n)ᶜ ≤ P {ω | ∀ z ∈ prevalenceGrid ((2 : ℝ)⁻¹ ^ n),
      c * Real.logb 7 (((2 : ℝ)⁻¹ ^ n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ((2 : ℝ)⁻¹ ^ n) (((2 : ℝ)⁻¹ ^ n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)}ᶜ := by
    intro n
    have heq := measure_subrange_prevalence_failure_translate hγ hγ₂ hgff hμ hAff hCC
      (dyadicScale n) a b c (y n) hunit
    simpa only [F, dyadicScale, compl_ofPred] using heq.symm.le
  calc P {ω | ¬ ∀ n : ℕ, N ≤ n → ∀ z ∈ annulus x (1 / 2) 1,
        z - phase n ∈ scaledLattice (dyadicScale n / 100) →
        c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * 1) (Real.sqrt (dyadicScale n) * 1) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = 1 * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)} ≤
      P {ω | ∀ n : ℕ, N ≤ n → ω ∈ F n}ᶜ := by
        apply measure_mono
        intro ω hbad hgood
        apply hbad
        intro n hn
        exact phase_criterionThree_count_of_translated_subrange_prevalence hc
          (hN₀.trans (hN.trans hn)) (hy n) (hxy n) (hgood n hn)
    _ ≤ δ := hbound N hN F hF

end HarmonicBalls.Section6
