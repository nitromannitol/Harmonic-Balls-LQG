import HarmonicBalls.Proofs.Sec6.FinitePhaseProbability
import HarmonicBalls.Proofs.Sec6.UniformPolynomialDyadicTail

/-! # Field-dependent lattice phases with growing finite ranges

The good-annulus count estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Polynomial decay at one mesh absorbs up to `2^(3*n)` candidate phases at
mesh `2⁻ⁿ`. The phase sets are deterministic, but the selected phase at
any mesh may depend arbitrarily on the whole field. -/
theorem exists_universal_growing_phaseCriterion_probability
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
    ∀ (s : ℝ), 0 < s → ∀ (x : ℂ) (F : ℕ → Finset ℂ),
      (∀ n, (F n).card ≤ 2 ^ (3 * n)) →
    ∀ (phase : Ω → ℕ → ℂ), (∀ ω n, phase ω n ∈ F n) →
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N a b (1 / 32) (phase ω)} ≤ δ := by
  classical
  obtain ⟨a, ha, D, r₀, hD, hr₀, hscale⟩ :=
    exists_scaled_phase_criterionThree_one_scale_failure_bound hgrowth hγ hγ₂ h₀ hμ₀ hb
  obtain ⟨N₀, hN₀, htail⟩ :=
    exists_uniform_dyadic_polynomial_tail_bound (p₀ := 1) (C₀ := D) (r₀ := r₀)
      (by norm_num) hr₀ hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hCfield hcirc μ hgff hμ s hs x phases hcard phase hphase
  let E : ℕ → ℂ → Set Ω := fun n q => {ω |
    ¬ ∀ z ∈ annulus x (s / 2) s,
      z - q ∈ scaledLattice (dyadicScale n * s / 100) →
      (1 / 32 : ℝ) * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)}
  let G : ℕ → Set Ω := fun n => if 9 ≤ n then (⋃ q ∈ phases n, E n q)ᶜ else univ
  have hG : ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < r₀ →
      P (G n)ᶜ ≤ ENNReal.ofReal (D * ((2 : ℝ)⁻¹ ^ n) ^ (1 : ℝ)) := by
    intro n hsmall
    by_cases hn : 9 ≤ n
    · have hsum : P (⋃ q ∈ phases n, E n q) ≤
          ((phases n).card : ℝ≥0∞) * ENNReal.ofReal (D * (dyadicScale n) ^ (4 : ℝ)) := by
        calc
          _ ≤ ∑ q ∈ phases n, P (E n q) := measure_biUnion_finset_le _ _
          _ ≤ ∑ _q ∈ phases n, ENNReal.ofReal (D * (dyadicScale n) ^ (4 : ℝ)) := by
            apply Finset.sum_le_sum
            intro q hq
            exact hscale Ω P hCfield hcirc μ hgff hμ s hs x q n hn (by simpa [dyadicScale] using hsmall)
          _ = _ := by simp
      have hncast : ((phases n).card : ℝ≥0∞) ≤ ((2 : ℕ) ^ (3 * n) : ℝ≥0∞) := by exact_mod_cast hcard n
      have hpow : (((2 : ℕ) ^ (3 * n) : ℝ≥0∞) * ENNReal.ofReal (D * (dyadicScale n) ^ (4 : ℝ))) =
          ENNReal.ofReal (D * ((2 : ℝ)⁻¹ ^ n) ^ (1 : ℝ)) := by
        have htwo : 0 < ((2 : ℝ) ^ n) := by positivity
        have heq : (dyadicScale n) = ((2 : ℝ) ^ n)⁻¹ := by simp [dyadicScale, inv_pow]
        rw [heq]
        simp only [inv_pow]
        rw [show ((2 : ℕ) ^ (3 * n) : ℝ≥0∞) = ENNReal.ofReal (((2 : ℝ) ^ n) ^ 3) by simp only [Nat.cast_ofNat]; rw [mul_comm 3 n, pow_mul]; simp]
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply congrArg ENNReal.ofReal
        generalize ht : (2 : ℝ) ^ n = t at *
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        all_goals
          calc
            t ^ 3 * (D * t⁻¹ ^ 4) = D * (t * t⁻¹) ^ 3 * t⁻¹ := by ring
            _ = D * t⁻¹ ^ 1 := by rw [mul_inv_cancel₀ (ne_of_gt htwo)]; simp
      simpa only [G, ite_eq_left hn, compl_compl] using
        hsum.trans (le_trans (by gcongr) (le_of_eq hpow))
    · simp [G, hn]
  calc
    P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N a b (1 / 32) (phase ω)} ≤
        P {ω | ∀ n : ℕ, N ≤ n → ω ∈ G n}ᶜ := by
      apply measure_mono
      intro ω hbad hgood
      apply hbad
      intro n hn z hz hlat
      have hn9 : 9 ≤ n := hN₀.trans (hN.trans hn)
      have hnot : ω ∉ E n (phase ω n) := by
        have hg := hgood n hn
        simp only [G, ite_eq_left hn9, mem_compl_iff, mem_iUnion] at hg
        exact fun he => hg ⟨phase ω n, hphase ω n, he⟩
      exact Classical.not_not.mp hnot z hz hlat
    _ ≤ δ := htail N hN Ω P G hG


/-- The growing-range estimate also holds for separated singular LQG
annuli, by the pathwise Weyl-weight comparison. -/
theorem exists_universal_singular_growing_phaseCriterion_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc →
    ∀ (s : ℝ), 0 < s → ∀ x : ℂ,
      s / 100 ≤ infDist (0 : ℂ) (annulus x (s / 4) (2 * s)) →
    ∀ (F : ℕ → Finset ℂ), (∀ n, (F n).card ≤ 2 ^ (3 * n)) →
    ∀ (phase : Ω → ℕ → ℂ), (∀ ω n, phase ω n ∈ F n) →
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N
        (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) (phase ω)} ≤ δ := by
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_universal_growing_phaseCriterion_probability hgrowth hγ hγ₂ h₀ hμ₀ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hE0 s hs x hd F hcard phase hphase
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hE0 hgff hγ hγ₂ hQ
  have hW := lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, hW hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  calc
    _ ≤ P {ω | ¬ PhaseVeryGoodCriterionThree (ν ω) s x N a b (1 / 32) (phase ω)} := by
      apply measure_mono_ae
      filter_upwards [hweight] with ω hω hbad
      intro hgood
      exact hbad (phaseVeryGoodCriterionThree_of_singular_weight hs hd (hN₀.trans hN) hω hgood)
    _ ≤ δ := hbound N hN Ω P hC hcirc ν hgff hν s hs x F hcard phase hphase

end HarmonicBalls.Section6
