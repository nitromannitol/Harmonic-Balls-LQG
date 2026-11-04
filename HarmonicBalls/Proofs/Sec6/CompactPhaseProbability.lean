import HarmonicBalls.Proofs.Sec6.SevenAdicProbabilityReduction

/-! # Good-annulus probability on dyadic phases

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`, with the GFF law bridge
in `LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter MarkovProcess
open scoped ENNReal

universe u

/-- A radius in `(0,1]` is a dyadic multiple of a phase in `(1/2,1]`. -/
theorem exists_dyadic_phase {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ (s : ℝ) (n : ℕ), s ∈ Ioc (1 / 2 : ℝ) 1 ∧ r = s * dyadicScale n := by
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  let d := dyadicScale n
  have hd : 0 < d := dyadicScale_pos n
  have hnhi' : r ≤ d := by simpa [d, dyadicScale] using hnhi
  have hnlo' : (1 / 2 : ℝ) * d < r := by
    simpa [d, dyadicScale, pow_succ, mul_comm] using hnlo
  refine ⟨r / d, n, ⟨?_, ?_⟩, ?_⟩
  · exact (lt_div_iff₀ hd).2 hnlo'
  · exact (div_le_one hd).2 hnhi'
  · dsimp [d]
    exact (div_mul_cancel₀ r (dyadicScale_pos n).ne').symm

/-- For the good-annulus event, the probability at any radius at most one
coincides with its probability at a dyadic phase in `(1/2,1]`. -/
theorem exists_dyadic_phase_goodAnnulus_probability
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {r a : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 < a) (b : ℝ) :
    ∃ s ∈ Ioc (1 / 2 : ℝ) 1,
      P {ω | ¬ IsGoodAnnulus (μ ω) r 0 a b} =
        P {ω | ¬ IsGoodAnnulus (μ ω) s 0 a b} := by
  obtain ⟨s, n, hs, rfl⟩ := exists_dyadic_phase hr hr1
  refine ⟨s, hs, ?_⟩
  exact badGoodAnnulus_probability_eq_dyadic_orbit hγ h hμ
    (by linarith [hs.1]) n ha b

/-- A threshold uniform over dyadic phases implies seven-adic good-annulus
prevalence. The phase probability bound is an explicit proof hypothesis. -/
theorem goodAnnuliSubRangeStep_of_dyadic_phase_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hphase : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ p ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω]
        (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
        IsLQGMeasureOfField P γ 0 hcirc μ →
        ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Ioc (1 / 2 : ℝ) 1,
          P {ω | ¬ IsGoodAnnulus (μ ω) s 0 a b} ≤ ENNReal.ofReal (1 - p)) :
    GoodAnnuliSubRangeStep.{u} := by
  apply goodAnnuliSubRangeStep_of_sevenAdic_reference_probability hgrowth
  intro γ hγ hγ2 b hb p hp Ω _ P hC hcirc μ hgff hμ
  obtain ⟨a, ha, hbound⟩ := hphase γ hγ hγ2 b hb p hp Ω P hC hcirc μ hgff hμ
  refine ⟨a, ha, ?_⟩
  intro n
  have hr : 0 < (7 : ℝ)⁻¹ ^ n := pow_pos (by norm_num) n
  have hr1 : (7 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨s, hs, heq⟩ := exists_dyadic_phase_goodAnnulus_probability hγ hgff hμ
    hr hr1 ha.1 b
  rw [heq]
  exact hbound s hs

end HarmonicBalls.Section6
