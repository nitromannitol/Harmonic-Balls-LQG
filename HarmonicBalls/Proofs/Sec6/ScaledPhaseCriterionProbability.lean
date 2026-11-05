import HarmonicBalls.Proofs.Sec6.ScaledPhaseCriterionGrid
import HarmonicBalls.Proofs.Sec6.ScaledSubrangeGridProbability

/-! # One-scale third-criterion estimate

The good-annulus count estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- A uniform polynomial bound for failure of the third criterion at one
specified dyadic mesh, at every positive radius deterministic centre, and prescribed lattice phase. -/
theorem exists_scaled_phase_criterionThree_one_scale_failure_bound
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ D r₀ : ℝ, 0 < D ∧ 0 < r₀ ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ (s : ℝ), 0 < s → ∀ (x phase : ℂ) (n : ℕ), 9 ≤ n → dyadicScale n < r₀ →
      P {ω | ¬ ∀ z ∈ annulus x (s / 2) s,
        z - phase ∈ scaledLattice (dyadicScale n * s / 100) →
        (1 / 32 : ℝ) * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)} ≤
        ENNReal.ofReal (D * (dyadicScale n) ^ (4 : ℝ)) := by
  obtain ⟨a, ha, D, r₀, hD, hr₀, hgrid⟩ :=
    exists_scaled_subrange_grid_failure_bound hgrowth hγ hγ₂ h₀ hμ₀ hb
  refine ⟨a, ha, D, r₀, hD, hr₀, ?_⟩
  intro Ω _ P hCfield hcirc μ hgff hμ s hs x phase n hn hsmall
  obtain ⟨y, hy⟩ := scaled_phase_annulus_lattice_subset_prevalenceGrid hs hn x phase
  calc
    _ ≤ P {ω | ∃ z ∈ prevalenceGrid (dyadicScale n),
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ ω) (s * r) (s • (z + y)) a b}.ncard : ℝ) <
              (1 / 32 : ℝ) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ))} := by
      apply measure_mono
      intro ω hbad
      by_contra hnot
      apply hbad
      intro z hz hlat
      apply scaled_criterionThree_count_of_subrange (by norm_num) hs hn
      apply le_of_not_gt
      intro hlt
      apply hnot
      refine ⟨s⁻¹ • z - y, hy z hz hlat, ?_⟩
      simpa only [sub_add_cancel, smul_smul, mul_inv_cancel₀ hs.ne', one_smul] using hlt
    _ ≤ ENNReal.ofReal (D * (dyadicScale n) ^ (4 : ℝ)) :=
      hgrid Ω P hCfield hcirc μ hgff hμ s hs y (dyadicScale n) (dyadicScale_pos n) hsmall

end HarmonicBalls.Section6
