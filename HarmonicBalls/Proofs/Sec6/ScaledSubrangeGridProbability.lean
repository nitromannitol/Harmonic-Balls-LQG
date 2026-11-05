import HarmonicBalls.Proofs.Sec6.ScaledGoodAnnulusProbability
import HarmonicBalls.Proofs.Sec6.PrevalenceGridUnion

/-! # Grid union bound for scaled good-annulus counts

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- The lower-tail estimate holds uniformly for all positive physical scales
and all deterministic translations of the prevalence grid. -/
theorem exists_scaled_subrange_grid_failure_bound
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
    ∀ (s : ℝ), 0 < s → ∀ (y : ℂ) (ε : ℝ), 0 < ε → ε < r₀ →
      P {ω | ∃ z ∈ prevalenceGrid ε,
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ ω) (s * r) (s • (z + y)) a b}.ncard : ℝ) <
              (1 / 32 : ℝ) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
        ENNReal.ofReal (D * ε ^ (4 : ℝ)) := by
  obtain ⟨a, ha, C, hC, htail⟩ :=
    exists_scaled_goodAnnulus_count_tail_of_volumeGrowth hgrowth hγ hγ₂ h₀ hμ₀ hb
  obtain ⟨r₀, hr₀, hr⟩ := exists_radius_logb_inverse_ge (b := 7) (D := 16) (by norm_num)
  refine ⟨a, ha, 403 ^ 2 * C, min r₀ 1, by positivity, lt_min hr₀ zero_lt_one, ?_⟩
  intro Ω _ P hCfield hcirc μ hgff hμ s hs y ε hε hsmall
  have hεr₀ : ε < r₀ := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hε1 : ε ≤ 1 := (lt_of_lt_of_le hsmall (min_le_right _ _)).le
  calc
    _ ≤ ENNReal.ofReal ((403 / ε) ^ 2) * ENNReal.ofReal (C * ε ^ (6 : ℝ)) :=
      measure_exists_mem_prevalenceGrid_le P hε hε1 _ _
        (fun z _ => htail Ω P hCfield hcirc μ hgff hμ s hs (s • (z + y)) ε hε (hr ε hε hεr₀))
    _ = ENNReal.ofReal ((403 / ε) ^ 2 * (C * ε ^ (6 : ℝ))) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (403 / ε) ^ 2)]
    _ = ENNReal.ofReal (403 ^ 2 * C * ε ^ (4 : ℝ)) := by
      congr 1
      have he : (4 : ℝ) = 6 - 2 := by norm_num
      rw [he, Real.rpow_sub hε, Real.rpow_two]
      field_simp

end HarmonicBalls.Section6
